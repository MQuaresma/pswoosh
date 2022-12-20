mod arithmetic;
pub mod util;

use std::arch::asm;
use crate::arithmetic::{fq::*, poly::*, polyvec::*, params::*};
use getrandom;
use sha3::{Shake128, CShake128, digest::{Update, ExtendableOutput, XofReader}};

const SYMBYTES: usize = 32;
const NOISE_BYTES: usize = (N*D*2)/8;
const PUBLICKEY_BYTES: usize = POLYVEC_BYTES;
const SECRETKEY_BYTES: usize = POLYVEC_BYTES;
const RATE: usize = 136;

/*
 * TODO:
 * x replaced hardcoded values with expressions
 * x Make rej_sampling constant time
 * x Implement gen_matrix
 * x Replace dummy code in XOF functions with call to library (RustCrypto)
 * x Fix cmp in fq.rs
 * x Implement getnoise
 * x Compute BARR constant for barret reduction
 * x Implement polyvec_ntt
 * - Integrate NIZK
 * - Implement schoolbook multiplication for testing
 * - Domain separation for XOF functions
 * - Pre-compute in Montgomery domain for fp_mul
 */

/*
 * Key generation wrapper
 */
pub fn keygen(seed: [u8; SYMBYTES], f:bool) -> ([u8; SECRETKEY_BYTES], [u8; PUBLICKEY_BYTES]) {
    kg(seed, f)
}


/*
 * Generate secret and error vectors and compute public key
 */
fn kg(seed: [u8; SYMBYTES], f: bool) -> ([u8; SECRETKEY_BYTES], [u8; PUBLICKEY_BYTES]) {
    let mut nonce: u8 = 0;
    let mut noiseseed: [u8; SYMBYTES] = [0; SYMBYTES];
    let skv: [u8; SECRETKEY_BYTES];
    let pkv: [u8; PUBLICKEY_BYTES];

    getrandom::getrandom(&mut noiseseed).expect("getrandom failed");

    let a: [PolyVec; N] = genmatrix(&seed, f);

    let mut s: PolyVec = getnoise(&noiseseed, nonce);
    nonce += 1;
    let mut e: PolyVec = getnoise(&noiseseed, nonce);

    let pk: PolyVec =
        if f {
            gen_pkl(&a, &mut s, &mut e)
        } else {
            gen_pkr(&a, &mut s, &mut e)
        };

    skv = polyvec_tobytes(s);
    pkv = polyvec_tobytes(pk);

    (skv, pkv)
}


/*
 * Key derivation wrapper to deserialize the vectors of polynomials
 */
pub fn skey_deriv(pkp1: [u8; PUBLICKEY_BYTES], pkp2: [u8; PUBLICKEY_BYTES], skp: [u8; SECRETKEY_BYTES], f: bool) -> [u8; SYMBYTES] {
    let mut pk: PolyVec = polyvec_frombytes(&pkp2);
    let mut s: PolyVec = polyvec_frombytes(&skp);
    let mut rin: [u8; POLYVEC_BYTES * 2] = [0; POLYVEC_BYTES * 2];

    if !f {
        rin[0..POLYVEC_BYTES].copy_from_slice(&pkp1);
        rin[POLYVEC_BYTES..POLYVEC_BYTES*2].copy_from_slice(&pkp2);
    } else {
        rin[0..POLYVEC_BYTES].copy_from_slice(&pkp2);
        rin[POLYVEC_BYTES..POLYVEC_BYTES*2].copy_from_slice(&pkp1);
    }

    let r = genoffset(&rin);

    sdk(&mut pk, &mut s, r, f)
}

/*
 * Shared key derivation
 */
fn sdk(pk: &mut PolyVec, s: &mut PolyVec, r: Poly, f: bool) -> [u8; SYMBYTES] {
    let mut kv: Poly;
    let mut k: [u8; SYMBYTES] = [0; SYMBYTES];

    polyvec_ntt(pk);
    polyvec_ntt(s);

    if !f {
        // pk * s
        kv = polyvec_basemul_acc(*pk, *s)
    } else {
        // s^T * pk
        kv = polyvec_basemul_acc(*s, *pk)
    }

    poly_invntt(&mut kv);

    kv = poly_add(kv, r);

    rec(&kv, &mut k);

    k
}

/*
 * Reconciliation
 */
fn rec(kv: &Poly, k: &mut [u8; SYMBYTES]) {
    for i in 0..D/8 {
        k[i] = 0;
        for j in 0..8 {
            k[i] |= (round(kv[8*i + j]) << j);
        }
    }
}

/*
 * Generates a public key from matrix A, secret and error vector
 */
fn gen_pk(a: &[PolyVec; N], s: &mut PolyVec, e: &mut PolyVec) -> PolyVec {
    let mut tmp: PolyVec = polyvec_init();

    polyvec_ntt(s);

    for i in 0..N {
        tmp[i] = polyvec_basemul_acc(a[i], *s);
    }

    polyvec_invntt(&mut tmp);
    polyvec_invntt(s);

    let pk: PolyVec = polyvec_add(tmp, *e);

    pk
}

/*
 * Generates a public key from matrix A, secret and error vector: sT * A + eT
 */
fn gen_pkl(a: &[PolyVec; N], s: &mut PolyVec, e: &mut PolyVec) -> PolyVec {
    let mut tmp: PolyVec = polyvec_init();

    polyvec_ntt(s);

    // tmp = sT * A
    for i in 0..N {
        tmp[i] = polyvec_basemul_acc(*s, a[i]);
    }

    polyvec_invntt(&mut tmp);
    polyvec_invntt(s);

    // pk = (sT * A) + eT
    let pk: PolyVec = polyvec_add(tmp, *e);

    pk
}

/*
 * Generates a public key from matrix A, secret and error vector: A * s + e
 */
fn gen_pkr(a: &[PolyVec; N], s: &mut PolyVec, e: &mut PolyVec) -> PolyVec {
    let mut tmp: PolyVec = polyvec_init();

    polyvec_ntt(s);

    // tmp = A * s
    for i in 0..N {
        tmp[i] = polyvec_basemul_acc(a[i], *s);
    }

    polyvec_invntt(&mut tmp);
    polyvec_invntt(s);

    // pk = (A * s) + e
    let pk: PolyVec = polyvec_add(tmp, *e);

    pk
}

/*
 * Converts element in Zq to a bit
 */
fn round(c: Elem) -> u8 {
    let mut l: u8;
    let mut h: u8;
    let r: u8;

    l = cmp(c, QQ);  //l = 0x80 if c < Q/4
    h = cmp(c, TQQ); //h = 0x01 if 3Q/4 < c

    l = (l >> 7) ^ 0x01;
    h = (h & 0x01) ^ 0x01;

    r = (l & h) as u8;

    r
}


/* Generates coefficients in Zq from a (uniformly random) stream of bytes
 *
 * Returns: number of coefficients generated
 */
fn rej_sampling(buf: &[u8; RATE], p: &mut Poly, mut offset: usize) -> usize {
    let mut c: usize = 0;
    let mut t: u8;
    let mut t_elem: Elem;

    while(c < RATE-ELEM_BYTES && offset < D) {
        t_elem = elem_frombytes(buf[c..c+ELEM_BYTES].try_into().unwrap());
        t = cmp(t_elem, Q);
        t = t >> 7; //t = 0x80 if t_elem < Q
        p[offset] = t_elem;
        offset += t as usize;  //only increment if cmp(tElem, Q) < 0 i.e. accept
        c += ELEM_BYTES
    }

    offset
}


fn genoffset(inp: &[u8; POLYVEC_BYTES * 2]) -> Poly {
    let mut buf: [u8; RATE] = [0; RATE];
    let mut r: Poly = poly_init();
    let mut ctr: usize = 0;
    let mut xof = Shake128::default();
    let mut rxof;

    xof.update(inp);
    rxof = xof.finalize_xof();

    while (ctr < D) {
        rxof.read(&mut buf);  //squeeze RATE bytes from state
        ctr = rej_sampling(&buf, &mut r, ctr);
    }

    r
}

/*
 * Samples ternary noise from a centered binomial distribution with:
 * - 25%: -1 (11)
 * - 50%: 0  (00, 10)
 * - 25%: 1  (01)
 */
fn cbd(buf: &[u8; NOISE_BYTES], p: &mut PolyVec) {
    let mut c: u8;
    let mut t: u8;
    let mut m: u64;

    for i in 0..N {
        for j in 0..D/4 { //CHECK ME
            c = buf[i*D/4+j];
            for k in 0..4 {
                t = c & 0x3;
                m = t as u64;

                unsafe {
                    asm!("popcnt {m}, {m}", // if t=0b11 then m=2 if t=0b00 then m=0 else m=1
                         m = inout(reg) m,
                    );
                }
                m = ((m << 62) as i64 >> 63) as u64;

                p[i][4*j + k] = Q.clone();

                for l in 0..NLIMBS {
                    p[i][4*j + k][l] &= m;  //p[i][4*j + k] = Q iff t = 0b11
                }

                /* Note:
                 * -1 = (Q-1) mod Q
                 * Q's last bit is always set, so setting last bit to 0 is equivalent
                 * to subtracting one
                 */
                m = (t & 0x1) as u64;
                p[i][4*j + k][0] ^= m;

                c >>= 2;
            }
        }
    }
}

fn getnoise(seed: &[u8; SYMBYTES], nonce: u8) -> PolyVec {
    let mut inp: [u8; SYMBYTES + 1] = [0; SYMBYTES + 1];
    let mut buf: [u8; NOISE_BYTES] = [0; NOISE_BYTES];
    let mut p: PolyVec = polyvec_init();
    let mut xof = Shake128::default();
    let mut rxof;

    inp[..SYMBYTES].copy_from_slice(seed);
    inp[SYMBYTES] = nonce;

    xof.update(&inp);
    rxof = xof.finalize_xof();

    rxof.read(&mut buf);

    cbd(&buf, &mut p);

    p
}

/*
 * Transpose matrix (testing purposes only)
 */
fn transpose(a: &[PolyVec;N], at: &mut [PolyVec; N]) {
    for i in 0..N {
        for j in 0..N {
            at[i][j] = a[j][i];
        }
    }
}

/*
 * Generates matrix A from a seed
 * - t => generate A^T
 */
fn genmatrix(seed: &[u8; SYMBYTES], t: bool) -> [PolyVec; N] {
    let mut buf: [u8; RATE] = [0; RATE];
    let mut a: [PolyVec; N] = [polyvec_init(); N];
    let mut ctr: usize;
    let mut xof = Shake128::default();
    let mut rxof;

    xof.update(seed);
    rxof = xof.finalize_xof();

    if !t {
        for i in 0..N {
            for j in 0..N {
                ctr = 0;

                while (ctr < D) {
                    rxof.read(&mut buf);  //squeeze RATE bytes from state
                    ctr = rej_sampling(&buf, &mut a[i][j], ctr);
                }
            }
        }
    } else {
        for i in 0..N {
            for j in 0..N {
                ctr = 0;

                while (ctr < D) {
                    rxof.read(&mut buf);  //squeeze RATE bytes from state
                    ctr = rej_sampling(&buf, &mut a[j][i], ctr);
                }
            }
        }
    }

    a
}


#[cfg(test)]
mod tests {
    use super::*;
    use getrandom;
    use crate::util::*;
    use std::time::*;

    #[test]
    fn test_scheme() {
        let mut seed: [u8; SYMBYTES] = [0; SYMBYTES];
        let mut pk1: [u8; PUBLICKEY_BYTES] = [0; PUBLICKEY_BYTES];
        let mut sk1: [u8; SECRETKEY_BYTES] = [0; SECRETKEY_BYTES];
        let mut pk2: [u8; PUBLICKEY_BYTES] = [0; PUBLICKEY_BYTES];
        let mut sk2: [u8; SECRETKEY_BYTES] = [0; SECRETKEY_BYTES];
        let mut ss1: [u8; SYMBYTES] = [0; SYMBYTES];
        let mut ss2: [u8; SYMBYTES] = [0; SYMBYTES];

        getrandom::getrandom(&mut seed).expect("getrandom failed");

        (sk1, pk1) = kg(seed, true);
        (sk2, pk2) = kg(seed, false);

        ss1 = skey_deriv(pk1, pk2, sk1, true);
        ss2 = skey_deriv(pk2, pk1, sk2, false);

        assert_eq!(ss1, ss2, "ERROR: shared secrets don't match!");
    }

    #[test]
    fn test_genmatrix() {
        let mut seed: [u8; SYMBYTES] = [0; SYMBYTES];
        let mut a0: [PolyVec; N] = [polyvec_init(); N];
        let mut a1: [PolyVec; N] = [polyvec_init(); N];
        let mut at: [PolyVec; N] = [polyvec_init(); N];
        let mut lt: bool = true;

        getrandom::getrandom(&mut seed).expect("getrandom failed");

        a0 = genmatrix(&seed, false);
        a1 = genmatrix(&seed, true);

        transpose(&a1, &mut at);

        assert!(a0 == at, "Matrices do not match");

        for i in 0..N {
            for j in 0..N {
                for k in 0..D {
                    lt &= (cmp(a0[i][j][k], Q) == 0x80);
                }
            }
        }

        assert!(lt, "Elements out of range");
    }

    #[test]
    fn test_genoffset() {
        let mut seed: [u8; POLYVEC_BYTES*2] = [0; POLYVEC_BYTES*2];
        let mut s: Poly = poly_init();
        let mut lt: bool = true;

        getrandom::getrandom(&mut seed).expect("getrandom failed");
        s = genoffset(&seed);

        for i in 0..D {
            lt &= (cmp(s[i], Q) == 0x80);
        }

        assert!(lt, "Elements out of range");
    }


    #[test]
    fn test_getnoise() {
        let mut seed: [u8; SYMBYTES] = [0; SYMBYTES];
        let mut s: PolyVec = polyvec_init();
        let mut sml: bool = true;
        let mut t0: bool = true;
        let mut t1: bool = true;
        let mut tn1: bool = true;
        let e0: Elem = fp_init();
        let e1: Elem = [0x01, 0x0, 0x0, 0x0];
        let mut qm1: Elem = fp_init();
        sub(&mut qm1, e0, e1);

        getrandom::getrandom(&mut seed).expect("getrandom failed");

        s = getnoise(&seed, 0);

        for i in 0..N {
            for j in 0..D {
                t0 = cmp(s[i][j], e0) == 0x00;
                t1 = cmp(s[i][j], e1) == 0x00;
                tn1 = cmp(s[i][j], qm1) == 0x00;
                sml &= (t0 | t1 | tn1);
            }
        }

        assert!(sml, "Elements out of range");
    }

    #[test]
    fn test_rec() {
        let s0: Poly = [TQQ.clone(); D];
        let s1: Poly = [HQ.clone(); D];
        let s2: Poly = [QQ.clone(); D];
        let s3: Poly = [fp_init(); D];
        let b0: [u8; SYMBYTES] = [0x00; SYMBYTES];
        let b1: [u8; SYMBYTES] = [0xff; SYMBYTES];
        let mut rb: [u8; SYMBYTES] = [0; SYMBYTES];

        rec(&s3, &mut rb);
        assert_eq!(rb, b0);

        rec(&s2, &mut rb);
        assert_eq!(rb, b1);

        rec(&s1, &mut rb);
        assert_eq!(rb, b1);

        rec(&s0, &mut rb);
        assert_eq!(rb, b1);
    }


    #[test]
    fn test_round() {
        let s0: Elem = TQQ.clone();
        let s1: Elem = HQ.clone();
        let s2: Elem = QQ.clone();
        let s3: Elem = fp_init();
        let b0: u8 = 0x00;
        let b1: u8 = 0x01;
        let mut rb: u8 = 0;

        rb = round(s3);
        assert_eq!(rb, b0);

        rb = round(s2);
        assert_eq!(rb, b1);

        rb = round(s1);
        assert_eq!(rb, b1);

        rb = round(s0);
        assert_eq!(rb, b1);
    }

    #[test]
    fn speed_nike() {
        let mut seed: [u8; SYMBYTES] = [0; SYMBYTES];
        let mut pkp: [u8; PUBLICKEY_BYTES] = [0; PUBLICKEY_BYTES];
        let mut skp: [u8; SECRETKEY_BYTES] = [0; SECRETKEY_BYTES];
        let mut ss: [u8; SYMBYTES] = [0; SYMBYTES];
        let mut t: [u64; NRUNS] = [0; NRUNS];

        getrandom::getrandom(&mut seed).expect("getrandom failed");

        for i in 0..NRUNS {
            t[i] = rdtsc();
            (skp, pkp) = kg(seed, true);
        }
        println!("keygen (cycles): ");
        print_res(&mut t);

        for i in 0..NRUNS {
            t[i] = rdtsc();
            ss = skey_deriv(pkp, pkp, skp, true);
        }
        println!("skey_deriv (cycles): ");
        print_res(&mut t);
    }

    #[test]
    fn speed_full() {
        let mut seed: [u8; SYMBYTES] = [0; SYMBYTES];
        let mut pkp: [u8; PUBLICKEY_BYTES] = [0; PUBLICKEY_BYTES];
        let mut skp: [u8; SECRETKEY_BYTES] = [0; SECRETKEY_BYTES];
        let mut rin: [u8; POLYVEC_BYTES * 2] = [0; POLYVEC_BYTES * 2];
        let mut ss: [u8; SYMBYTES] = [0; SYMBYTES];
        let mut t: [u64; NRUNS] = [0; NRUNS];
        let mut a: [PolyVec; N] = [polyvec_init(); N];
        let mut s: PolyVec = polyvec_init();

        getrandom::getrandom(&mut seed).expect("getrandom failed");

        for i in 0..NRUNS {
            t[i] = rdtsc();
            a = genmatrix(&seed, false);
        }
        println!("genmatrix (cycles): ");
        print_res(&mut t);

        for i in 0..NRUNS {
            t[i] = rdtsc();
            s = getnoise(&mut seed, 0);
        }
        println!("getnoise (cycles): ");
        print_res(&mut t);

        for i in 0..NRUNS {
            t[i] = rdtsc();
            s[i % N] = genoffset(&rin);
        }
        println!("genoffset (cycles): ");
        print_res(&mut t);

        for i in 0..NRUNS {
            t[i] = rdtsc();
            poly_ntt(&mut s[i % N]);
        }
        println!("poly_ntt (cycles):");
        print_res(&mut t);

        for i in 0..NRUNS {
            t[i] = rdtsc();
            poly_invntt(&mut s[i % N]);
        }
        println!("poly_invntt (cycles):");
        print_res(&mut t);

        for i in 0..NRUNS {
            t[i] = rdtsc();
            s[i % N] = polyvec_basemul_acc(a[i % N], a[(i + 1) % N]);
        }
        println!("polyvec_basemul_acc (cycles): ");
        print_res(&mut t);

        for i in 0..NRUNS {
            t[i] = rdtsc();
            (skp, pkp) = kg(seed, true);
        }
        println!("keygen (cycles): ");
        print_res(&mut t);

        for i in 0..NRUNS {
            t[i] = rdtsc();
            ss = skey_deriv(pkp, pkp, skp, true);
        }
        println!("skey_deriv (cycles): ");
        print_res(&mut t);
    }

    #[test]
    fn time_nike() {
        let mut seed: [u8; SYMBYTES] = [0; SYMBYTES];
        let mut pkp: [u8; PUBLICKEY_BYTES] = [0; PUBLICKEY_BYTES];
        let mut skp: [u8; SECRETKEY_BYTES] = [0; SECRETKEY_BYTES];
        let mut ss: [u8; SYMBYTES] = [0; SYMBYTES];
        let mut t: [u128; NRUNS] = [0; NRUNS];
        let mut start: Instant;

        getrandom::getrandom(&mut seed).expect("getrandom failed");

        start = Instant::now();
        for i in 0..NRUNS {
            t[i] = start.elapsed().as_nanos();
            (skp, pkp) = kg(seed, true);
        }
        println!("keygen (ns): ");
        print_res_u128(&mut t);

        start = Instant::now();
        for i in 0..NRUNS {
            t[i] = start.elapsed().as_nanos();
            ss = skey_deriv(pkp, pkp, skp, true);
        }
        println!("skey_deriv (ns): ");
        print_res_u128(&mut t);
    }

    #[test]
    fn time_full() {
        let mut seed: [u8; SYMBYTES] = [0; SYMBYTES];
        let mut pkp: [u8; PUBLICKEY_BYTES] = [0; PUBLICKEY_BYTES];
        let mut skp: [u8; SECRETKEY_BYTES] = [0; SECRETKEY_BYTES];
        let mut rin: [u8; POLYVEC_BYTES * 2] = [0; POLYVEC_BYTES * 2];
        let mut ss: [u8; SYMBYTES] = [0; SYMBYTES];
        let mut t: [u128; NRUNS] = [0; NRUNS];
        let mut a: [PolyVec; N] = [polyvec_init(); N];
        let mut s: PolyVec = polyvec_init();
        let mut start: Instant;

        getrandom::getrandom(&mut seed).expect("getrandom failed");

        start = Instant::now();
        for i in 0..NRUNS {
            t[i] = start.elapsed().as_nanos();
            a = genmatrix(&seed, false);
        }
        println!("genmatrix (ns): ");
        print_res_u128(&mut t);

        start = Instant::now();
        for i in 0..NRUNS {
            t[i] = start.elapsed().as_nanos();
            s = getnoise(&mut seed, 0);
        }
        println!("getnoise (ns): ");
        print_res_u128(&mut t);

        start = Instant::now();
        for i in 0..NRUNS {
            t[i] = start.elapsed().as_nanos();
            s[i % N] = genoffset(&rin);
        }
        println!("genoffset (ns): ");
        print_res_u128(&mut t);

        start = Instant::now();
        for i in 0..NRUNS {
            t[i] = start.elapsed().as_nanos();
            poly_ntt(&mut s[i % N]);
        }
        println!("poly_ntt (ns):");
        print_res_u128(&mut t);

        start = Instant::now();
        for i in 0..NRUNS {
            t[i] = start.elapsed().as_nanos();
            poly_invntt(&mut s[i % N]);
        }
        println!("poly_invntt (ns):");
        print_res_u128(&mut t);

        start = Instant::now();
        for i in 0..NRUNS {
            t[i] = start.elapsed().as_nanos();
            s[i % N] = polyvec_basemul_acc(a[i % N], a[(i + 1) % N]);
        }
        println!("polyvec_basemul_acc (ns): ");
        print_res_u128(&mut t);

        start = Instant::now();
        for i in 0..NRUNS {
            t[i] = start.elapsed().as_nanos();
            (skp, pkp) = kg(seed, true);
        }
        println!("keygen (ns): ");
        print_res_u128(&mut t);

        start = Instant::now();
        for i in 0..NRUNS {
            t[i] = start.elapsed().as_nanos();
            ss = skey_deriv(pkp, pkp, skp, true);
        }
        println!("skey_deriv (ns): ");
        print_res_u128(&mut t);
    }
}
