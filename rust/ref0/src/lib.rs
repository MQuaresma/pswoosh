mod arithmetic;
pub mod util;

use std::arch::asm;
use crate::arithmetic::{fq::*, poly::*, polyvec::*};
use getrandom;

const SYMBYTES: usize = 32;
const NOISE_BYTES: usize = (N*D*2)/8;

/*
 * TODO:
 * - replaced hardcoded values with expressions
 * - write unit tests
 * x Make rej_sampling constant time
 * x Implement gen_matrix
 * - Replace dummy code in XOF functions with call to library (RustCrypto ??)
 *   - Do we want to domain separate
 * - Fix cmp in fq.rs
 * - Implement fqmul
 * - Implement full modular reduction
 * x Implement getnoise
 * x Compute BARR constant for barret reduction
 * - Implement polyvec_ntt
 * - Replace constants in fq with macros (??)
 */

/*
 * Key generation wrapper
 */
pub fn keygen(seed: [u8; SYMBYTES]) {
    kg(seed);
}

/*
 * Generate secret and error vectors and compute public key
 */
fn kg(seed: [u8; SYMBYTES]) {
    let mut nonce: u8 = 0;
    let mut noiseseed: [u8; SYMBYTES] = [0; SYMBYTES];
    let a: [PolyVec; N] = genmatrix(&seed);

    getrandom::getrandom(&mut noiseseed).expect("getrandom failed");

    let mut s: PolyVec = getnoise(&noiseseed, nonce);

    nonce += 1;
    let mut e: PolyVec = getnoise(&noiseseed, nonce);
    
    let pk: PolyVec = gen_pkl(&a, &mut s, &mut e);
}


/*
 * Key derivation wrapper to deserialize the vectors of polynomials
 */
pub fn skey_deriv(pkp: [u8; POLYVEC_BYTES], skp: [u8; 2*POLYVEC_BYTES], seed: [u8; SYMBYTES]) {
    let pk: PolyVec = polyvec_frombytes(&pkp);
    let s: PolyVec = polyvec_frombytes(skp[..POLY_BYTES].try_into().unwrap());
    let e: PolyVec = polyvec_frombytes(skp[POLY_BYTES..].try_into().unwrap());

    sdk(pk, (s,e), seed);
}

/*
 * Shared key derivation
 * FIXME
 */
fn sdk(pk: PolyVec, sk: (PolyVec, PolyVec), seed: [u8; 32]) {
    let mut s: PolyVec = sk.0;
    let mut e: PolyVec = sk.1;
    let a: [PolyVec; N] = genmatrix(&seed);

    let pk2: PolyVec = gen_pkl(&a, &mut s, &mut e);
    let mut r_in: [u8; POLYVEC_BYTES * 2] = [0; POLYVEC_BYTES * 2];

    r_in[0..POLYVEC_BYTES].copy_from_slice(&polyvec_tobytes(pk));
    r_in[POLYVEC_BYTES..POLYVEC_BYTES*2].copy_from_slice(&polyvec_tobytes(pk2));

    let r = gen_randoffset(&r_in);   // r = H(pk, pk2);

    let mut k: Poly = polyvec_basemul_acc(pk, s);
    k = poly_add(k, r);
    rec(&mut k);
}

/*
 * Reconciliation
 */
fn rec(k: &mut Poly) {
    for i in 0..D {
        k[i] = round(k[i]);
    }
}

/*
 * Generates a public key from matrix A, secret and error vector: sT * A + eT
 */
fn gen_pkl(a: &[PolyVec; N], s: &mut PolyVec, e: &mut PolyVec) -> PolyVec {
    let mut tmp: PolyVec = polyvec_init();

    polyvec_ntt(s);
    polyvec_ntt(e);

    // tmp = sT * A
    for i in 0..N {
        tmp[i] = polyvec_basemul_acc(*s, a[i]);
    }

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
    polyvec_ntt(e);

    // tmp = A * s
    for i in 0..N {
        tmp[i] = polyvec_basemul_acc(a[i], *s);
    }

    // pk = (A * s) + e
    let pk: PolyVec = polyvec_add(tmp, *e);

    pk
}

/*
 * Converts element in Zq to a bit
 */
fn round(c: Elem) -> Elem {
    let mut c1: u8;
    let mut c2: u8;
    let mut r: Elem = fp_init();

    c1 = cmp(c, QQ);
    c2 = cmp(c, TQQ);

    c1 = (c1 >> 7) ^ 0x1;               // (c1 >> 7) = 1 iff c1 < 0 i.e. c < QQ
    c2 = ((c2 as i8 - 1) as u8) >> 7;   // (c2 - 1) < 0 iff c2 <= 0

    r[0] = (c1 & c2) as u64;

    r
}


const RATE: usize = 136;
/*
 * Placeholder for XOF function (need to check licensing)
 */
fn xof_squeeze(out: &mut [u8], len: usize) {
}


/*
 * Placeholder for XOF function (need to check licensing)
 */
fn xof_absorb(inp: &[u8], len: usize) {
}


/* Description: generates coefficients in Zq from a (uniformly random) stream of bytes
 *
 * Result: number of coefficients generated
 */
fn rej_sampling(buf: &[u8; RATE], p: &mut Poly, mut offset: usize) -> usize {
    let mut c: usize = 0;
    let mut t: u8;
    let mut t_elem: Elem;

    while(c < RATE-ELEM_BYTES && offset < D) {
        t_elem = elem_frombytes(buf[c..c+ELEM_BYTES].try_into().unwrap());
        t = cmp(t_elem, Q);
        t = (t as i8 >> 7) as u8; //t = 0xff if t < 0
        p[offset] = t_elem;
        offset += (1u8 & t) as usize;  //only increment if cmp(tElem, Q) < 0 i.e. accept
        c += ELEM_BYTES
    }

    offset
}


fn gen_randoffset(inp: &[u8; POLYVEC_BYTES * 2]) -> Poly {
    let mut buf: [u8; RATE] = [0; RATE];
    let mut r: Poly = poly_init();
    let mut ctr: usize = 0;

    xof_absorb(inp, POLYVEC_BYTES * 2);

    while (ctr < D) {
        xof_squeeze(&mut buf, RATE);
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
                    asm!("popcnt {m}, {m}", // if t=0b11 then m=2 if else m=1
                         m = inout(reg) m,
                    );
                }
                m = ((m << 61) as i64 >> 63) as u64;

                p[i][4*j + k] = Q.clone();

                for l in 0..NLIMBS {
                    p[i][4*j + k][l] &= m;  //p[i][4*j + k] = Q iff t = 0b11
                }

                /* Note:
                 * (Q-1) = -1 mod Q
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

    inp[..SYMBYTES].copy_from_slice(seed);
    inp[SYMBYTES] = nonce;
    xof_absorb(&inp, SYMBYTES + 1);

    xof_squeeze(&mut buf, NOISE_BYTES);

    cbd(&buf, &mut p);

    p
}


fn genmatrix(seed: &[u8; SYMBYTES]) -> [PolyVec; N] {
    let mut buf: [u8; RATE] = [0; RATE];
    let mut a: [PolyVec; N] = [polyvec_init(); N];
    let mut ctr: usize;

    xof_absorb(seed, SYMBYTES + 1);

    for i in 0..N {
        for j in 0..N {
            ctr = 0;

            while (ctr < D) {
                xof_squeeze(&mut buf, RATE);
                ctr = rej_sampling(&buf, &mut a[i][j], ctr);
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

    #[test]
    fn speed_nike() {
        let mut seed: [u8; SYMBYTES] = [0; SYMBYTES];
        let mut t: [u64; NRUNS] = [0; NRUNS];
        getrandom::getrandom(&mut seed).expect("getrandom failed");

        for i in 0..NRUNS {
            t[i] = cpucycles();
            keygen(seed);
        }
        println!("keygen: ");
        print_res(&mut t);

        for i in 0..NRUNS {
            t[i] = cpucycles();
            keygen(seed);
        }
        println!("skey_deriv: ");
        print_res(&mut t);

        for i in 0..NRUNS {
            t[i] = cpucycles();
            keygen(seed);
        }
        println!("skey_deriv: ");
        print_res(&mut t);
    }

    #[test]
    fn speed_full() {
        let mut seed: [u8; SYMBYTES] = [0; SYMBYTES];
        let mut t: [u64; NRUNS] = [0; NRUNS];
        let mut a: [PolyVec; N] = [polyvec_init(); N];
        let mut s: PolyVec = polyvec_init();

        getrandom::getrandom(&mut seed).expect("getrandom failed");

        for i in 0..NRUNS {
            t[i] = cpucycles();
            a = genmatrix(&seed);
        }
        println!("genmatrix: ");
        print_res(&mut t);

        for i in 0..NRUNS {
            t[i] = cpucycles();
            s = getnoise(&mut seed, 0);
        }
        println!("getnoise: ");
        print_res(&mut t);

        for i in 0..NRUNS {
            t[i] = cpucycles();
            poly_ntt(&mut s[i]);
        }
        println!("poly_ntt:");
        print_res(&mut t);

        for i in 0..NRUNS {
            t[i] = cpucycles();
            poly_invntt(&mut s[i]);
        }
        println!("poly_invntt:");
        print_res(&mut t);

        for i in 0..NRUNS {
            t[i] = cpucycles();
            s[0] = polyvec_basemul_acc(a[0], a[1]);
        }
        println!("polyvec_basemul_acc: ");
        print_res(&mut t);

        for i in 0..NRUNS {
            t[i] = cpucycles();
            keygen(seed);
        }
        println!("keygen: ");
        print_res(&mut t);

        for i in 0..NRUNS {
            t[i] = cpucycles();
            keygen(seed);
        }
        println!("skey_deriv: ");
        print_res(&mut t);

        for i in 0..NRUNS {
            t[i] = cpucycles();
            keygen(seed);
        }
        println!("skey_deriv: ");
        print_res(&mut t);

    }
}
