mod arithmetic;

use crate::arithmetic::fq::*;
use crate::arithmetic::poly::*;
use crate::arithmetic::polyvec::*;

const SYMBYTES: usize = 32;
const NOISE_BYTES: usize = (d*N*2)/8;

fn main() {
    let r: u8 = (0x80 as u8);
    println!("{:x}", r);
}


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
 * - Implement getnoise
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
    let a: [PolyVec; N] = genmatrix(&seed, nonce);

    nonce += 1;
    let mut s: PolyVec = getnoise(&seed, nonce);

    nonce += 1;
    let mut e: PolyVec = getnoise(&seed, nonce);

    let pk: PolyVec = gen_pk(&a, &mut s, &mut e);
}


/*
 * Key derivation wrapper to deserialize the vectors of polynomials
 */
pub fn skey_deriv(pkp: [u8; POLYVEC_BYTES], skp: [u8; 2*POLYVEC_BYTES], seed: [u8; SYMBYTES]) {
    let pk: PolyVec = polyvec_frombytes(&pkp);
    let mut s: PolyVec = polyvec_frombytes(skp[..POLYVEC_BYTES].try_into().unwrap());
    let mut e: PolyVec = polyvec_frombytes(skp[POLYVEC_BYTES..].try_into().unwrap());

    sdk(pk, (s,e), seed);
}

/*
 * Shared key derivation
 */
fn sdk(pk: PolyVec, mut sk: (PolyVec, PolyVec), seed: [u8; 32]) {
    let mut s: PolyVec = sk.0;
    let mut e: PolyVec = sk.1;
    let a: [PolyVec; N] = genmatrix(&seed, 0);

    let pk2: PolyVec = gen_pk(&a, &mut s, &mut e);
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
    for i in 0..d {
        k[i] = round(k[i]);
    }
}

/*
 * Generates a public key from matrix A, secret and error vector
 */
fn gen_pk(a: &[PolyVec; N], s: &mut PolyVec, e: &mut PolyVec) -> PolyVec {
    let mut tmp = polyvec_init();

    let s = polyvec_ntt(s);
    let e = polyvec_ntt(e);

    // A * s + e
    for i in 0..N {
        tmp[i] = polyvec_basemul_acc(a[i], *s);
    }
    let pk: PolyVec = polyvec_add(tmp, *e);

    pk
}

/*
 * Converts element in Zq to a bit
 */
fn round(c: Elem) -> Elem {
    let mut c1: u8 = 0;
    let mut c2: u8 = 0;
    let mut r: Elem = [0, 0, 0];

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
    let mut t: u8 = 0;
    let mut tElem: Elem = [0, 0, 0];

    while(c < RATE-ELEM_BYTES) {
        tElem = elem_frombytes(buf[c..c+ELEM_BYTES].try_into().unwrap());
        t = cmp(tElem, Q);
        t = (t as i8 >> 7) as u8; //t = 0xff if t < 0
        p[offset] = tElem;
        offset += (1u8 & t) as usize;  //only increment if cmp(tElem, Q) < 0 i.e. accept
        c += ELEM_BYTES
    }

    offset
}


fn gen_randoffset(inp: &[u8; POLYVEC_BYTES * 2]) -> Poly {
    let mut buf: [u8; RATE] = [0; RATE];
    let mut r: Poly = init();
    let mut ctr: usize = 0;

    xof_absorb(inp, POLYVEC_BYTES * 2);

    while (ctr < d) {
        xof_squeeze(&mut buf, RATE);
        ctr = rej_sampling(&buf, &mut r, ctr);
    }

    r
}

/*
 * Samples ternary noise from a centered binomial distribution with:
 * - 25%: -1
 * - 50%: 0
 * - 25%: 1
 */
fn cbd(buf: &[u8; NOISE_BYTES], p: &mut PolyVec) {
    let mut c: u8 = 0;
    let mut t: u8 = 0;

    for i in 0..N {
        for j in 0..d/4 {
            c = buf[i*d/4+j];
            for k in 0..4 {
                t = c & 0x3;
                p[i][j*4 + k] = [0,0,0]; //FIXME: load into p
                c >>= 2;
            }
        }
    }
}

fn getnoise(seed: &[u8; SYMBYTES], nonce: u8) -> PolyVec {
    let mut inp: [u8; SYMBYTES + 1] = [0; SYMBYTES + 1];
    let mut buf: [u8; NOISE_BYTES] = [0; NOISE_BYTES];
    let mut p: PolyVec = [init(); N];

    inp[..SYMBYTES].copy_from_slice(seed);
    inp[SYMBYTES] = nonce;
    xof_absorb(&inp, SYMBYTES + 1);

    xof_squeeze(&mut buf, NOISE_BYTES);

    cbd(&buf, &mut p);

    p
}


fn genmatrix(seed: &[u8; SYMBYTES], nonce: u8) -> [[Poly; N]; N] {
    let mut inp: [u8; SYMBYTES + 1] = [0; SYMBYTES+1];
    let mut buf: [u8; RATE] = [0; RATE];
    let mut a: [[Poly; N];N] = [[init(); N]; N];
    let mut ctr: usize = 0;

    inp[0..SYMBYTES].copy_from_slice(seed);
    inp[SYMBYTES] = nonce;

    xof_absorb(&inp, SYMBYTES + 1);

    for i in 0..N {
        for j in 0..N {
            ctr = 0;

            while (ctr < d) {
                xof_squeeze(&mut buf, RATE);
                ctr = rej_sampling(&buf, &mut a[i][j], ctr);
            }
        }
    }

    a
}


mod util {
    use super::*;
    use crate::arithmetic::*;

}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::arithmetic::fq::*;

    #[test]
    fn csub_corr() {
        let mut a: Elem = Q.clone();
        let b: Elem = a;
        
        csub(&mut a);
        assert_eq!();
    }
}
