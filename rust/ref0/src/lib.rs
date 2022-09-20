mod arithmetic;

use crate::arithmetic::fq::*;
use crate::arithmetic::poly::*;
use crate::arithmetic::polyvec::*;

const SYMBYTES: usize = 32;

// TODO: replace hardcoded values by expressions

/*
 * Shared key derivation
 */
fn sdk(pk: PolyVec, sk: (PolyVec, PolyVec), seed: [u8; SYMBYTES]) {
    let s: PolyVec = sk.0;
    let e: PolyVec = sk.1;
    let a: [PolyVec; N] = genmatrix(seed, 0);

    let pk2: PolyVec = gen_pk(&a, &s, &e);
    let mut r_in: [u8; POLYVEC_BYTES * 2] = [0; POLYVEC_BYTES * 2];

    r_in[0..POLYVEC_BYTES].copy_from_slice(&polyvec_tobytes(pk));
    r_in[POLYVEC_BYTES..POLYVEC_BYTES*2].copy_from_slice(&polyvec_tobytes(pk2));

    let r = gen_randoffset(r_in);   // r = H(pk, pk2);

    let mut k: Poly = polyvec_basemul_acc(pk, s);
    k = poly_add(k, r);
    rec(&mut k);
}

/*
 * Reconciliation
 */
fn rec(k: &mut Poly) {
    for i in 0..d
    {
        k[i] = round(k[i]);
    }
}

/*
 * Generates a public key from matrix A, secret and error vector
 */
fn gen_pk(a: &[PolyVec; N], s: &PolyVec, e: &PolyVec) -> PolyVec {
    let mut tmp = polyvec_init();
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
fn xof_squeeze(out: &mut [u8])
{
}


/*
 * Placeholder for XOF function (need to check licensing)
 */
fn xof_absorb(inp: &[u8], len: usize)
{
}


/* Description: generates coefficients in Zq from a (uniformly random) stream of bytes
 *
 * Result: number of coefficients generated
 */
fn rej_sampling(buf: &[u8; RATE], p: &mut Poly, mut offset: usize) -> usize {
    let mut c: usize = 0;
    let mut tElem: Elem = [0, 0, 0];

    while(c < RATE-24) {
        tElem = elem_frombytes(buf[c..c+24].try_into().unwrap());
        //TODO: not CT!!!!
        if cmp(tElem, Q) < 0 {
            p[offset] = tElem;
            offset += 1;
        }
        c += 24;
    }

    offset
}


fn gen_randoffset(inp: [u8; POLYVEC_BYTES * 2]) -> Poly {
    let mut buf: [u8; RATE] = [0; RATE];
    let mut r: Poly = init();
    let mut ctr: usize = 0;

    xof_absorb(&inp, POLYVEC_BYTES * 2);

    while (ctr < d) {
        xof_squeeze(&mut buf);
        ctr = rej_sampling(&buf, &mut r, ctr);
    }

    r
}


fn getnoise(seed: [u8; SYMBYTES], nonce: u8) -> PolyVec
{
    let p: PolyVec = [init(); N];

    p
}


// TODO
fn genmatrix(seed: [u8; SYMBYTES], nonce: u8) -> [[Poly; N]; N]
{
    let mut a: [[Poly; N];N] = [[init(); N]; N];

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
