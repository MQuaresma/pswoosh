use crate::arithmetic::fq::*;

pub const D: usize = 256;
pub const POLY_BYTES: usize = ELEM_BYTES * D;
const ZETAS: [Elem; D] = [[0; NLIMBS]; D]; // FIXME
const ZETAS_INV: [Elem; D] = [[0; NLIMBS]; D]; // FIXME

pub type Poly = [Elem; D]; // R_q


pub fn poly_init() -> Poly {
    [fp_init(); D]
}


pub fn poly_add(a: Poly, b: Poly) -> Poly {
    let mut c: Poly = poly_init();

    for i in 0..D {
        add(&mut c[i], a[i], b[i]);
    }

    c
}

pub fn poly_sub(a: Poly, b: Poly) -> Poly {
    let mut c: Poly = poly_init();

    for i in 0..D {
        sub(&mut c[i], a[i], b[i]);
    }

    c
}

pub fn poly_csub(mut a: Poly) -> Poly {
    for i in 0..D {
        csub(&mut a[i]);
    }
    a
}

/*
 * Base-multiplication in a polynomials
 */
pub fn poly_basemul(a: Poly, b: Poly) -> Poly {
    let mut c: Poly = poly_init();

    for i in 0..D {
        mul(&mut c[i], a[i], b[i]); //scalar multiplication in NTT
    }

    c
}

/* CHECK ME
 * In-place NTT
 */
pub fn poly_ntt(a: &mut Poly) {
    let mut len: usize = D>>2;
    let mut off: usize;
    let mut joff: usize;
    let mut zoff: usize = 0;
    let mut t: Elem;
    let mut r: Elem = fp_init();

    for i in 0..7 {
        off = 0;
        while(off < D) {
            zoff += 1;
            joff = off;
            for _j in 0..len {
                t = a[joff+len];
                mul(&mut r, t, ZETAS[zoff]);
                t = a[joff];
                add(&mut a[joff], t, r);
                sub(&mut a[joff+len], t, r);
                joff += 1;
            }
            off += len;
        }
        len >>= 1;
    }
}

/* TODO
 * In-place Inverse NTT
 */
pub fn poly_invntt(a: &mut Poly) {
    let mut len: usize = 1;
    let mut off: usize;
    let mut joff: usize;
    let mut zoff: usize = 0;
    let mut t: Elem;
    let mut r: Elem;
    let mut m: Elem = fp_init();

    for i in 0..7 {
        off = 0;
        while(off < D) {
            joff = off;
            for j in 0..len {
                t = a[joff];
                r = a[joff+len];
                add(&mut a[joff], t, r);
                sub(&mut m, t, r);
                mul(&mut a[joff+len], m, ZETAS_INV[zoff]);
                joff += 1;
            }
            off += len;
            zoff += 1;
        }
        len <<= 1;
    }

    for i in 0..D {
        t = a[i];
        mul(&mut t, a[i], ZETAS_INV[D-1]);
        a[i] = t;
    }
}

/*
 * Deserializes polynomial
 */
pub fn poly_frombytes(rp: &[u8; POLY_BYTES]) -> Poly {
    let mut p: Poly = poly_init();

    for i in 0..D {
        p[i] = elem_frombytes(rp[ELEM_BYTES*i..ELEM_BYTES*i+ELEM_BYTES].try_into().unwrap());
    }

    p
}

/*
 * Seralizes polynomial
 */
pub fn poly_tobytes(a: Poly) -> [u8; POLY_BYTES] {
    let mut r: [u8; POLY_BYTES] = [0; POLY_BYTES];

    for i in 0..D {
        r[ELEM_BYTES*i..ELEM_BYTES*i+8].copy_from_slice(&elem_tobytes(a[i]));
    }

    r
}
