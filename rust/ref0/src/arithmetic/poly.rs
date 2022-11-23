use crate::arithmetic::fq::*;

pub const D: usize = 256;
pub const POLY_BYTES: usize = ELEM_BYTES * D;

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

/* TODO
 * In-place NTT
 */
pub fn poly_ntt(a: &mut Poly) {

}

/* TODO
 * In-place Inverse NTT
 */
pub fn poly_invntt(a: &mut Poly) {

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
