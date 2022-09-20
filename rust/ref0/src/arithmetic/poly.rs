pub const d: usize = 256;
pub const POLY_BYTES: usize = ELEM_BYTES * d;

use crate::arithmetic::fq::*;

pub type Poly = [Elem; d]; // R_q

pub fn init() -> Poly {
    let mut p : Poly = [[0,0,0]; d];
    p
}


pub fn poly_add(a: Poly, b: Poly) -> Poly {
    let mut c: Poly = init();

    for i in 0..d {
        add(&mut c[i], a[i], b[i]);
    }

    c
}

pub fn poly_sub(a: Poly, b: Poly) -> Poly {
    let mut c: Poly = init();

    for i in 0..d {
        sub(&mut c[i], a[i], b[i]);
    }

    c
}

pub fn poly_csub(mut a: Poly) -> Poly {
    for i in 0..d {
        csub(&mut a[i]);
    }
    a
}

/*
 * Base-multiplication in a polynomials
 */
pub fn poly_basemul(a: Poly, b: Poly) -> Poly {
    let mut c: Poly = init();

    for i in 0..d {
        fqmul(&mut c[i], a[i], b[i]); //scalar multiplication in NTT
    }

    c
}

/*
 * Seralizes polynomial
 */
pub fn poly_tobytes(a: Poly) -> [u8; POLY_BYTES] {
    let mut r: [u8; POLY_BYTES] = [0; POLY_BYTES];

    for i in 0..d {
        r[ELEM_BYTES*i..ELEM_BYTES*i+8].copy_from_slice(&elem_tobytes(a[i]));
    }

    r
}
