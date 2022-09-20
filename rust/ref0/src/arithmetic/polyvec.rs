use crate::arithmetic::poly::*;

pub const N: usize = 28;
pub const POLYVEC_BYTES: usize = POLY_BYTES * N;

pub type PolyVec = [Poly; N];  // R_q^N

pub fn polyvec_init() -> PolyVec {
    let mut p : PolyVec = [init(); N];
    p
}


pub fn polyvec_add(a: PolyVec, b: PolyVec) -> PolyVec {
    let mut c: PolyVec = polyvec_init();

    for i in 0..N {
        c[i] = poly_add(a[i], b[i]);
    }

    c
}

/*
 * Base-multiplication in a polynomials
 */
pub fn polyvec_basemul_acc(a: PolyVec, b: PolyVec) -> Poly {
    let mut c: Poly = init();
    let mut t: Poly = init();

    c = poly_basemul(a[0], b[0]);
    
    for i in 1..N {
        t = poly_basemul(a[i], b[i]);
        c = poly_add(c, t);
    }

    c
}

pub fn polyvec_tobytes(a: PolyVec) -> [u8; POLYVEC_BYTES] {
    let mut r: [u8; POLYVEC_BYTES] = [0; POLYVEC_BYTES];

    for i in 0..d {
        r[POLY_BYTES*i..POLY_BYTES*i+POLY_BYTES].copy_from_slice(&poly_tobytes(a[i]));
    }

    r
}
