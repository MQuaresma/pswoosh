use crate::arithmetic::poly::*;

pub const N: usize = 28;
pub const POLYVEC_BYTES: usize = POLY_BYTES * N;

pub type PolyVec = [Poly; N];  // R_q^N

pub fn polyvec_init() -> PolyVec {
    [poly_init(); N]
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
    let mut c: Poly;
    let mut t: Poly;

    c = poly_basemul(a[0], b[0]);
    
    for i in 1..N {
        t = poly_basemul(a[i], b[i]);
        c = poly_add(c, t);
    }

    c
}

pub fn polyvec_ntt(a: &mut PolyVec) {
    for i in 0..N {
        poly_ntt(&mut a[i]);
    }
}

pub fn polyvec_invntt(a: &mut PolyVec) {
    for i in 0..N {
        poly_invntt(&mut a[i]);
    }
}

pub fn polyvec_frombytes(a: &[u8; POLYVEC_BYTES]) -> PolyVec {
    let mut pv: PolyVec = polyvec_init();

    for i in 0..N {
        pv[i] = poly_frombytes(a[POLY_BYTES*i..POLY_BYTES*i+POLY_BYTES].try_into().unwrap());
    }

    pv
}

pub fn polyvec_tobytes(a: PolyVec) -> [u8; POLYVEC_BYTES] {
    let mut r: [u8; POLYVEC_BYTES] = [0; POLYVEC_BYTES];

    for i in 0..N {
        r[POLY_BYTES*i..POLY_BYTES*i+POLY_BYTES].copy_from_slice(&poly_tobytes(a[i]));
    }

    r
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_polyvec_add() {
        println!("polyvec_add: ");
        let a: [PolyVec; 5] = [polyvec_init(); 5];

        let c = polyvec_add(a[0], a[1]);
    }
}
