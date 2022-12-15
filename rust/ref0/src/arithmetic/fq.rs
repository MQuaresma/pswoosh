pub const NLIMBS: usize = 4;
pub type Elem = [u64; NLIMBS];
const K: usize = 214; // bit size of q
pub const ELEM_BYTES: usize = K/8+2; //FIXME
const RAD: usize = 64; //radix

/* Q = 2^214-255 */   /* 2^0              2^64               2^128              2^192   */
pub const Q: Elem =   [0xffffffffffffff01,0xffffffffffffffff,0xffffffffffffffff,0x3fffff];
/* HQ = Q/2 */
pub const HQ: Elem =  [0xffffffffffffff80,0xffffffffffffffff,0xffffffffffffffff,0x1fffff];
/* QQ = Q/4 */
pub const QQ: Elem =  [0xffffffffffffffc0,0xffffffffffffffff,0xffffffffffffffff,0xfffff];
/* TQQ = 3Q/4 */
pub const TQQ: Elem = [0xffffffffffffff40,0xffffffffffffffff,0xffffffffffffffff,0x2fffff]; 
/* BARR = 2^(64*2*NLIMBS) / Q */
const BARR: [u64; 5] = [0x0, 0xff00000, 0x0, 0x0, 0x40000000000];
const M: u64 = 255;

#[link(name = "fq", kind="static")]
extern {
    fn fp_add(rp: *const u64, ap: *const u64, bp: *const u64);
    fn fp_sub(rp: *const u64, ap: *const u64, bp: *const u64);
    fn fp_mul(rp: *const u64, ap: *const u64, bp: *const u64);
    fn fp_toM(rp: *const u64, ap: *const u64);
    fn fp_fromM(rp: *const u64, ap: *const u64);
}

pub fn add(c: &mut Elem, a: Elem, b: Elem) {
    unsafe {
        fp_add(c.as_ptr(), a.as_ptr(), b.as_ptr());
    }
}

pub fn sub(c: &mut Elem, a: Elem, b: Elem) {
    unsafe {
        fp_sub(c.as_ptr(), a.as_ptr(), b.as_ptr());
    }
}

pub fn mul(c: &mut Elem, a: Elem, b: Elem) {
    let mut aM: Elem = fp_init();
    let mut bM: Elem = fp_init();
    let mut cM: Elem = fp_init();
    unsafe {
        fp_toM(aM.as_ptr(), a.as_ptr());
        fp_toM(bM.as_ptr(), b.as_ptr());
        fp_mul(cM.as_ptr(), aM.as_ptr(), bM.as_ptr());
        fp_fromM(c.as_ptr(), cM.as_ptr());
    }
}

pub fn toM(aM: &mut Elem, a: Elem) {
    unsafe {
        fp_toM(aM.as_ptr(), a.as_ptr());
    }
}

pub fn fromM(a: &mut Elem, aM: Elem) {
    unsafe {
        fp_fromM(a.as_ptr(), aM.as_ptr());
    }
}

fn addc(a: u64, b: u64, cf: u64) -> (u64, u64) {
    let r = (a as u128) + (b as u128) + (cf as u128);
    ((r >> 64) as u64, r as u64)
}

/*
 * Conditionally subtracts Q from h if h >= Q in CT
 */
pub fn csub(h: &mut Elem) {
    let mut t: Elem;
    let mut t0: u64;
    let mut mask: u64;
    let mut cf: u64 = 0;

    t = h.clone();

    (cf, t[0]) = addc(t[0], M, cf);
    (cf, t[1]) = addc(t[1], 0, cf);
    (_, t[2]) = addc(t[2], 0, cf);  // cf = 0

    t0 = t[2] >> 16;
    t[2] &= 0xffff;
    (_, mask) = addc(!t0, 1, 0); // prevents overflow when t0 = 0

    t[0] ^= h[0];
    t[1] ^= h[1];
    t[2] ^= h[2];

    t[0] &= mask;
    t[1] &= mask;
    t[2] &= mask;

    h[0] ^= t[0];
    h[1] ^= t[1];
    h[2] ^= t[2];
}

pub fn fp_init() -> Elem {
    [0; NLIMBS]
}

/*
fn addc(a: u64, b: u64, cf: u64) -> (u64, u64) {
let r = (a as u128) + (b as u128) + (cf as u128);
((r >> 64) as u64, r as u64)
}

    fn sbb(a: u64, b: u64, cf: u64) -> (u64, u64) {
    let r = (a as u128) - ((b as u128) + (cf as u128));
    ((r >> 127) as u64, r as u64) //TODO: checkme
}

    fn mulc(a: u64, b: u64) -> (u64, u64) {
    let r = (a as u128) * (b as u128);
    let l = r as u64;
    let h = (r >> 64) as u64;
    (h, l)
}

pub fn add(c: &mut Elem, a: Elem, b: Elem) {
    let mut cf: u64 = 0;

    for i in 0..NLIMBS {
    (cf, c[i]) = addc(a[i], b[i], cf);
}
}

    pub fn sub(c: &mut Elem, a: Elem, b: Elem) {
    let mut cf: u64 = 0;

    for i in 0..NLIMBS {
    (cf, c[i]) = sbb(b[i], a[i], cf);
}
}

    fn mul(a: Elem, b: Elem) -> [u64; 2*NLIMBS] {
    let mut h: u64;
    let mut l: u64;
    let mut cf: u64 = 0;
    let mut c: [u64; 2*NLIMBS] = [0; 2*NLIMBS];

    for i in 0..NLIMBS {
    for j in 0..NLIMBS {
    (h, l) = mulc(b[j], a[i]);
    (cf, c[i+j]) = addc(l, c[i+j], cf);
    (cf, c[i+j+1]) = addc(h, c[i+j+1], cf);
}
}
    
    c[NLIMBS-1] += cf;

    c
}

    /*
     * Performs multiplication with partial modular reduction: (a * b) mod 2^144
     *
     */
    fn mulmod(c: &mut Elem, a: Elem, b: Elem) {
    let mut h: u64;
    let mut l: u64;
    let mut t0: u64;
    let mut t1: u64;
    let mut cf: u64 = 0;

     *c = fq_init();

    (h, l) = mulc(a[0], b[0]);
    (cf, c[0]) = addc(c[0], l, cf);
    (cf, c[1]) = addc(c[1], h, cf);


    (h, l) = mulc(a[1], b[0]);
    (cf, c[1]) = addc(c[1], l, cf);
    (cf, c[2]) = addc(c[2], h, cf); //CHECK: cf = 0 ??

    (h, l) = mulc(a[0], b[1]);
    (cf, c[1]) = addc(c[1], l, cf);
    (cf, c[2]) = addc(c[2], h, cf); //CHECK: cf = 0 ??

    //TODO: handle h and cf
    (h, l) = mulc(a[2], b[0]); // h <= 2 ^ 14
    t0 = l >> 16;
    h <<= 48;
    h |= t0;
    l &= 0xffff;
    (cf, c[2]) = addc(c[2], l, cf);
    (cf, h) = addc(h, 0, cf); //CHECK: cf = 0 ??
    (h, l) = mulc(h, M);
    (cf, c[0]) = addc(c[0], l, cf);
    (cf, c[1]) = addc(c[1], h, cf);
    
    //TODO: handle h and cf
    (h, l) = mulc(a[0], b[2]); // h <= 2 ^ 14
    t0 = l >> 16;
    h <<= 48;
    h |= t0;
    l &= 0xffff;
    (cf, c[2]) = addc(c[2], l, cf);
    (cf, h) = addc(h, 0, cf); //CHECK: cf = 0 ??
    (h, l) = mulc(h, M);
    (cf, c[0]) = addc(c[0], l, cf);
    (cf, c[1]) = addc(c[1], h, cf);

    //TODO: handle h and l
    (h, l) = mulc(a[2], b[1]);
    t0 = l >> 16;
    h <<= 48;
    t0 |= h;
    t1 = l & 0xffff;
    t1 <<= 48;

    (h, l) = mulc(t1, M);    // merge with t1 * (2^50 * M)
    (cf, c[0]) = addc(c[0], l, cf);

    (cf, c[1]) = addc(c[1], h, cf);
    (cf, c[2]) = addc(c[2], 0, cf);  //propagate carry

    (h, l) = mulc(t0, M);
    (cf, c[1]) = addc(c[1], l, cf);
    (cf, c[2]) = addc(c[2], h, cf);  //propagate carry

    //TODO: handle h and l
    (h, l) = mulc(a[1], b[2]);
    t0 = l >> 16;
    h <<= 48;
    t0 |= h;
    t1 = l & 0xffff;
    t1 <<= 48;
    (h, l) = mulc(t1, M);    // merge with t1 * (2^50 * M)
    (cf, c[0]) = addc(c[0], l, cf);

    (cf, c[1]) = addc(c[1], h, cf);
    (cf, c[2]) = addc(c[2], 0, cf);  //propagate carry

    (h, l) = mulc(t0, M);
    (cf, c[1]) = addc(c[1], l, cf);
    (cf, c[2]) = addc(c[2], h, cf);  //propagate carry

    //TODO: handle h and l
    (h, l) = mulc(a[2], b[2]);
    t0 = l >> 16;
    h <<= 48;
    t0 |= h;
    t1 = l & 0xffff;
    t1 <<= 48;

    (h, l) = mulc(t1, M);
    (cf, c[1]) = addc(c[1], l, cf);

    (cf, c[2]) = addc(c[2], h, cf); // CHECK: cf == 0 ??
    (h, l) = mulc(t0, M);           // CHECK: bounds for h
    (cf, c[2]) = addc(c[2], l, cf);
    
    t0 = c[2] >> 16;
    h <<= 48;
    t0 |= h;
    c[2] &= 0xffff;

    (h, l) = mulc(t0, M);
    (cf, c[0]) = addc(c[0], l, cf);
    (cf, c[1]) = addc(c[1], h, cf);
    (_, c[2]) = addc(c[2], 0, cf);  // CHECK: cf == 0 ??
}

    /*
     * Conditionally subtracts Q from h if h >= Q in CT
     */
    pub fn csub(h: &mut Elem) {
    let mut t: Elem;
    let mut t0: u64;
    let mut mask: u64;
    let mut cf: u64 = 0;

    t = h.clone();

    (cf, t[0]) = addc(t[0], M, cf);
    (cf, t[1]) = addc(t[1], 0, cf);
    (_, t[2]) = addc(t[2], 0, cf);  // cf = 0

    t0 = t[2] >> 16;
    t[2] &= 0xffff;
    (_, mask) = addc(!t0, 1, 0); // prevents overflow when t0 = 0

    t[0] ^= h[0];
    t[1] ^= h[1];
    t[2] ^= h[2];

    t[0] &= mask;
    t[1] &= mask;
    t[2] &= mask;

    h[0] ^= t[0];
    h[1] ^= t[1];
    h[2] ^= t[2];
}

    pub fn fqmul(c: &mut Elem, a: Elem, b: Elem) {
}

    /* TODO: doesn't work with h >= Q^2
     * Efficient CT modular reduction
     */ 
    fn barrett_red(h: &mut [u64; 6]) -> Elem {
    let mut t: [u64; 6];
    let mut r0: Elem = fq_init();
    let mut r1: Elem = fq_init();
    let mut r: Elem = fq_init();

    // q1 = x / b^(k-1)
    r0[0] = h[2];
    r0[1] = 0;
    r0[2] = 0;

    //q2 = q1 * BARR
    // t = mul(r0, BARR);
    t = [0; 6];

    //q3 = q2 / b^(k+1)
    r0[0] = t[4];
    r0[1] = t[5];

    // r0 = x mod b^(k+1)
    r1[0] = h[4];
    r1[1] = h[5];

    // q3 * Q / b ^ (k+1)
    // *h = mul(r0, Q);
    r0[0] = h[4];
    r0[1] = h[5];

    // r = r0 - r1
    sub(&mut r, r0, r1);

    r
}
 */

/* Description: Constant time comparison of two field elements
 *
 * Returns -1 if a < b; 0 if a = b; 1 if a > b
 */
pub fn cmp(a: Elem, b: Elem) -> u8 {
    let mut r: u8 = 0;
    let mut mask: u8 = 0xff;
    let mut s_ai: i64;
    let mut s_bi: i64;
    let mut gt: u8;
    let mut lt: u8;

    for i in (0..NLIMBS).rev() {
        s_ai = a[i] as i64;
        s_bi = b[i] as i64;

        lt = (((s_ai - s_bi) as u64) >> 63) as u8;
        gt = (((s_bi - s_ai) as u64) >> 63) as u8;

        //  high order limb comparisons take precedence
        lt &= mask;
        gt &= mask;

        mask ^= (lt | gt);
        r |= (lt << 7);
        r |= gt;
    }

    r
}

/* Converts stream of bytes into value of type Elem
 *
 */
pub fn elem_frombytes(ep: &[u8; ELEM_BYTES]) -> Elem {
    let mut e: Elem = fp_init();

    for i in 0..NLIMBS-1 {
        e[i] = u64::from_le_bytes(ep[8*i..8*i+8].try_into().unwrap());
    }

    e[NLIMBS-1] = u32::from_le_bytes(ep[8*(NLIMBS-1)..8*(NLIMBS-1)+4].try_into().unwrap()) as u64;

    e
}
/* Converts field element into a byte buffer
 *
 * n.b: currently exporting one extra unnecessary/zero byte for simplicity reasons
 */
pub fn elem_tobytes(e: Elem) -> [u8; ELEM_BYTES] {
    let mut r: [u8; ELEM_BYTES] = [0; ELEM_BYTES];

    for i in 0..NLIMBS-1 {
        r[8*i..8*i+8].copy_from_slice(&e[i].to_le_bytes());
    }

    r[8*(NLIMBS-1)..8*(NLIMBS-1)+4].copy_from_slice(&e[NLIMBS-1].to_le_bytes()[0..4]); //remove trailing bytes

    r
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_fp_add() {
        let a: Elem = QQ.clone();
        let b: Elem = QQ.clone();
        let rc: Elem = HQ.clone();
        let mut c: Elem = fp_init();

        add(&mut c, a, b); // q/4 + q/4

        assert_eq!(rc, c, "fp_add: Values don't match");
    }

    #[test]
    fn test_fp_sub() {
        let a: Elem = HQ.clone();
        let b: Elem = QQ.clone();
        let rc: Elem = QQ.clone();
        let mut c: Elem = fp_init();

        sub(&mut c, a, b); // q/2 - q/4

        assert_eq!(rc, c, "fp_sub: Values don't match");
    }

    #[test]
    fn test_fp_mul() {
        let a: Elem = QQ.clone();
        let b: Elem = [0x03, 0x0, 0x0, 0x0];
        let rc: Elem = TQQ.clone();
        let mut c: Elem = fp_init();

        mul(&mut c, a, b); // q/4 * 3

        assert_eq!(rc, c, "fp_mul: Values don't match");
    }

    #[test]
    fn test_fp_bytes() {
        let a: Elem = QQ.clone();
        let mut r: Elem = fp_init();
        let mut b: [u8; ELEM_BYTES] = [0; ELEM_BYTES];

        b = elem_tobytes(a);
        r = elem_frombytes(&b);
        assert_eq!(a, r, "fp_bytes: Values don't match");
    }

    #[test]
    fn test_cmp() {
        let a: Elem = HQ.clone();

        assert_eq!(cmp(a, HQ), 0x00);
        assert_eq!(cmp(a, QQ), 0x01);
        assert_eq!(cmp(a, TQQ), 0x80);
    }
}
