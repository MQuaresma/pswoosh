const NLIMBS: usize = 3;
pub type Elem = [u64; NLIMBS];
pub const ELEM_BYTES: usize = 18;

                     /*2^0              2^64               2^128  */
pub const Q: Elem = [0xffffffffffffd000,0xffffffffffffffff,0x0ffff]; // Q = 2^144-12287
pub const HQ: Elem = [0xffffffffffffe800,0xffffffffffffffff,0x7fff];
pub const QQ: Elem = [0xfffffffffffff400,0xffffffffffffffff,0x3fff];
pub const TQQ: Elem = [0xffffffffffffdc00,0xffffffffffffffff,0xbfff];
const BARR: Elem = [0, 0, 0]; //FIXME
const M: u64 = 12287;

/* TODO: replace w/ macro ??
pub const HQ: Elem = [Q[0] >> 1 + ((Q[1] % 1) << 63), Q[1] >> 1 + ((Q[2] % 1) << 63), Q[2] >> 1];  
pub const QQ: Elem = [Q[0] >> 2 + ((Q[1] % 3) << 62), Q[1] >> 1 + ((Q[2] % 3) << 62), Q[2] >> 2];
pub const 3QQ: Elem = add([Q[0] >> 2 + ((Q[1] % 3) << 62), Q[1] >> 1 + ((Q[2] % 3) << 62), Q[2] >> 2];
 */

fn main() {
    let mut a: Elem = [0,0,0x18000];
    let b: Elem = [6,7,8];
    let mut c: Elem = [0, 0, 0];

    let r = cmp(a, b);
    println!("{:x}", r);
}

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

fn mul(a: Elem, b: Elem) -> [u64; 6] {
    let mut h: u64;
    let mut l: u64;
    let mut cf: u64 = 0;
    let mut c: [u64; 6] = [0, 0, 0, 0, 0, 0];

    for i in 0..NLIMBS {
        for j in 0..NLIMBS {
            (h, l) = mulc(b[j], a[i]);
            (cf, c[i+j]) = addc(l, c[i+j], cf);
            (cf, c[i+j+1]) = addc(h, c[i+j+1], cf);
        }
    }
    
    c[5] += cf;

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

    *c = [0, 0, 0];

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
    let mut r0: Elem = [0, 0, 0];
    let mut r1: Elem = [0, 0, 0];
    let mut r: Elem = [0, 0, 0];

    // q1 = x / b^(k-1)
    r0[0] = h[2];
    r0[1] = 0;
    r0[2] = 0;

    //q2 = q1 * BARR
    t = mul(r0, BARR);

    //q3 = q2 / b^(k+1)
    r0[0] = t[4];
    r0[1] = t[5];

    // r0 = x mod b^(k+1)
    r1[0] = h[4];
    r1[1] = h[5];

    // q3 * Q / b ^ (k+1)
    *h = mul(r0, Q);
    r0[0] = h[4];
    r0[1] = h[5];

    // r = r0 - r1
    sub(&mut r, r0, r1);

    r
}
/* Description: Constant time comparison of two field elements
 *
 * Returns -1 if a < b; 0 if a = b; 1 if a > b
 */
pub fn cmp(a: Elem, b: Elem) -> u8 {
    let mut r: u8 = 0;
    let mut mask: u8 = 0xff;
    let mut gt: u8 = 0;
    let mut lt: u8 = 0;
    let mut tr: u64 = 0;

    for i in (0..NLIMBS).rev() {
        tr = (a[i] as i64 - b[i] as i64) as u64;
        lt = ((tr >> 63) as u8) << 7;

        tr = (b[i] as i64 - a[i] as i64) as u64;
        gt = (tr >> 63) as u8;

        //FIXME
        r |= (lt & mask);
        r |= (gt & mask);
    }

    r
}

/* Description: converts stream of bytes into value of type Elem
 *
 */
pub fn elem_frombytes(ep: &[u8; 18]) -> Elem {
    let mut e: Elem = [0, 0, 0];

    for i in 0..NLIMBS-1 {
        e[i] = u64::from_le_bytes(ep[8*i..8*i+8].try_into().unwrap());
    }

    e[NLIMBS-1] = u16::from_le_bytes(ep[8*(NLIMBS-1)..8*(NLIMBS-1)+2].try_into().unwrap()) as u64;

    e
}

pub fn elem_tobytes(e: Elem) -> [u8; ELEM_BYTES] {
    let mut r: [u8; ELEM_BYTES] = [0; ELEM_BYTES];

    for i in 0..NLIMBS-1 {
        r[8*i..8*i+8].copy_from_slice(&e[i].to_le_bytes());
    }

    r[8*(NLIMBS-1)..8*(NLIMBS-1)+2].copy_from_slice(&e[NLIMBS-1].to_le_bytes()[0..2]); //remove trailing bytes

    r
}
