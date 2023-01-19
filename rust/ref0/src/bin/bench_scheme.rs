use ref0::*;
use ref0::util::*;

fn main() {
    let mut seed: [u8; SYMBYTES] = [0; SYMBYTES];
    let mut a: Matrix = matrix_init();
    let mut pkp: [u8; PUBLICKEY_BYTES] = [0; PUBLICKEY_BYTES];
    let mut skp: [u8; SECRETKEY_BYTES] = [0; SECRETKEY_BYTES];
    let mut ss: [u8; SYMBYTES] = [0; SYMBYTES];
    let mut t: [u64; NRUNS] = [0; NRUNS];

   for i in 0..NRUNS {
        t[i] = rdtsc();
        (skp, pkp) = keygen(&a, true);
    }
    println!("keygen (cycles): ");
    print_res(&mut t);

    for i in 0..NRUNS {
        t[i] = rdtsc();
        ss = skey_deriv(pkp, pkp, skp, true);
    }
    println!("skey_deriv (cycles): ");
    print_res(&mut t);
}
