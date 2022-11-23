use core::arch::x86_64;

pub const NRUNS: usize = 10;

pub fn cpucycles() -> u64 {
    let res: u64;
    unsafe {
        res = x86_64::_rdtsc();
    }
    res
}

fn median(t: &mut [u64; NRUNS]) -> u64 {
    t.sort();

    if(NRUNS % 2 == 1) {
        t[NRUNS/2]
    } else {
        (t[NRUNS/2-1] + t[NRUNS/2+1])/2
    }
    
}

fn average(t: &[u64; NRUNS]) -> u64 {
    let mut a: u64 = 0;

    for i in 0..NRUNS {
        a += t[i];
    }

    a/(NRUNS as u64)
}

pub fn print_res(t: &mut [u64; NRUNS]) {
    for i in 0..NRUNS-1 {
        t[i] = t[i+1] - t[i];
    }

    println!("average: {}", average(t));
    println!("median: {}", median(t));
    println!();
}
