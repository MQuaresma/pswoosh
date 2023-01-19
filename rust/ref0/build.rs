use std::process::Command;

fn main() {
    Command::new("make").args(["-C","src/arithmetic", "clean"]).status().unwrap();
    Command::new("make").args(["-C","src/arithmetic"]).status().unwrap();
    cc::Build::new()
        .file("../../supercop-20221122_crypto_stream_aes256ctr_dolbeau_aesenc-int/aesenc-int.c")
        .flag("-march=native")
        .flag("-fomit-frame-pointer")
        .flag("-Wno-unused-function")
        .flag("-fwrapv")
        .flag("-fPIC")
        .flag("-fPIE")
        .compile("aesenc-int");

    // println!("cargo:rustc-link-lib=static=fq");
    println!("cargo:rustc-link-search=./src/arithmetic");
    println!("cargo:rerun-if-changed=src/arithmetic/fq.jinc");
    println!("cargo:rerun-if-changed=src/arithmetic/fq.jazz");
    println!("cargo:rerun-if-changed=src/arithmetic/libfq.a");
    println!("cargo:rerun-if-changed=src/arithmetic/Makefile");
}
