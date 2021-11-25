use std::io;
use std::process::Command;

fn main() -> io::Result<()> {
    let llvm_cxx_flags = llvm_config("--cxxflags")?;

    let mut cpp_build = cc::Build::new();
    cpp_build.cpp(true);
    for flag in llvm_cxx_flags.split_whitespace() {
        cpp_build.flag(flag);
    }
    cpp_build.file("src/llvm-gc.cpp").compile("llvmrs");

    Ok(())
}

fn llvm_config(arg: &str) -> io::Result<String> {
    Command::new("llvm-config").arg(arg).output().map(|output| {
        String::from_utf8(output.stdout).expect("Output from llvm-config is not valid UTF-8")
    })
}
