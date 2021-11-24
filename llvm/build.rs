fn main() {
    cc::Build::new()
        .cpp(true)
        .shared_flag(true)
        .file("src/llvm-gc.cpp")
        .compile("llvmrs");
}
