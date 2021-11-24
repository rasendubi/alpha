pub mod shadow_stack;

pub fn link_all_builtin_gcs() {
    unsafe {
        LLVMLinkAllBuiltinGCs();
    }
}

extern "C" {
    fn LLVMLinkAllBuiltinGCs();
}
