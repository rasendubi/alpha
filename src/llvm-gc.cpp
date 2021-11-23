// #include "llvm/CodeGen/LinkAllCodegenComponents.h"
#include "llvm/IR/BuiltinGCs.h"

extern "C" void alpha_llvm_link_all_builtin_gcs() {
  llvm::linkAllBuiltinGCs();
}
