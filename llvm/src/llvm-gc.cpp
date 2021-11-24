#include "llvm/IR/BuiltinGCs.h"

extern "C" void LLVMLinkAllBuiltinGCs() {
  llvm::linkAllBuiltinGCs();
}
