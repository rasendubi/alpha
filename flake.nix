{
  description = "alpha";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
  };

  outputs = { self, nixpkgs }: {
    devShell.x86_64-linux =
      let pkgs = nixpkgs.legacyPackages.x86_64-linux;
      in pkgs.mkShell {
        nativeBuildInputs = [
          pkgs.rustup
          pkgs.lldb
        ];
        buildInputs = [
          pkgs.llvm_13
          pkgs.libffi
          pkgs.libxml2
        ];

        RUST_LOG = "alpha::execution_session,alpha::gc[collect_garbage]=INFO";
      };
  };
}
