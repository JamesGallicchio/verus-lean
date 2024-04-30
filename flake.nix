{
  description = "Sets up the dependencies for verus";

  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs?ref=nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }:

    flake-utils.lib.eachDefaultSystem(system:
      let
      	pkgs     = nixpkgs.legacyPackages.${system};
      	pkgs_x86 = nixpkgs.legacyPackages.x86_64-linux;
      	pkgs_arm = nixpkgs.legacyPackages.aarch64-linux;
      	version  = "0.0.1";
      	src      = self;
      in rec {      
        devShell = pkgs.mkShell {
          shellHook = ''
            PATH=/home/james/Projects/verus-lean/verus/source/target-verus/release:$PATH
            VERUS_Z3_PATH=$(whereis z3 | awk '{print $2}')
          '';
          nativeBuildInputs = with pkgs; [
            rustup
            tokei
      
            llvmPackages_14.libcxxStdenv
            llvmPackages_14.libunwind
            llvmPackages_14.libcxx
            clang-tools_14
            gnumake

            z3_4_12
          ];
        };
      }

    );

}

