{
  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let pkgs = nixpkgs.legacyPackages.${system};
      in
      rec {
        defaultPackage = packages.agda-smash;
        packages = {
          agda-smash = pkgs.runCommand "agda-smash"
            {
              buildInputs = [
                pkgs.gnumake
                (pkgs.agda.withPackages (p: [ p.standard-library ]))
              ];
            }
            ''
              ${pkgs.gnumake}/bin/make OUT_DIR=$out
            '';
        };
        checks = {
          build = self.defaultPackage."${system}";
        };
      }
    );
}
