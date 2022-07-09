{
  description = "A Coq Library for Matching Logic";

  inputs = {
    nixpkgs.url = "github:NixOs/nixpkgs";
    flake-utils.url = "github:numtide/flake-utils";
   };

  outputs = { self, nixpkgs, flake-utils }: (
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = nixpkgs.legacyPackages.${system};
        coqMatchingLogic = "coq-matching-logic";
        basicDeps = [
          pkgs.coq
          pkgs.coqPackages.equations
          pkgs.coqPackages.stdpp
        ];
      in {
        packages.${coqMatchingLogic} = pkgs.coqPackages.callPackage 
        ( { coq, stdenv }:
        stdenv.mkDerivation {
          name = coqMatchingLogic;

          src = self;
          propagatedBuildInputs = basicDeps;
          enableParallelBuilding = true;

          installFlags = [ "COQLIB=$(out)/lib/coq/${coq.coq-version}/" ];
        } ) { } ;

        devShell = pkgs.mkShell {
          buildInputs = basicDeps ++ [pkgs.python310Packages.alectryon];
         };
      }
    )
  );
}
