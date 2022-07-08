{
  description = "A template that shows all standard flake outputs";

  inputs = {
    nixpkgs.url = "github:NixOs/nixpkgs";
    flake-utils.url = "github:numtide/flake-utils";
   };

  outputs = { self, nixpkgs, flake-utils }: (
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = nixpkgs.legacyPackages.${system};
        packageName = "coq-matching-logic";
        basicDeps = [
          pkgs.coq
          pkgs.coqPackages.equations
          pkgs.coqPackages.stdpp
        ];
      in {
        packages.${packageName} = pkgs.coqPackages.callPackage 
        ( { coq, stdenv }:
        stdenv.mkDerivation {
          name = "coq-matching-logic";

          src = self;
          propagatedBuildInputs = basicDeps;
          enableParallelBuilding = true;

          installFlags = [ "COQLIB=$(out)/lib/coq/${coq.coq-version}/" ];
        } ) { } ;

        devShell = pkgs.mkShell {
          buildInputs = basicDeps;
         };
      }
    )
  );
}
