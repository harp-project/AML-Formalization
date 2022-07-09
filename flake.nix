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

      in {
        # The 'matching logic in Coq' library
        packages.coq-matching-logic
        = pkgs.coqPackages.callPackage 
        ( { coq, stdenv }:
        stdenv.mkDerivation {
          name = "coq-matching-logic";
          src = self + "/matching-logic";
          propagatedBuildInputs = [
            pkgs.coq
            pkgs.coqPackages.equations
            pkgs.coqPackages.stdpp
          ];
          enableParallelBuilding = true;
          installFlags = [ "COQLIB=$(out)/lib/coq/${coq.coq-version}/" ];
        } ) { } ;

        # Documentation of the 'matching logic in Coq' library
        packages.coq-matching-logic-doc
        = pkgs.coqPackages.callPackage 
        ( { coq, stdenv }:
        stdenv.mkDerivation {
          name = "coq-matching-logic-doc";
          src = self + "/matching-logic";
          propagatedBuildInputs =
            self.outputs.packages.${system}.coq-matching-logic.propagatedBuildInputs
          ++ [
            pkgs.python310Packages.alectryon
          ];
          enableParallelBuilding = true;
          installTargets = "install-doc";
          #installFlags = [ "COQLIB=$(out)/lib/coq/${coq.coq-version}/" ];
        } ) { } ;

        # Example: FOL embedded in matching logic
        packages.coq-matching-logic-example-fol
        = pkgs.coqPackages.callPackage 
        ( { coq, stdenv }:
        stdenv.mkDerivation {
          name = "coq-matching-logic-example-fol";
          src = self + "/examples/03_FOL";
          propagatedBuildInputs = [
            self.outputs.packages.${system}.coq-matching-logic
          ];
          installFlags = [ "COQLIB=$(out)/lib/coq/${coq.coq-version}/" ];
        } ) { } ;
        
        # Metamath exporter: Build & Test
        packages.coq-matching-logic-mm-exporter
        = pkgs.coqPackages.callPackage 
        ( { coq, stdenv }:
        stdenv.mkDerivation {
          name = "coq-matching-logic-mm-exporter";
          src = self + "/prover";
          propagatedBuildInputs = [
            self.outputs.packages.${system}.coq-matching-logic
          ];

          buildPhase = ''
            make test
          '';
          
          dontInstall = true;
        } ) { } ;


        #devShell = pkgs.mkShell {
        #  buildInputs = basicDeps ++ [pkgs.python310Packages.alectryon];
        # };
      }
    )
  );
}
