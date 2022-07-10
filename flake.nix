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
          buildInputs = [
            self.outputs.packages.${system}.coq-matching-logic
            pkgs.python310Packages.alectryon
            pkgs.coq
          ];
          
          buildPhase = ''
            make coqdoc "PATH_TO_COMPILED_LIBRARY=${self.outputs.packages.${system}.coq-matching-logic}/lib/coq/${coq.coq-version}/MatchingLogic}"
          '';

          dontInstall = true;
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


        packages.default = self.outputs.packages.${system}.coq-matching-logic;
        
        devShell = pkgs.mkShell {
          buildInputs = self.output.packages.default.buildInputs ++ self.output.packages.default.propagatedBuildInputs;
        };
      }
    )
  );
}
