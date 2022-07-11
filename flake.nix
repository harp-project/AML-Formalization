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
          src = self + "/matching-logic-doc";
          buildInputs = [
            self.outputs.packages.${system}.coq-matching-logic
            pkgs.python310Packages.alectryon
            pkgs.coq
          ];
          

          buildFlags = [ "PATH_TO_COMPILED_LIBRARY=${self.outputs.packages.${system}.coq-matching-logic}/lib/coq/${coq.coq-version}/user-contrib/MatchingLogic" ];

          installTargets = "install-coqdoc";
          # We are not going to install this system-wide, so we can afford not to have the coq version in the path to the docs.
          # We do not want to have the version in the path, since it would be harder for the CI the figure out where the docs live. 
          # installFlags = [ "DOCDIR=$(out)/share/coq/${coq.coq-version}" "INSTALLCOQDOCROOT=coq-matching-logic" ];
          installFlags = [ "DOCDIR=$(out)/share/doc" "INSTALLCOQDOCROOT=coq-matching-logic" ];
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
            pkgs.metamath
            pkgs.ghc
          ];

          postPatch = ''
            patchShebangs --build check-generated-proof-objects.sh patch-extracted-hs.sh
          '';

          buildPhase = ''
            make test
          '';
          
          dontInstall = true;
        } ) { } ;


        packages.default = self.outputs.packages.${system}.coq-matching-logic;
        
        devShell = pkgs.mkShell {
          buildInputs = self.outputs.packages.${system}.default.buildInputs ++ self.outputs.packages.${system}.default.propagatedBuildInputs;
        };
      }
    )
  );
}
