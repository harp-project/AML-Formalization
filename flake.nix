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

        # Newer version of Alectryon
        packages.alectryon
        = pkgs.python310Packages.buildPythonPackage rec {
                pname = "alectryon";
                version = "1.4.0";

                src = pkgs.fetchFromGitHub {
                    owner = "cpitclaudel";
                    repo = "alectryon";
                    rev = "739b46da22d272e748f60f3efcd2989d696fba71";
                    sha256 = "n+B+f1PPODLGgL36Aj8srDngRp5ZmhKYxikEF+c+5YI=";
                };

                propagatedBuildInputs = [
                   pkgs.python310Packages.pygments
                    pkgs.python310Packages.dominate
                    pkgs.python310Packages.beautifulsoup4
                    pkgs.python310Packages.docutils
                    pkgs.python310Packages.sphinx
                ];

                doCheck = false;
            };

        # The 'matching logic in Coq' library
        packages.coq-matching-logic
        = pkgs.coqPackages.callPackage 
        ( { coq, stdenv }:
        stdenv.mkDerivation {
          name = "coq-matching-logic";
          src = pkgs.lib.cleanSource (pkgs.nix-gitignore.gitignoreSourcePure [
            ".git"
            ".circleci/"
            ".github"
            "result*"
            "*.nix"
            "flake.lock"
            ./.gitignore
          ] ./matching-logic);

          propagatedBuildInputs = [
            coq
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
          src = pkgs.lib.cleanSource (pkgs.nix-gitignore.gitignoreSourcePure [
            ".git"
            ".circleci/"
            ".github"
            "result*"
            "*.nix"
            "flake.lock"
            ./.gitignore
          ] ./matching-logic-doc);
          buildInputs = [
            self.outputs.packages.${system}.alectryon
            self.outputs.packages.${system}.coq-matching-logic
            # we use a newer version which is compatible with new pigments
            #pkgs.python310Packages.alectryon
            pkgs.python310Packages.pygments
            pkgs.python310Packages.pip
            pkgs.coqPackages.serapi
            coq
            pkgs.parallel
          ];
          
          postPatch = ''
            patchShebangs run_alectryon.sh
          '';

          buildFlags = [ "PATH_TO_COMPILED_LIBRARY=${self.outputs.packages.${system}.coq-matching-logic}/lib/coq/${coq.coq-version}/user-contrib/MatchingLogic/" ];

          installTargets = "install-coqdoc install-alectryon";
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
          src = pkgs.lib.cleanSource (pkgs.nix-gitignore.gitignoreSourcePure [
            ".git"
            ".circleci/"
            ".github"
            "result*"
            "*.nix"
            "flake.lock"
            ./.gitignore
          ] ./examples/03_FOL);

          propagatedBuildInputs = [
            self.outputs.packages.${system}.coq-matching-logic
          ];
          installFlags = [ "COQLIB=$(out)/lib/coq/${coq.coq-version}/" ];
        } ) { } ;

        # Example: ProofMode tutorial
        packages.coq-matching-logic-example-proofmode
        = pkgs.coqPackages.callPackage 
        ( { coq, stdenv }:
        stdenv.mkDerivation {
          name = "coq-matching-logic-example-proofmode";
          src = pkgs.lib.cleanSource (pkgs.nix-gitignore.gitignoreSourcePure [
            ".git"
            ".circleci/"
            ".github"
            "result*"
            "*.nix"
            "flake.lock"
            ./.gitignore
          ] ./examples/02_proofmode);
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
