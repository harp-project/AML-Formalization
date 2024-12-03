{
  description = "A Coq Library for Matching Logic";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/release-24.11";
    flake-utils.url = "github:numtide/flake-utils";
    pyk.url = "github:runtimeverification/pyk/v0.1.491";
   };

  outputs = { self, nixpkgs, flake-utils, pyk }: (
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = nixpkgs.legacyPackages.${system};
        coqPackages = pkgs.coqPackages_8_20;
        pyk-py = pyk.packages.${system}.pyk-python311;
        python = pyk-py.python;
        # stdpp = coqPackages.stdpp.overrideAttrs (o : { src = fetchTarball { url = "https://gitlab.mpi-sws.org/iris/stdpp/-/archive/master/stdpp-master.tar.bz2"; sha256="sha256:1f8v61mcixcai8ki1l350hlnypc7v3rrxjcx4m0xclb01rlf9afa";}; });

        # The 'matching logic in Coq' library
        
        coq-matching-logic = { coqPackages }: (
        coqPackages.callPackage 
        ( { coq, stdenv }:
        stdenv.mkDerivation {
          name = "coq-matching-logic";
          src = ./matching-logic;

          propagatedBuildInputs = [
            coq
            coqPackages.equations
            # stdpp
            coqPackages.stdpp
            coqPackages.LibHyps
          ];
          enableParallelBuilding = true;
          installFlags = [ "COQLIB=$(out)/lib/coq/${coq.coq-version}/" ];

          passthru = { inherit coqPackages; };
        } ) { }
	);


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
        packages.coq-matching-logic = coq-matching-logic { coqPackages = coqPackages; };

        # The 'matching logic in Coq' library
        # packages.coq-matching-logic-v8_17 = coq-matching-logic { coqPackages = pkgs.coqPackages_8_17; };

        # Documentation of the 'matching logic in Coq' library
        packages.coq-matching-logic-doc
        = coqPackages.callPackage 
        ( { coq, stdenv }:
        stdenv.mkDerivation {
          name = "coq-matching-logic-doc";
          src = ./matching-logic-doc;
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

          installTargets = "install-coqdoc";
          #installTargets = "install-coqdoc install-alectryon install-snippets";

          # We are not going to install this system-wide, so we can afford not to have the coq version in the path to the docs.
          # We do not want to have the version in the path, since it would be harder for the CI the figure out where the docs live. 
          # installFlags = [ "DOCDIR=$(out)/share/coq/${coq.coq-version}" "INSTALLCOQDOCROOT=coq-matching-logic" ];
          installFlags = [ "DOCDIR=$(out)/share/doc" "INSTALLCOQDOCROOT=coq-matching-logic" ];
        } ) { } ;


        packages.koreimport
        = python.pkgs.buildPythonApplication {
          name = "koreimport";
          src = ./koreimport;
          format = "pyproject";
          propagatedBuildInputs = [
            python.pkgs.setuptools
            pyk-py
          ];
        };


        packages.koreimport-test
        = pkgs.stdenv.mkDerivation {
          name = "koreimport-test";
          src = ./koreimport-test;

          buildInputs = [
            pkgs.bash
            self.outputs.packages.${system}.coq-matching-logic
            self.outputs.packages.${system}.koreimport
            coqPackages.coq
            coqPackages.equations
            coqPackages.stdpp
          ];


          configurePhase = "";
          buildPhase = ''
            koreimport -o out.v --module IMP korefiles/imp.kore
            coqc out.v
            mkdir -p $out
          '';
          installPhase = "";
        };


        # Example: FOL embedded in matching logic
        packages.coq-matching-logic-example-fol
        = coqPackages.callPackage 
        ( { coq, stdenv }:
        stdenv.mkDerivation {
          name = "coq-matching-logic-example-fol";
          src = ./examples/03_FOL;

          propagatedBuildInputs = [
            self.outputs.packages.${system}.coq-matching-logic
          ];
          installFlags = [ "COQLIB=$(out)/lib/coq/${coq.coq-version}/" ];
          passthru = { inherit coqPackages; };
        } ) { } ;

        # Example: ProofMode tutorial
        packages.coq-matching-logic-example-proofmode
        = coqPackages.callPackage 
        ( { coq, stdenv }:
        stdenv.mkDerivation {
          name = "coq-matching-logic-example-proofmode";
          src = ./examples/02_proofmode;

          propagatedBuildInputs = [
            self.outputs.packages.${system}.coq-matching-logic
          ];
          installFlags = [ "COQLIB=$(out)/lib/coq/${coq.coq-version}/" ];
          passthru = { inherit coqPackages; };
        } ) { } ;
 
        
        # Metamath exporter: Build & Test
        packages.coq-matching-logic-mm-exporter
        = coqPackages.callPackage 
        ( { coq, stdenv }:
        stdenv.mkDerivation {
          name = "coq-matching-logic-mm-exporter";
          src = ./prover;

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

          passthru = { inherit coqPackages; };
        } ) { } ;


        packages.default = self.outputs.packages.${system}.coq-matching-logic;
        
        devShells = {
          coq-matching-logic =
            let
              coq-matching-logic = self.outputs.packages.${system}.coq-matching-logic;
            in
              pkgs.mkShell {
                inputsFrom = [coq-matching-logic];
                packages = [coq-matching-logic.coqPackages.coq-lsp];
              };


          #coq-matching-logic-v8_17 =
          #  let
          #    coq-matching-logic = self.outputs.packages.${system}.coq-matching-logic-v8_17;
          #  in
          #    pkgs.mkShell {
          #      inputsFrom = [coq-matching-logic];
          #      packages = [coq-matching-logic.coqPackages.coq-lsp];
          #    };

          coq-matching-logic-example-fol =
            let
              coq-matching-logic-example-fol = self.outputs.packages.${system}.coq-matching-logic-example-fol;
            in
              pkgs.mkShell {
                inputsFrom = [coq-matching-logic-example-fol];
                packages = [coq-matching-logic-example-fol.coqPackages.coq-lsp];
              };


          coq-matching-logic-example-proofmode =
            let
              coq-matching-logic-example-proofmode = self.outputs.packages.${system}.coq-matching-logic-example-proofmode;
            in
              pkgs.mkShell {
                inputsFrom = [coq-matching-logic-example-proofmode];
                packages = [coq-matching-logic-example-proofmode.coqPackages.coq-lsp];
              };

          koreimport =
            let
              koreimport = self.outputs.packages.${system}.koreimport;
            in
              pkgs.mkShell {
                inputsFrom = [koreimport];
                packages = [pkgs.python311Packages.mypy];
              };

          koreimport-test =
            let
              koreimport-test = self.outputs.packages.${system}.koreimport-test;
            in
              pkgs.mkShell {
                inputsFrom = [koreimport-test];
                #packages = [koreimport-test.coqPackages.coq-lsp];
              };


          coq-matching-logic-mm-exporter =
            let
              coq-matching-logic-mm-exporter = self.outputs.packages.${system}.coq-matching-logic-mm-exporter;
            in
              pkgs.mkShell {
                inputsFrom = [coq-matching-logic-mm-exporter];
                packages = [coq-matching-logic-mm-exporter.coqPackages.coq-lsp];
              };
        };
      }
    )
  );
}
