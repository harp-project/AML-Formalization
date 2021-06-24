{ coqVersion }:
with import <nixpkgs> {};

let
  coqVersion_ = builtins.replaceStrings ["."] ["_"] coqVersion;
  pkgs = import <nixpkgs> { };
  ncoq = pkgs."coq_${coqVersion_}";
  ncoqPackages = pkgs."coqPackages_${coqVersion_}";
  stdpp = ncoqPackages.callPackage
    ( { coq, stdenv, fetchFromGithub }:
      stdenv.mkDerivation {
        name = "coq${coq.coq-version}-stdpp";

        src = fetchGit {
          url = "https://gitlab.mpi-sws.org/iris/stdpp.git";
          rev = lib.strings.fileContents ../deps/stdpp.rev;
        };
        postPatch = ''
          patchShebangs --build coq-lint.sh
        '';
        buildInputs = with coq.ocamlPackages; [ ocaml camlp5 ];
        propagatedBuildInputs = [ coq ];
        enableParallelBuilding = true;

        installFlags = [ "COQLIB=$(out)/lib/coq/${coq.coq-version}/" ];
      } ) { } ;
  equations = ncoqPackages.callPackage
    ( { coq, stdenv, fetchFromGithub }:
      stdenv.mkDerivation {
        name = "coq${coq.coq-version}-equations-head";

        src = fetchGit {
          url = "https://github.com/mattam82/Coq-Equations.git";
          rev = lib.strings.fileContents ../deps/equations.rev;
        };
        buildInputs = with coq.ocamlPackages; [ ocaml ];
        propagatedBuildInputs = [ coq ];
        enableParallelBuilding = true;
        postPatch = ''
          patchShebangs --build configure.sh
        '';
        configurePhase = "./configure.sh";

        installFlags = [ "COQLIB=$(out)/lib/coq/${coq.coq-version}/" ];
      } ) { } ;


in { inherit stdpp; coq = ncoq; inherit equations; }
