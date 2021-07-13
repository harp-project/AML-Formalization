{ coqVersion }:
with import <nixpkgs> {};

let
  sources = import ./sources.nix;
  coq = import sources."coq" { };
  coqVersion = "8.14-git";
  pkgs = import <nixpkgs> { };

  stdpp = pkgs.callPackage
    ( { stdenv, fetchFromGithub }:
      stdenv.mkDerivation {
        name = "coq${coqVersion}-stdpp";

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

        installFlags = [ "COQLIB=$(out)/lib/coq/${coqVersion}/" ];
      } ) { } ;

   equations = pkgs.callPackage
    ( { stdenv, fetchFromGithub }:
      stdenv.mkDerivation {
        name = "coq${coqVersion}-equations";

        src = fetchGit {
          url = "https://github.com/mattam82/Coq-Equations.git";
          ref = "master";
          rev = "5fbb32364ba9952d71c7262090c27013729653f7";
        };

        postPatch = ''
          patchShebangs --build configure.sh
        '';
        configurePhase = "./configure.sh";

        buildInputs = with coq.ocamlPackages; [ ocaml camlp5 zarith findlib ];
        propagatedBuildInputs = [ coq ];
        enableParallelBuilding = true;

        installFlags = [ "COQLIB=$(out)/lib/coq/${coqVersion}/" ];
      } ) { } ;
in { inherit coq; inherit stdpp; inherit equations; }
