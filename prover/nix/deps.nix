{ coqVersion }:
with import <nixpkgs> {};

let
  coqVersion_ = builtins.replaceStrings ["."] ["_"] coqVersion;
  pkgs = import <nixpkgs> { };
  ncoq = pkgs."coq_${coqVersion_}";
  ncoqPackages = pkgs."coqPackages_${coqVersion_}";

  mllib = import ../../matching-logic/default.nix { inherit coqVersion;  };

   equations = ncoqPackages.callPackage
    ( { coq, stdenv, fetchFromGithub }:
      stdenv.mkDerivation {
        name = "coq${coq.coq-version}-stdpp";

        src = fetchGit {
          url = "https://github.com/mattam82/Coq-Equations.git";
          ref = "8.13";
          rev = "a7f1a02745092f4ddce4f91d0a5d69fb85376c34";
        };

        postPatch = ''
          patchShebangs --build configure.sh
        '';
        configurePhase = "./configure.sh";

        buildInputs = with coq.ocamlPackages; [ ocaml camlp5 zarith findlib ];
        propagatedBuildInputs = [ coq ];
        enableParallelBuilding = true;

        installFlags = [ "COQLIB=$(out)/lib/coq/${coq.coq-version}/" ];
      } ) { } ;

    metamath = pkgs.metamath;
in { coq = ncoq; inherit equations; inherit metamath; inherit mllib; }
