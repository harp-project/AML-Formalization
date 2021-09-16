let
  sources = import ../../nix/sources.nix;
  pinned = import sources."nixpkgs" { config = {}; overlays = []; };
in

{ coqVersion }:
with import <nixpkgs> {};

let
  coqVersion_ = builtins.replaceStrings ["."] ["_"] coqVersion;
  pkgs = pinned;
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

  quickchick = ncoqPackages.QuickChick; /*

  quickchick = ncoqPackages.callPackage
    ( { coq, stdenv, fetchFromGithub }:
      stdenv.mkDerivation {
        name = "coq${coq.coq-version}-quickchick";

        src = fetchGit {
          url = "https://github.com/QuickChick/QuickChick.git";
          rev = "80f4c88e949f25b6167993ce6a7e34ed29ca44cb";
        };

        buildInputs = (with coq.ocamlPackages; [ ocaml camlp5 ocamlbuild findlib zarith menhir ])
                      ++ [pkgs.perl pkgs.ncurses pkgs.dune_2]
                      ++ [ncoqPackages.mathcomp ncoqPackages.simple-io];
        propagatedBuildInputs = [ coq ];
        enableParallelBuilding = true;

        buildPhase = ''
          dune build
        '';

        installPhase = ''
          dune install --prefix=$out/lib/coq/${coq.coq-version}/
        '';

        setupHook = writeText "setupHook.sh" ''
          export OCAMLPATH="''${OCAMLPATH:-""}''${OCAMLPATH:+:}''$1/lib/coq/${coq.coq-version}/user-contrib/"
        '';
      } ) { } ;

     */
in { inherit stdpp; inherit quickchick; coq = ncoq; otherDeps = (with coq.ocamlPackages; [ ocaml camlp5 ocamlbuild findlib zarith menhir ]);
}
