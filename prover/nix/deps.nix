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

  mllib = import ../../matching-logic/default.nix { inherit coqVersion;  };

    metamath = pkgs.metamath;
    ocaml = coq.ocamlPackages.ocaml;
    camlp5 = coq.ocamlPackages.camlp5;
    findlib = ncoq.ocamlPackages.findlib;
    zarith = ncoq.ocamlPackages.zarith;

in { coq = ncoq; inherit metamath; inherit mllib;
  inherit ocaml; inherit camlp5;
  inherit findlib; inherit zarith;
}
