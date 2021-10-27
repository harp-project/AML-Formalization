let
  sources = import ../../nix/sources.nix;
  pinned = import sources."nixpkgs" { config = {}; overlays = []; };
in

{ coqVersion ? "8.14"}:
with import <nixpkgs> {};

let

  deps = import ./nix/deps.nix { inherit coqVersion; };
  
  self = mkShell {
    name="matching-logic-example-03-FOL";
    buildInputs = [deps.coq deps.mllib]; 
  };

in
  self
