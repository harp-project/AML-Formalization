let
  sources = import ../nix/sources.nix;
  pinned = import sources."nixpkgs" { config = {}; overlays = []; };
in

{ coqVersion ? "8.14"}:
with import <nixpkgs> {};

let

  deps = import ./nix/deps.nix { inherit coqVersion; };
  
  self = mkShell {
    name="matching-logic-interactive-prover";
    buildInputs = [deps.coq deps.mllib deps.findlib deps.zarith
      deps.ocaml deps.camlp5 deps.metamath
      pinned.ghc
    ];
  };

in
  self
