{ coqVersion ? "8.13"}:
with import <nixpkgs> {};

let

  deps = import ./nix/deps.nix { inherit coqVersion; };
  
  self = mkShell {
    name="matching-logic-interactive-prover";
    buildInputs = [deps.coq deps.mllib deps.equations deps.findlib deps.zarith
      deps.ocaml deps.camlp5 deps.metamath
      ghc
    ];
  };

in
  self
