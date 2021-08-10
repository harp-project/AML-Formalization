{ coqVersion ? "8.13"}:
with import <nixpkgs> {};

let

  deps = import ./nix/deps.nix { inherit coqVersion; };
  
  self = mkShell {
    name="matching-logic-interactive-prover";
    buildInputs = [deps.coq deps.stdpp deps.equations deps.metamath];
  };

in
  self
