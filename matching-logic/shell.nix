{ coqVersion ? "8.15"}:
with import <nixpkgs> {};

let

  deps = import ./nix/deps.nix { inherit coqVersion; };
  
  self = mkShell {
    name="ml-in-coq-dev-env";
    buildInputs = [deps.coq deps.stdpp deps.equations];
  };

in
  self
