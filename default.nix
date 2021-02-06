{ coqVersion ? "8.13"}:
with import <nixpkgs> {};

let

  deps = import ./nix/deps.nix { inherit coqVersion; };
/*  deps = { coq = ncoq; inherit stdpp; }; */
  self = stdenv.mkDerivation {
    name = "coq${deps.coq.coq-version}-matching-logic";

    src = ./.;

    buildInputs = [ git deps.coq dune deps.stdpp];

    buildPhase = ''
        make
    '';

    installFlags = [ "COQLIB=$(out)/lib/coq/${coq.coq-version}/" ];
  };
  in self

