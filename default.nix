{ coqVersion ? "8.13"}:
with import <nixpkgs> {};

let
  coqVersion_ = builtins.replaceStrings ["."] ["_"] coqVersion;
  _ = builtins.trace coqVersion_ 0;
  pkgs = import <nixpkgs> { };
  ncoq = pkgs."coq_${coqVersion_}";
  ncoqPackages = pkgs."coqPackages_${coqVersion_}";
  /*stdpp = import ./nix/stdpp.nix;*/
  stdpp = ncoqPackages.callPackage
    ( { coq, stdenv, fetchFromGithub }:
      stdenv.mkDerivation {
        name = "coq${coq.coq-version}-stdpp";

        src = fetchGit {
          url = "https://gitlab.mpi-sws.org/iris/stdpp.git";
          rev = "bcebd707d223fe539f8db924dc3bac1fe8c6e678";
        };
        buildInputs = with coq.ocamlPackages; [ ocaml camlp5 ];
        propagatedBuildInputs = [ coq ];
        enableParallelBuilding = true;

        installFlags = [ "COQLIB=$(out)/lib/coq/${coq.coq-version}/" ];
      } ) { } ;
  self = stdenv.mkDerivation {
    name = "coq${ncoq.coq-version}-matching-logic";

    src = ./.;

    buildInputs = [ git ncoq dune stdpp];

    buildPhase = ''
        make
    '';

    installFlags = [ "COQLIB=$(out)/lib/coq/${coq.coq-version}/" ];
  };
  in self

