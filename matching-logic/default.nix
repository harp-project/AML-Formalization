{ coqVersion ? "8.13"}:
with import <nixpkgs> {};

let

  deps = import ./nix/deps.nix { inherit coqVersion; };

  self = stdenv.mkDerivation {
    name = "coq${deps.coq.coq-version}-matching-logic";

    src = ./.;

    buildInputs = [git deps.quickchick];
    propagatedBuildInputs = [deps.coq deps.stdpp];

    buildPhase = ''
        make
    '';

    installFlags = [ "COQLIB=$(out)/lib/coq/${deps.coq.coq-version}/" ];

    meta = {
      description = "A Coq Library for Matching Logic";
      homepage = "https://github.com/harp-project/AML-Formalization";
      license = lib.licenses.lgpl21Only;
    };

    passthru = {
      compatibleCoqVersions = v: builtins.elem v [ "8.12" "8.13" ];
    };
  };
  in self

