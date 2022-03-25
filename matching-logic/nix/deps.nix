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

  dpdgraph = ncoqPackages.callPackage
    ( { coq, stdenv, fetchFromGithub }:
      stdenv.mkDerivation {
        name = "coq${coq.coq-version}-dpdgraph";

        src = fetchGit {
          url = "https://github.com/coq-community/coq-dpdgraph.git";
          ref = "coq-v8.14";
          rev = lib.strings.fileContents ../deps/dpdgraph.rev;
        };
        buildInputs = [autoconf] ++ (with coq.ocamlPackages; [ ocaml camlp5 findlib ocamlgraph zarith]);
        propagatedBuildInputs = [ coq ];
        enableParallelBuilding = true;

        preConfigure = ''autoconf'';
        preInstall = ''
          mkdir -p $out/bin
        '';
        installFlags = [ "COQLIB=$(out)/lib/coq/${coq.coq-version}/" "BINDIR=$(out)/bin" ];
      } ) { } ;

   equations = ncoqPackages.callPackage
    ( { coq, stdenv, fetchFromGithub }:
      stdenv.mkDerivation {
        name = "coq${coq.coq-version}-stdpp";

        src = fetchGit {
          url = "https://github.com/mattam82/Coq-Equations.git";
          ref = "8.14";
          rev = "841e0bc6bce3a3021b5eb13a612190428699a2ca";
        };

        postPatch = ''
          patchShebangs --build configure.sh
        '';
        configurePhase = "./configure.sh";

        buildInputs = with coq.ocamlPackages; [ ocaml camlp5 zarith findlib ];
        propagatedBuildInputs = [ coq ];
        enableParallelBuilding = true;

        installFlags = [ "COQLIB=$(out)/lib/coq/${coq.coq-version}/" ];
      } ) { } ;

  unicoq = ncoqPackages.callPackage
    ( { coq, stdenv, fetchFromGithub }:
      stdenv.mkDerivation {
        name = "coq${coq.coq-version}-unicoq";

        src = fetchGit {
          url = "https://github.com/unicoq/unicoq.git";
          ref = "master-8.14";
          rev = lib.strings.fileContents ../deps/unicoq.rev;
        };

        patches = [../deps/unicoq-meta.patch];

        configurePhase = "coq_makefile -f _CoqProject -o Makefile";

        buildInputs = with coq.ocamlPackages; [ ocaml camlp5 zarith];
        propagatedBuildInputs = [ coq coq.ocamlPackages.findlib ];
        enableParallelBuilding = true;

        installFlags = [ "COQLIB=$(out)/lib/coq/${coq.coq-version}/" ];
        installPhase = ''
          make "COQLIB=$out/lib/coq/${coq.coq-version}" install
          cp ocaml/META "$out/lib/coq/${coq.coq-version}/user-contrib/Unicoq"
        '';

        setupHook = writeText "setupHook.sh" ''
          export OCAMLPATH="''${OCAMLPATH:-""}''${OCAMLPATH:+:}''$1/lib/coq/${coq.coq-version}/user-contrib/"
        '';


      } ) { } ;

  mtac2 = ncoqPackages.callPackage
    ( { coq, stdenv, fetchFromGithub }:
      stdenv.mkDerivation {
        name = "coq${coq.coq-version}-mtac2";

        src = fetchGit {
          url = "https://github.com/Mtac2/Mtac2.git";
          ref = "master-8.14";
          rev = lib.strings.fileContents ../deps/mtac2.rev;
        };

        postPatch = ''
          patchShebangs --build configure.sh ./tests/sf5/configure.sh
        '';


        configurePhase = "mkdir -p .git/hooks; ./configure.sh";
        buildPhase = ''
          make VERBOSE=1 CAMLPKGS='-package Unicoq' real-all
        '';

        buildInputs = with coq.ocamlPackages; [ ocaml camlp5 unicoq zarith ];
        propagatedBuildInputs = [ coq unicoq ];
        enableParallelBuilding = true;

        installFlags = [ "COQLIB=$(out)/lib/coq/${coq.coq-version}/" ];
      } ) { } ;


in { inherit stdpp; coq = ncoq; inherit equations; inherit mtac2; inherit dpdgraph; }
