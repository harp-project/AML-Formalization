# AML-Formalization

In this project we attempt to fully implement the "Applicative Matching Logic" framework in Coq, with example intances.
The project can be used as a Coq library, in which various Matching Logic theories can be defined and reasoned about.

## For users

The project is available in the `coq-extra-dev` repository and can be installed as follows:
```sh
opam repo add coq-extra-dev https://coq.inria.fr/opam/extra-dev
opam install coq-matching-logic
```

## For developers

### Build

The easiest way to build this library is using the Nix package manager.

1. [Install Nix](https://nixos.org/download.html)
```sh
$ curl -L https://nixos.org/nix/install | sh
```

2. Run Nix shell and let Nix handle all the dependencies
```sh
$ nix-shell
```

3. Build using `make`
```sh
$ make
```

Alternatively, it is possible to build the project in Docker:
```sh
./build-in-docker.sh
```

### Structure

- `MatchingLogic.Utils` - A collection of generally usefull definitions and lemmas, independent of Matching Logic.
- `MatchingLogic.Syntax`, `MatchingLogic.Semantics`, `MatchingLogic.ProofSystem` -
  define syntax, semantics, proof system, respectively, and its properties.
  The user of the library is supposed to import these three.
- `MatchingLogic.Helpers`




## References

Official language definition http://fsl.cs.illinois.edu/index.php/Applicative_Matching_Logic

Snapshot version of the technical report, that was used for the ipmlementation can be found in doc\chen-rosu-2019-trb-public_march182020.pdf
