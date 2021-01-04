CI test

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

### Dependencies:
- Coq 8.12
- stdpp (development version)
```sh
opam repo add iris-dev https://gitlab.mpi-sws.org/iris/opam.git
opam install coq-stdpp
```

The project can be built using `make`:
```sh
make
```
or using `dune`:
```sh
dune build
```
for both of which one needs to have Coq 8.12 installed.
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
