# AML-Formalization

In this project we attempt to fully implement the "Applicative Matching Logic" framework in Coq, with example intances.
The project has two parts:
1.  A matching logic library for Coq, in which various Matching Logic theories can be defined and reasoned about.
    (see the directory `matching-logic`)
2.  An interactive prover / proof mode for matching logic, built inside Coq (see `prover`). This prover uses the matching logic library, and additionally provides some other features, like proof extraction into Metamath (WIP).



## For users

TODO lets have an example project here in this repository

## For developers

### Build

The easiest way to build the library is using the Nix package manager.

0. [Install Nix](https://nixos.org/download.html)
```sh
$ curl -L https://nixos.org/nix/install | sh
```

1. Step into the directory with the library
```sh
$ cd matching-logic
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

### IDE setup
If you have ProofGeneral or CoqIde installed, just run them inside the `nix-shell`.
It will detect the nix-provided coq and libraries automatically.

### Structure

- `MatchingLogic.Utils` - A collection of generally usefull definitions and lemmas, independent of Matching Logic.
- `MatchingLogic.Syntax`, `MatchingLogic.Semantics`, `MatchingLogic.ProofSystem` -
  define syntax, semantics, proof system, respectively, and its properties.
  The user of the library is supposed to import these three.
- `MatchingLogic.Helpers`




## References

Official language definition http://fsl.cs.illinois.edu/index.php/Applicative_Matching_Logic

Snapshot version of the technical report, that was used for the ipmlementation can be found in doc\chen-rosu-2019-trb-public_march182020.pdf
