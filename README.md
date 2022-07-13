# AML-Formalization

In this project we attempt to fully implement the "Applicative Matching Logic" framework in Coq, with example intances.

## Documentation

- [coqdoc](https://harp-project.github.io/AML-Formalization/branch/master/coqdoc/toc.html)

## For developers

### Build

The matching logic library (in the directory `matching-logic/`) depends on:
- Coq 8.15
- stdpp 1.7
- equations 1.3

The easiest way to build the library is using the [Nix package manager](https://nixos.org/download.html),
using the [Nix Flakes](https://nixos.wiki/wiki/Flakes) feature.

#### Build using Nix Flakes

If you want to work on the matching logic library:

1. Enter a development environment for the matching logic library:
```sh
$ nix develop '.#coq-matching-logic'
```
2. Inside the `nix develop` shell, `cd` into `matching-logic/`, then run your favourite IDE (or just `make`).


Alternatively, instead of entering the development environment, one may want to
build the matching-logic library in an isolated environment:
```sh
$ nix build '.#coq-matching-logic'
```
(this is what CI does).
Note that every time you run `nix build`, it starts from the fresh environment.


If you want to work on the Metamath extractor:
```sh
nix develop '.#coq-matching-logic-mm-exporter'
```
If you want to work on examples:
```sh
nix develop '.#coq-matching-logic-example-fol'.
```
And so on. To list all packages, run:
```sh
nix flake show
```


#### If your Nix does not support Flakes:

1. Upgrade nix
```sh
$ nix upgrade-nix
```
2. [Enable Flakes](https://nixos.wiki/wiki/Flakes)


Alternatively, we provide a [flake-compat](https://github.com/edolstra/flake-compat)-based wrapper for building the matching logic library
with a 'classical' `nix`, without flakes.

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

Note that this works only for the library located in the `matching-logic/` directory.
In particular, the Metamath extractor (located in the directory `prover/`), as well as
the examples in the directory `examples/`, cannot be built this way.


### IDE setup

If you have ProofGeneral, CoqIde, or VSCoq, installed, just run them inside the `nix-shell`.
It will detect the nix-provided coq and libraries automatically.

### Structure

- `matching-logic` library contains a locally-nameless encoding of matching logic in Coq.
- `examples` folder contain a set of examples about using the matching logic embedding.
- `prover` defines a proof of concept about extracting matching logic proofs to Metamath.


## References

Official language definition http://fsl.cs.illinois.edu/index.php/Applicative_Matching_Logic

Snapshot version of the technical report, that was used for the ipmlementation can be found in `doc/chen-rosu-2019-trb-public_march182020.pdf`.
