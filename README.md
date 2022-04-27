# AML-Formalization

In this project we attempt to fully implement the "Applicative Matching Logic" framework in Coq, with example intances.

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

We currently depend on Stdpp and Equations.

### IDE setup

If you have ProofGeneral or CoqIde installed, just run them inside the `nix-shell`.
It will detect the nix-provided coq and libraries automatically.

### Structure

- `matching-logic` library contains a locally-nameless encoding of matching logic in Coq.
- `examples` folder contain a set of examples about using the matching logic embedding.
- `prover` defines a proof of concept about extracting matching logic proofs to Metamath.


## References

Official language definition http://fsl.cs.illinois.edu/index.php/Applicative_Matching_Logic

Snapshot version of the technical report, that was used for the ipmlementation can be found in doc\chen-rosu-2019-trb-public_march182020.pdf
