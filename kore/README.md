# Dependently typed formalisation of Kore

This subproject defines the syntax and semantics of Kore using a dependently typed, locally-nameless approach.

## Usage instructions

This package depends on [the `matching-logic` one](../matching-logic), follow the instructions in the [main README file](../README.md) to build it. The compiled files need to be accessible while building this package, which can be achieved easiest by running `make install` after the final `make` step in those instructions. Afterwards, this package may be built by running `make` in this folder. You may choose to `make install` this package as well, if you do not wish to work in this folder. Once the setup is completed, any theories may be written and tested using a Coq IDE. See [the theories folder](src/theories) for examples.

> [!NOTE]
> The installation of the `matching-logic` package may be circumvented by adding the `-Q ../matching-logic/src MatchingLogic` flag to the top of the [Coq project file](_CoqProject). In this case, running just `make` first in the `matching-logic` directory, followed by this one is sufficient. This is not recommended.

## Structure

- `Basics.v` provides a definition for heterogeneous lists, and defines a number of properties for it alongside with computable definitions for some standard lemmas.
- `Signature.v` defines Kore signatures. These signatures include sorts, infinitely many variables for each sort, and symbols. The argument and return sorts of these symbols are also specified in the signature. The file contains a default variable representation utilising strings.
- `Syntax.v` defines the dependently-typed syntax of Kore and notations for the syntax. The syntax is encoded in a locally-nameless style. Therefore, the type of `Pattern` is indexed by not only a sort, but also two scopes for dangling (set and element) de Bruijn indices.
- `Freshness.v` defines how fresh variables are generated (for any sort).
- `Substitution.v` defines bound (set and element) variable substitutions, and it proves some simple properties about them.
- `Semantics.v` defines dependently-typed models for Kore, and the notion of satisfiability.
- `Builtins.v` defines implementations of [K's builtin, hooked symbols](https://kframework.org/k-distribution/include/kframework/builtin/domains).
- `DVParsers.v` defines custom parsers for [K's builtin types](https://kframework.org/k-distribution/include/kframework/builtin/domains), such as `Int`, `String`, `MInt`, etc. These parsers are used in the semantics of Kore to assign meaning to domain values (denoted by the `hasDomainValues` attribute in K).

The project also includes sevaral example theories, models for these theories, and satisfaction proofs in these models. These theories also serve as unit tests for the formalisation:

- `src/theories/simple/InjectionTest.v` is a simple test for injections in Kore. This file highlight an inconsistency with transitive proofs: if a value can be injected into a supertype in two different ways, then these injected values do not necessarily are equal (while this is expected accoring to the [transitivity axiom of injections](https://github.com/harp-project/AML-Formalization/blob/b1da1484bd73fd81dde4d331d5fbf64e55951d17/koreimport-test/korefiles/imp.kore#L53)).
- `src/theories/simple/InjectionTest2.v` is another simple test for injections and subsorting in Kore.
- `src/theories/simple/DVTest.v` is a test for domain values.
- `src/theories/simple/Nat.v` defines a dependently typed signature for natural numbers and bools.
- `src/theories/simple/Maps.v` defines a theory and a model for K's `Map` type, including a few selected operations. This file also includes a number of satisfaction proofs for the theory.
- `src/theories/simple/MInt.v` defines a theory and a model for K's `MInt` type, alongside with some proofs of satisfaction.
- `src/theories/complex/Demo.v` defines a demo case study (with boolean and natural number values) on how to use the infrastructure around the formalisation.
- `src/theories/complex/Imp.v` defines a partial theory for the [IMP case study](https://github.com/runtimeverification/k/blob/ea08909b72f56615ab7dfe7a6e17218b6be01de4/pyk/regression-new/pl-tutorial/1_k/2_imp/lesson_4/imp.k#L4) implemented with K, alogside with an example model and satisfaction proofs.
- `src/theories/BoolNatProductMInt.v` defines a complex theory of machine integers, natural numbers, boolean, and product values.

Furthermore, the repository also includes some generated Roqc/Coq case studies:

- `src/theories/generated/DemoGen.v` includes a simple, automatically generated theory for custom-defined bools in K, the corresponding model, and satisfaction proofs.
- `src/theories/generated/DemoGen2.v` includes a generated theory that tests injections of Kore (generated from K), the corresponding model, and satisfaction proofs.
- `src/theories/generated/tree.v` includes a portion of the Kore theory that can be generated from `tree.k` (which can be found at the same location). This file also includes an automatically generated model, and satisfaction proofs in this model.

