# Dependently typed formalisation of Kore

This subproject defines the syntax and semantics of Kore using a dependently typed, locally-nameless approach.

## Structure

- `Basics.v` provides a definition for heterogeneous lists, and defines a number of properties for it alongside with computable definitions for some standard lemmas.
- `Signature.v` defines Kore signatures. These signatures include sorts, infinitely many variables for each sort, and symbols. The argument and return sorts of these symbols are also specified in the signature. The file contains a default variable representation utilising strings.
- `Syntax.v` defines the dependently-typed syntax of Kore and notations for the syntax. The syntax is encoded in a locally-nameless style. Therefore, the type of `Pattern` is indexed by not only a sort, but also two scopes for dangling (set and element) de Bruijn indices.
- `Freshness.v` defines how fresh variables are generated (for any sort).
- `Substitution.v` defines bound (set and element) variable substitutions, and it proves some simple properties about them.
- `Semantics.v` defines dependently-typed models for Kore, and the notion of satisfiability.

