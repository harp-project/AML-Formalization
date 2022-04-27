# A Locally-Nameless Formalization of Matching logic 

This library includes an embedding of matching logic in the Coq proof system.

## Structure of the source files

All Coq source files are in the directory `src/`.
The structure is as follows:

First, we have some general utilities.
- `Utils/` - A collection of generally useful definitions and lemmas, independent of matching logic:
  - `Lattice.v` - formalization of complete lattices and Knaster-Tarski theorem.
  - `stdpp_ext.v` - an extension to the stdpp library.
  - `extralibrary.v` - generally useful lemmas and tactics

Second, we have things related to matching logic syntax.
- `Signature.v` - type classes representing matching logic signatures
- `StringSignature.v` - a particular, string-based, implementation of a signature
- `Pattern.v` - matching logic patterns and their well-formedness constraints
- `Freshness.v` - fresh variable generation and related lemmas and tactics
- `Substitution.v` - all kinds of substitutions and related lemmas
- `ApplicationContext.v` - application contexts
- `PatternContext.v` - generic, pattern-based contexts
- `SyntacticConstruct.v` - type classes for extending the syntax and defining syntactic sugar
- `NamedAxioms` a way how to give (parameterized) names to axioms of matching logic theories
- `SyntaxLemmas/` - various lemmas about syntax that require reasoning about more then one component:
  - `ApplicationCtxSubstitution.v` - lemmas combining application contexts and substitution
  - `FreshnessApplicationCtx.v` - lemmas combining application contexts and freshness
  - `FreshnessSubstitution.v` - lemmas combining freshness and substitutions
  - `PatternCtxApplicationCtx.v` - lemmas about conversion between generic pattern contexts and application contexts
- `Syntax.v` - remaining stuff about syntax
- `DerivedOperators_Syntax.v` - syntax of basic derived operators (e.g., `and`, `nu`, ...)
- `wftactics.v` - tactics for reasoning about well-formedness of patterns

Third, we have things related to matching logic semantics.
- `Semantics.v` - definitions of models and semantics
- `PrePredicate` - helper definitions and lemmas for reasoning about predicate patterns
- `monotonic.v` - a proof that well-formed patterns give rise to monotonic functions; important for `mu`
- `FixpointReasoning.v` - additional content on reasoning about the semantics of fixpoint patterns
- `ModelIsomorphism.v` - definition of model isomorphisms; proof that model isomorphism preserves the semantics of patterns


Fourth, things related to matching logic proof system.
- `ProofSystem.v` - the definition of the proof system and its basic properties
- `ProofSystemSoundness.v` - soundness of the proof system, connecting it with the semantics
- `ProofMode.v` - support for formal reasoning using the proof system

Fifth, matching logic theories.
- `theories/`
  - `Definedness_Syntax.v` - theory of definedness, totality, equality, inclusion, membership - syntax and axioms
  - `Definedness_Semantics.v` - lemmas about semantics of the above
  - `Definedness_ProofSystem.v` - proofs using the matching logic proof system about definedness and related notions
  - `Sorts_Syntax.v` - definition of syntax for sorts and many-sorted functions and related notions
  - `Sorts_Semantics.v` - the semantics of sorts, many-sorted functions, and related notions
  - `Sorts_ProofSystem.v` - proof using the matching logic proof system about sorts
  - `ModelExtension.v` - definition of the "open fragment" of matching logic; semantics of formulas from this fragment is preserved when extending the model with new elements
