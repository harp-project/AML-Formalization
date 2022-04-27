# A Coq Formalization of Matching logic 

This library contains an embedding of matching logic in the Coq proof system, using the locally-nameless representation.

[Generated html files of the latest version.](https://harp-project.github.io/AML-Formalization/toc.html)

## Structure of the source files

All Coq source files are in the directory `src/`.
The structure is as follows:

First, we have some general utilities.
- [`Utils/`](src/Utils/) - A collection of generally useful definitions and lemmas, independent of matching logic:
  - [`Lattice.v`](src/Utils/Lattice.v) - formalization of complete lattices and Knaster-Tarski theorem.
  - [`stdpp_ext.v`](src/Utils/stdpp_ext.v) - an extension to the stdpp library.
  - [`extralibrary.v`](src/Utils/extralibrary.v) - generally useful lemmas and tactics

Second, we have things related to matching logic syntax.
- [`Signature.v`](src/Signature.v) - type classes representing matching logic signatures
- [`StringSignature.v`](src/StringSignature.v) - a particular, string-based, implementation of a signature
- [`Pattern.v`](src/Pattern.v) - matching logic patterns and their well-formedness constraints
- [`Freshness.v`](src/Freshness.v) - fresh variable generation and related lemmas and tactics
- [`Substitution.v`](src/Substitution.v) - all kinds of substitutions and related lemmas
- [`ApplicationContext.v`](src/ApplicationContext.v) - application contexts (contexts consisting only of applications)
- [`PatternContext.v`](src/PatternContext.v) - generic, pattern-based contexts
- [`SyntacticConstruct.v`](src/SyntacticConstruct.v) - type classes for extending the syntax and defining syntactic sugar
- [`NamedAxioms.v`](src/NamedAxioms.v) a way how to give (parameterized) names to axioms of matching logic theories
- [`SyntaxLemmas/`](src/SyntaxLemmas/) - various lemmas about syntax that require reasoning about more then one component:
  - [`ApplicationCtxSubstitution.v`](src/SyntaxLemmas/ApplicationCtxSubstitution.v) - lemmas combining application contexts and substitution
  - [`FreshnessApplicationCtx.v`](src/SyntaxLemmas/FreshnessApplicationCtx.v) - lemmas combining application contexts and freshness
  - [`FreshnessSubstitution.v`](src/SyntaxLemmas/FreshnessSubstitution.v) - lemmas combining freshness and substitutions
  - [`PatternCtxApplicationCtx.v`](src/SyntaxLemmas/PatternCtxApplicationCtx.v) - lemmas about conversion between generic pattern contexts and application contexts
- [`Syntax.v`](src/Syntax.v) - remaining stuff about syntax
- [`DerivedOperators_Syntax.v`](src/DerivedOperators_Syntax.v) - syntax of basic derived operators (e.g., `and`, `nu`, ...)
- [`wftactics.v`](src/wftactics.v) - tactics for reasoning about well-formedness of patterns

Third, we have things related to matching logic semantics.
- [`Semantics.v`](src/Semantics.v) - definitions of models and semantics
- [`DerivedOperators_Semantics.v`](src/DerivedOperators_Semantics.v) - semantics of derived operators
- [`PrePredicate.v`](src/PrePredicate.v) - helper definitions and lemmas for reasoning about predicate patterns
- [`monotonic.v`](src/monotonic.v) - a proof that well-formed patterns give rise to monotonic functions; important for `mu`
- [`FixpointReasoning.v`](src/FixpointReasoning.v) - additional content on reasoning about the semantics of fixpoint patterns
- [`ModelIsomorphism.v`](src/ModelIsomorphism.v) - definition of model isomorphisms; proof that model isomorphism preserves the semantics of patterns

Fourth, things related to matching logic proof system.
- [`ProofSystem.v`](src/ProofSystem.v) - the definition of the proof system and its basic properties
- [`ProofSystemSoundness.v`](src/ProofSystemSoundness.v) - soundness of the proof system, connecting it with the semantics
- [`ProofMode.v`](src/ProofMode.v) - support for formal reasoning using the proof system

Fifth, matching logic theories.
- [`Theories/`](src/Theories/)
  - [`Definedness_Syntax.v`](src/Theories/Definedness_Syntax.v) - theory of definedness, totality, equality, inclusion, membership - syntax and axioms
  - [`Definedness_Semantics.v`](src/Theories/Definedness_Semantics.v) - lemmas about semantics of the above
  - [`Definedness_ProofSystem.v`](src/Theories/Definedness_ProofSystem.v) - proofs using the matching logic proof system about definedness and related notions
  - [`Sorts_Syntax.v`](src/Theories/Sorts_Syntax.v) - definition of syntax for sorts and many-sorted functions and related notions
  - [`Sorts_Semantics.v`](src/Theories/Sorts_Semantics.v) - the semantics of sorts, many-sorted functions, and related notions
  - [`Sorts_ProofSystem.v`](src/Theories/Sorts_ProofSystem.v) - proof using the matching logic proof system about sorts
  - [`ModelExtension.v`](src/Theories/ModelExtension.v) - definition of the "open fragment" of matching logic; semantics of formulas from this fragment is preserved when extending the model with new elements
