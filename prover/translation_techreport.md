# Converting locally-nameless proofs to named proofs

- To extract matching logic proofs to Metamath, first we need to convert proofs implemented in the locally-nameless proof system to a named proof system.
- The conversion should be sound that is, if $p : \Gamma \vdash_{LN} \phi$, then $convertProof(p) : convertPatterns(\Gamma) \vdash convertPattern(\phi)$.
- Disclaimer: this work is not yet about translation to Metamath.

## Motivating examples

In this section, we explore the options to define the conversion above. We start with $convertPattern$.

### Random names

Suppose that we have the following locally nameless pattern:

$$
\exists . \bot \to \exists . 0
$$

We could assign names to the binders randomly, and obtain:

$$
\exists x. \bot \to \exists x. x
$$

What if we modify this pattern slightly (we use $\Longrightarrow$ to denote the translation):

$$
\exists . \bot \to \exists . 1 \qquad\Longrightarrow\qquad \exists x. \bot \to \exists x. x
$$

This translation is not sound anymore, because $x$ was accidentally captured.

### Random, but pairwise different names

If we used different names during the conversion, the accidental capture above is avoided.

$$
\exists . \bot \to \exists . 1 \qquad\Longrightarrow\qquad \exists x. \bot \to \exists y. y
$$

However, accidental capture can still occur:

$$
\exists . \bot \to \exists . x \qquad\Longrightarrow\qquad \exists x. \bot \to \exists y. x
$$

Thus we can conclude that we need a state (for example, a list of names that are forbidden to use). If we start the previous conversion with $x$ being forbidden, then $x$ will not be captured accidentally:

$$
\exists . \bot \to \exists . x \qquad\Longrightarrow\qquad \exists y. \bot \to \exists z. x
$$

### Translation of proofs with random names

Suppose that we have to translate an instance of the propositional proof rule $P1 : \phi \to \psi \to \phi$:

$$
(\exists . f 0) \to \bot \to (\exists . f 0)
$$

If we do this randomly, there is no assurance that both $\exists$ will be named the same way, which is a requirement by the proof rule.

$$
(\exists x. f x) \to \bot \to (\exists y. f y)
$$

The pattern above could not be proved by $P1$.

### Naming the innermost quantifier first

We need to ensure that the locally nameless pattern which correspond to the same metavariables in the proof rules are converted to syntactically equal patterns. One option is to assign names in an innermost manner. Suppose that the variables we generate are $x,y,z$. By rule $Propagation_\exists$ with $C := \Box \cdot \exists . 0$:

$$
(\exists . 0) \cdot (\exists . 0) \to \exists . 0 \cdot (\exists . 0) \qquad\Longrightarrow\qquad
(\exists x. x) \cdot (\exists x. x) \to \exists y. y \cdot (\exists x. x)
$$

However, the translated pattern does not correspond to an instance of $Propagation_\exists$ in the named proof system! A correct instance would be:

$$
(\exists x. x) \cdot (\exists x. x) \to \exists x. x \cdot (\exists x. x)
$$

### Naming on the fly, while traversing the pattern

Another option is to invent names on the fly, while traversing the locally nameless pattern. For example:

$$
(\exists . 0) \to \exists . (\exists . 0)
$$

This pattern is provable by applying $Substitution$ and $Existential Quantifier$. In this case, this pattern is actually the result of a substitution:

$$
(X \to \exists . X)[]
$$

## Approaches currently under investigation

### Caching approach

### Naming on the fly, with custom substitutions

### Static analysis-based approach

## Testing before verification

