# Converting locally-nameless proofs to named proofs

- To extract matching logic proofs to Metamath, first we need to convert proofs implemented in the locally-nameless proof system to a named proof system.
- The conversion must be **sound**:

$$
⟦\phi⟧_{LN} = ⟦convertPattern(\phi)⟧
$$

$$
p : \Gamma \vdash_{LN} \phi \quad\text{implies}\quad convertProof(p) : convertPatterns(\Gamma) \vdash convertPattern(\phi)
$$

- Disclaimer: this work is *not yet* about translation to Metamath.

## Motivating examples

In this section, we explore various options to generate names for binders and define the conversion functions above. We start with $convertPattern$.

### Names without restriction

Consider the following locally nameless pattern:

$$
\exists . (\bot \to \exists . 0)
$$

We can assign names to its binders *arbitrarily*, and obtain a correct translation:

$$
\exists x. (\bot \to \exists x. x)
$$

However, choosing names arbitrarily does not work in general. Condider the previous example slightly modified:

$$
\exists . (\bot \to \exists . \mathbf{1})
$$

When choosing names arbitrarily, we may come to the same named pattern as above, which is not a sound conversion as $x$ gets accidentally captured by the inner quantifier.

$\textcolor{green}{\textsf{In some cases it needs to be guaranteed that the names generated for binders are different.}}$

### Pairwise distinct names

When generating arbitrary but different names to the binders in the previous example, we can avoid the accidental shadowing/capture ($\Longrightarrow$ denoting the pattern translation):

$$
\exists . (\bot \to \exists . 1) \qquad\Longrightarrow\qquad \exists x. (\bot \to \exists y. y)
$$

However, accidental capture can still occur if the arbitrary name we choose for the binder happens to be among the free variables of the pattern:

$$
\exists . (\bot \to \exists . x) \qquad\Longrightarrow\qquad \exists x. (\bot \to \exists y. x)
$$

$\textcolor{green}{\textsf{Clearly, the names cannot be chosen arbitrarily. A name generated for a binder must not clash with free names in its body nor with previously generated names for outer binders.}}$

This suggests that the conversion should generate *fresh* names by taking a list of names in use (including the originally free variables as well as the newly generated bound variables).

If we start the previous conversion with $x$ known to be taken, the names generated will be $y$ and $z$, and $x$ will not be captured accidentally:

$$
\exists . (\bot \to \exists . x) \qquad\Longrightarrow\qquad \exists y. (\bot \to \exists z. x)
$$

### Translation of proofs

Ideally, the translation of proofs would be just the translation of the patterns appearing in the proof. However, for the named proofs to hold, the various copies of a single pattern must be identical; generating alpha-equivalent patterns is not sufficient for the conversion to be sound. Similar consideration applies to variable names.

For instance, suppose that we have to translate an instance of the propositional proof rule $P1 : \phi \to \psi \to \phi$.

$$
(\exists . f \cdot 0) \to \bot \to (\exists . f \cdot 0)
$$

If the two instances of pattern $\exists . f \cdot 0$ are not given the same new variable name, the translated pattern cannot not be proved by $P1$:

$$
(\exists x. f \cdot x) \to \bot \to (\exists y. f \cdot y)
$$

$\textcolor{green}{\textsf{We need to ensure that the locally nameless patterns that correspond to the same metavariables in the proof rules are converted to syntactically equal patterns.}}$

We can achieve this by caching translations, by guiding the random name generation with explicit seeds, or by pre-generating the list of variable names using static analysis. We will discuss these approaches in detail down below, but they have in common that they are parametrized by a *state* that determines the translation.
(We investigated stateless/pure options too, assuming that the translation of $\phi$ only depends on $\phi$ but not on its context, but these options cannot meet the dependencies/constaints discussed above.)

## Assuming a deterministic name generator

Assume that we can sample new variable names deterministically (the implementation of this may be based on multiple approaches discussed below).

The question here is whether a wise order of visiting the patterns (binders) of the proof can ensure the constraint on the proof translation.

### Naming the inner quantifiers first

One option is to assign names in an inside-out (bottom-up) manner. Suppose that the variables we generate are $x,y,z$. By rule $Propagation_\exists$ with $C := \Box \cdot \exists . 0$:

$$
(\exists . 0) \cdot (\exists . 0) \to \exists . (0 \cdot \exists . 0) \qquad\Longrightarrow\qquad
(\exists x. x) \cdot (\exists x. x) \to \exists y. (y \cdot \exists x. x)
$$

However, the translated pattern does not correspond to an instance of $Propagation_\exists$ in the named proof system! A correct instance would be:

$$
(\exists x. x) \cdot (\exists x. x) \to \exists x. (x \cdot \exists x. x)
$$

### Naming the outer quantifier first

NOTE: write down both stateless and stateful (function returning a state and a named pattern).

Another option is to invent names on the fly, while traversing the locally nameless pattern. This way, the outer quantifier first will be named. For example:

$$
(\exists . 0) \to \exists . (\exists . 0)
$$

This pattern is provable by applying $Substitution$ and $Existential Quantifier$. In this case, this pattern is actually the result of a substitution:

$$
(X \to \exists . X)[\exists . 0/X]
$$

$$
(\exists x. x) \to \exists x. (\exists y. y) \neq (\exists x. x) \to \exists x. (\exists x. x) = (X \to \exists x. X)[\exists x. x/X]
$$

## Approaches currently under investigation

### Caching approach

### Naming on the fly, with custom substitutions

### Static analysis-based approach

## Testing before verification

