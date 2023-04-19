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

> #### Requirement 1
> **In some cases it needs to be guaranteed that the names generated for binders are different.**

### Pairwise distinct names

When generating arbitrary but different names to the binders in the previous example, we can avoid the accidental shadowing/capture ($\Longrightarrow$ denoting the pattern translation):

$$
\exists . (\bot \to \exists . 1) \qquad\Longrightarrow\qquad \exists x. (\bot \to \exists y. y)
$$

However, accidental capture can still occur if the arbitrary name we choose for the binder happens to be among the free variables of the pattern:

$$
\exists . (\bot \to \exists . x) \qquad\Longrightarrow\qquad \exists x. (\bot \to \exists y. x)
$$

Clearly, the names cannot be chosen arbitrarily.

> #### Requirement 2
> **A name generated for a binder must not clash with free names in its body nor with previously generated names for outer binders.**

This suggests that the conversion should generate *fresh* names by taking a list of names in use (including the originally free variables as well as the newly generated bound variables).

If we start the previous conversion with $x$ known to be taken, it will not be captured accidentally:

$$
\exists . (\bot \to \exists . x) \qquad\Longrightarrow\qquad \exists y. (\bot \to \exists z. x)
$$

### Translation of proofs

Ideally, the translation of proofs would be just the translation of the patterns appearing in the proof (and proving them with the corresponding named proof rules). However, for the named proofs to hold, the various copies of a single pattern must be identical; generating alpha-equivalent patterns is not sufficient for the conversion to be sound. Similar consideration applies to variable names.

For instance, suppose that we have to translate an instance of the propositional proof rule $P_1 : \phi \to \psi \to \phi$.

$$
(\exists . f \cdot 0) \to \bot \to (\exists . f \cdot 0)
$$

If the two instances of pattern $\exists . f \cdot 0$ are not given the same new variable name, the translated pattern cannot not be proved by $P_1$:

$$
(\exists x. f \cdot x) \to \bot \to (\exists y. f \cdot y)
$$

> #### Requirement 3
> **We need to ensure that the locally nameless patterns that correspond to the same metavariables in the proof rules are converted to syntactically equal patterns.**

The same requirement needs to be satisfied by the metavariables denoting names occuring multiple times in a proof rule, for example $Propagation_\exists$. For instance the following translation is wrong:

$$
(\exists . 0) \cdot (\exists . 0) \to \exists . (0 \cdot \exists . 0) \qquad\Longrightarrow\qquad
(\exists x. x) \cdot (\exists x. x) \to \exists y. (y \cdot \exists x. x)
$$

On the right-hand side of $\to$, the firtst $\exists$ should bind the same variable as in the left-hand side. Acceptable results of the conversion in this case would be:

$$
(\exists x. x) \cdot (\exists x. x) \to \exists x. (x \cdot \exists x. x) \qquad\textsf{ or}\qquad
(\exists x. x) \cdot (\exists y. y) \to \exists x. (x \cdot \exists y. y)
$$

> #### Requirement 4
> **We need to ensure that the metavariables denoting names, occuring multiple times in a proof rule a converted to identical names.**

### Substitutions

Finally, the same requirement also needs to be satisfied by substitutions, that is if there is a pattern $\phi[\psi/X]$, then all occurrences of $X$ is replaced by identical $\psi$ instances. For example the following locally nameless pattern can be proven with $Substitution$ and $Existential Quantifier$.

$$
(\exists . 0) \to \exists . (\exists . 0) \qquad === \qquad (X \to \exists . X)[\exists . 0/X]
$$

This pattern could be wrongly converted to:

$$
(\exists x. x) \to \exists x. (\exists y. y) \qquad =/= \qquad (X \to \exists y. X)[\exists x . x/X]
$$

While a correct instance would be:

$$
(\exists y. y) \to \exists x. (\exists y. y) \qquad === \qquad (X \to \exists x. X)[\exists y . y/X]
$$

Actually, we want to express a homomorphism property of the conversion w.r.t. substitutions:

$$
convertPattern(\phi[\psi/x]) = convertPattern(\phi)[convertPattern(\psi)/x]
$$

*Note that this is a requirement if we suppose that the named substitution is implemented in the standard, capture-avoiding way*.

> #### Requirement 5
> **We need to ensure that the conversion is a homomorphism w.r.t. substutition.**



We can achieve this by caching translations, by guiding the random name generation with explicit seeds, or by pre-generating the list of variable names using static analysis. We will discuss these approaches in detail down below, but they have in common that they are parametrized by a *state* that determines the translation.
(We investigated stateless/pure options too, assuming that the translation of $\phi$ only depends on $\phi$ but not on its context, but these options cannot meet the dependencies/constaints discussed above.)

## Converting implication and application: using different or identical names in the subpattern?

If we generate names based on a state, it is a decision point how this state is propagated to the conversion of subpatterns of implications and applications.

### Using the same names in subpatterns

The first option is to use the same state in both subpatterns, however, when this easily could lead us to the violation of either [Requirement 4](#requirement-4) or [Requirement 5](#requirement-5), when combined with the options to translate quantifiers below.

### Different names in subpatterns

Another option is to generate different names for the subpatterns, but in this case even [Requirement 3](#requirement-3) is violated. We refer to the example from there:

$$
(\exists . f \cdot 0) \to \bot \to (\exists . f \cdot 0) \qquad\Longrightarrow\qquad (\exists x. f \cdot x) \to \bot \to (\exists y. f \cdot y)
$$

## Converting quantifiers: Name-first or body-first?

Assume that the generation of the variable bound by an exists-quantifier can depend on the conversion of its body, an vice versa.

The question here is whether a wise order of visiting the patterns (binders) of the proof along with the right order of generating the new name and the conversion of the body can ensure the constraint on the proof translation.

### Body-first: naming the inner quantifiers first

One option is to assign names in an inside-out (bottom-up) manner. In this case, we convert the body and based on the result we invent the new quantified name.

Suppose that we generate distict, fresh variables $x, y, z$. If we assigned these names inside-out, we would violate [Requirement 4](#requirement-4) in the example discussed there.

$$
(\exists . 0) \cdot (\exists . 0) \to \exists . (0 \cdot \exists . 0) \qquad\Longrightarrow\qquad
(\exists x. x) \cdot (\exists x. x) \to \exists y. (y \cdot \exists x. x)
$$

In this case, the converted pattern does not correspond to an instance of $Propagation_\exists$ in the named proof system!

### Name-first: naming the outer quantifiers first

Another option is to invent names on the fly, while traversing the locally nameless pattern. This way, the outer quantifier first will be named. For example:

$$
(X \to \exists . X)[\exists . 0/X] \qquad===\qquad (\exists . 0) \to \exists . (\exists . 0)
$$

This pattern is provable by applying $Substitution$ and $Existential Quantifier$. However, when converting this pattern, we violate [Requirement 5](#requirement-5):

$$
(\exists x. x) \to \exists x. (\exists y. y) \qquad=/=\qquad (\exists x. x) \to \exists x. (\exists x. x) \qquad===\qquad (X \to \exists x. X)[\exists x. x/X]
$$

## More complex approaches

Based on the points discussed above, we can conclude that a more complex conversion is needed.

### Caching approach

In our first attempt, we tried to ensure that all alpha-equivalent subpatterns are identical. This is implemented as a caching translation. We use the cache to store locally-nameless (sub)patterns that we already encountered during the recursion, and map them to the named pattern they have been converted to at the first occurance. The algorithm can be described with the following pseudo-code for implication:

```
convert(phi, cache) =
  if phi is in cache then
    cache[phi]
  else
    case phi of
      ...
      imp phi1 phi2 -> let phi1' := convert(phi1, cache) in
                         let phi2' := convert(phi2, (phi1, phi1') : cache) in
                           named_imp phi1' phi2'
      ...
```

The disadvantage of this approach is its complexity. Beside a state which is needed to generate names for the binders, a cache also has to be maintained. Moreover, the conversion can be still sound, if not all alpha-equivalent subpatterns are identical.

### Name-first with custom substitutions

The second approach is to combine [Name-first](#name-first-naming-the-outer-quantifiers-first) with [Using the same names in subpatterns](#using-the-same-names-in-subpatterns). We have already discussed that this approach violates [Requirement 5](#requirement-5), if the standard definition of substitution is used. However, we can create an alternative definition, which is still capture-avoiding by always renaming all of the bound variables in a pattern based on a state.

The main disadvantage of this approach is that the named substitution is not standard (thus it is also conceptionally different from the version in the Metamath formalisation).

### Static analysis-based approach

In the third approach, the state for the conversion is a list of names which will be used for the binders. The conversion in this way is the most flexible, because not names need to be generated. Obviously, the names provided should satisfy a number of criteria to avoid violating the requirements above. For this purpose, we can analyse the locally-nameless proof first, and decide what variables can be used.

For example, by $P_1$, we can prove $(\exists . f \cdot 0) \to (\exists . \exists . (0 \to 1)) \to (\exists . f \cdot 0)$. To use this conversion, we need to provide a list of names, so that the after the conversion the two instances corresponding $(\exists . f \cdot 0)$ are identical. One option for such a list could be $[x, y, z, x]$. The result of the conversion is the following pattern: $(\exists x. f \cdot x) \to (\exists y. \exists z. z \to y) \to (\exists x. f \cdot x)$.

This list of names can be produced during proof analysis:

1. Generate as many names as quantifiers in $(\exists . f \cdot 0)$.
2. Generate as many names as quantifiers in $(\exists . \exists . (0 \to 1))$.
3. Concatenate the lists generated in steps 1, 2 and 1.

On the one hand, the major advantage of this approach is its flexibility. On the other hand, a lot of side conditions need to be carried while proving the soundness.

## Testing before verification

Before starting implementing the approaches above in Coq, we implemented them in Haskell, together with some of the requirements above. Thereafter, we utilised Haskell Quickcheck to generate random data to test the requirements for the conversion candidates. Up to now (19th April 2023) We found both [Name-first with custom substitutions](#name-first-with-custom-substitutions) and [Static analysis-based approach](#-tatic-analysis-based-approach) usable, thus we started investigating these.
