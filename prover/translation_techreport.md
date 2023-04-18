# Converting locally-nameless proofs to named proofs

- To extract matching logic proofs to Metamath, first we need to convert proofs implemented in the locally-nameless proof system to a named proof system.
- The conversion should be sound that is, if $p : \Gamma \vdash_{LN} \phi$, then $convertProof(p) : convertPatterns(\Gamma) \vdash convertPattern(\phi)$.
- Disclaimer: this work is not yet about translation to Metamath.

## Motivating examples

In this section, we explore the options to define the conversion above. We start with $convertPattern$.

### Random names

Suppose, that we have the following locally nameless pattern:

$$
\exists . \bot \to \exists . 0
$$

We could assign names to the binders randomly, and obtain:

$$
\exists x. \bot \to \exists x. x
$$

What if we modify this pattern slightly (we use $\Longrightarrow$ to denote the translation):

$$
\exists . \bot \to \exists . 1 \Longrightarrow \exists x. \bot \to \exists x. x
$$

This translation is not sound anymore, because $x$ was accidentally captured.

### Random, but pairwise different names

If we used different names during the conversion, the accidental capture above is avoided.

$$
\exists . \bot \to \exists . 1 \Longrightarrow \exists x. \bot \to \exists y. y
$$

However, accidental capture can still occur:

$$
\exists . \bot \to \exists . x \Longrightarrow \exists x. \bot \to \exists y. x
$$

Thus we can conclude that we need a state (for example, a list of names that are forbidden to use). If we start the previous conversion with $x$ being forbidden, then $x$ will not be captured accidentally:

$$
\exists . \bot \to \exists . x \Longrightarrow \exists y. \bot \to \exists z. x
$$

### 

