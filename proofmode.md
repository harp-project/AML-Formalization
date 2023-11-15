# List of proof mode tactics

|  Entering, exiting the proof mode |  |
|-----------------------------------------:|------------------------------------|
| `toMLGoal`                               | enter the proof mode               |
| `fromMLGoal`                             | leave the proof mode (applies the Inherit proof rule)             |

| Propositional tactics | |
|-----------------------------------------:|------------------------------------|
| `mlIntro "H"`                            | move the LHS of an implication into the local context - implication introduction               |
| `mlRevert "H"`, `mlRevertLast`           | move the local hypothesis `"H"` (or the last one) into the LHS of the goal |
| `mlClear "H"`                            | removes a local hypothesis `"H"` |
| `mlDestructAnd "H" as "H1" "H2"`         | create two local hypotheses from one that is a conjunction - conjunction elimination |
| `mlDestructOr "H" as "H1" "H2"`          | create two subgoals, one with new local hypothesis `"H1"` and the other with `"H2"`, from a goal with a disjunctive hypothesis "H" - disjunction elimination |
| `mlSplitAnd`                             | create two subgoals from one goal that is a conjunction - conjunction introduction |
| `mlLeft`, `mlRight`                      | choose a branch in a goal that is a disjunction - disjunction introduction |
| `mlDestructBot`                          | finish a proof by using a false hypothesis - bottom elimination |
| `mlExfalso`                              | prove that the hypotheses are inconsistent instead of the current goal |
| `mlClassic phi as "H1" "H2"`             | destruct on the disjunction `phi or neg phi` and save the result as local hypothesis "H1" or "H2"       |
| `mlExact "H"`                            | finish a proof by using the local hypothesis `"H"` which is the same as the goal |
| `mlAssumption`                           | finish a proof by using some local hypothesis which is the same as the goal |
| `mlApply "H"`                            | apply an implication from a local hypothesis `"H"` to the goal |
| `mlApply "H" in "H0"`                    | apply an implication from a local hypothesis `"H"` to another hypothesis "H0" |
| `mlRewriteBy "H" at n`                   | rewrite using a local hypothesis that is a matching logic equality (when working under the theory of definedness) - elimination of equality |
| `mlReflexivity`                          | finish proof of a conclusion of the shape `op phi phi` - for reflexive operators (e.g., `=ml`, `--->`, `<--->`) |
| `mlSymmetry`, `mlSymmetry in "H"`        | swaps the sides of an equality |
| `mlSwap "H" with "H0"`                   | swaps the positions of two hypotheses |
| `mlConj "H1" "H2" as "HC"`               | makes a conjunction of two hypotheses |
| `mlRename "H1" into "H2"`                | renames a local hypothesis |


| Meta-level propositional tactics | |
|------------------------------------------------:|------------------------------------|
| `mlExactMeta`                                   | finish a proof by using a global hypothesis or a lemma which is the same as the goal |
| `mlRewrite term at n`, `mlRewrite <- term at n` | rewrite using a global hypothesis or a lemma that is a matching logic equivalence, where `term` is fully specialized |
| `mlApplyMeta term`                              | apply an implication (or a chain of implications) from a lemma or a Coq hypothesis to the goal |
| `mlApplyMeta term in "H"`                       | apply an implication (or a chain of implications) from a lemma or a Coq hypothesis to a local hypothesis |

| First-order tactics | |
|-----------------------------------------:|------------------------------------|
| `mlDestructEx "H" as x`                  | use the local hypothesis `"H"` to extract a witness `x`, where `x` already is a fresh variable - elimination of existential quantifier |
| `mlIntroAll x`                           | specialize a universally quantified goal, where `x` already is a fresh variable - introduction of universal quantifier |
| `mlSpecialize "H" with x`                | specialize a local hypothesis `"H"` using a variable `x` - elimination of universal quantifier |
| `mlExists x`                             | use `x` to specialize an existential goal - introduction of existential quantifier |
| `mlRevertAll x`                          | moves the free variable `x` back into the goal by quantifying over it |

| Other tactics | |
|-----------------------------------------:|------------------------------------|
| `mlSimpl` | simplifies substitutions by preserving the structure of derived operators and it can be used otside of the proof mode too. |
