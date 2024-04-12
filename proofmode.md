# List of proof mode tactics

|  Entering, exiting the proof mode |  |
|-----------------------------------------:|------------------------------------|
| `toMLGoal`                               | Enters the proof mode.               |
| `fromMLGoal`                             | Leaves the proof mode (applies the Inherit proof rule).            |

|  Structural tactics |  |
|-----------------------------------------:|------------------------------------|
| `mlIntro "H"`                            | Moves the LHS of an implication into the local context - implication introduction.              |
| `mlRevert "H"`, `mlRevertLast`           | Moves the local hypothesis `"H"` (or the last one) into the LHS of the goal. |
| `mlClear "H"`                            | Removes a local hypothesis `"H"`. |
| `mlSwap "H" with "H0"`                   | Swaps the positions of two hypotheses. |
| `mlRename "H1" into "H2"`                | Renames a local hypothesis. |


| Propositional tactics | |
|-----------------------------------------:|------------------------------------|
| `mlDestructAnd "H" as "H1" "H2"`         | Creates two local hypotheses from one that is a conjunction - conjunction elimination. |
| `mlDestructOr "H" as "H1" "H2"`          | Creates two subgoals, one with new local hypothesis `"H1"` and the other with `"H2"`, from a goal with a disjunctive hypothesis `"H"` - disjunction elimination. |
| `mlSplitAnd`                             | Creates two subgoals from one goal that is a conjunction - conjunction introduction. |
| `mlLeft`, `mlRight`                      | Chooses a branch in a goal that is a disjunction - disjunction introduction. |
| `mlDestructBot`                          | Finishes a proof by using a false hypothesis - bottom elimination. |
| `mlExfalso`                              | Replaces the current goal with `patt_bott` (false pattern). |
| `mlClassic phi as "H1" "H2"`             | Separates cases based on the disjunction `phi or neg phi` and saves the result as local hypothesis `"H1"` or `"H2"`. |
| `mlExact "H"`                            | Finishes a proof by using the local hypothesis `"H"` which is the same as the goal. |
| `mlAssumption`                           | Finishes a proof by using some local hypothesis which is the same as the goal. |
| `mlApply "H"`                            | Applies an implication from a local hypothesis `"H"` to the goal. |
| `mlApply "H" in "H0"`                    | Applies an implication from a local hypothesis `"H"` to another hypothesis `"H0"`. |
| `mlConj "H1" "H2" as "HC"`               | Makes a conjunction of two hypotheses. |


| Meta-level propositional tactics | |
|------------------------------------------------:|------------------------------------|
| `mlExactMeta`                                   | Finishes a proof by using a global hypothesis or a lemma which is the same as the goal. |
| `mlRewrite term at n`, `mlRewrite <- term at n` | Rewrites using a global hypothesis or a lemma that is a matching logic equivalence, where `term` is fully specialized. |
| `mlApplyMeta term`                              | Applies an implication (or a chain of implications) from a lemma or a Coq hypothesis to the goal. |
| `mlApplyMeta term in "H"`                       | Applies an implication (or a chain of implications) from a lemma or a Coq hypothesis to a local hypothesis. |

| First-order tactics | |
|-----------------------------------------:|------------------------------------|
| `mlDestructEx "H" as x`                  | Uses the local hypothesis `"H"` to extract a witness `x`, where `x` already is a fresh variable - elimination of existential quantifier. |
| `mlIntroAll x`                           | Introduction of universal quantifier. |
| `mlSpecialize "H" with x`                | Specializes a local hypothesis `"H"` using a variable `x` - elimination of universal quantifier. |
| `mlExists x`                             | Uses `x` to specialize an existential goal - introduction of existential quantifier. |
| `mlRevertAll x`                          | Moves the free variable `x` back into the goal by quantifying over it. |

| Tactics for equational reasoning | |
|-----------------------------------------:|------------------------------------|
| `mlRewriteBy "H" at n`                   | Rewrites using a local hypothesis that is a matching logic equality (when working under the theory of definedness, and without restrictions on the reasoning, i.e., `AnyReasoning` is used) - elimination of equality. |
| `mlReflexivity`                          | Solves a goal of the shape `op phi phi` - for reflexive operators (e.g., `=ml`, `--->`, `<--->`). |
| `mlSymmetry`, `mlSymmetry in "H"`        | Swaps the sides of an equality. |

| Other tactics | |
|-----------------------------------------:|------------------------------------|
| `mlSimpl`, `mlSimpl in H` | Simplifies substitutions by preserving the structure of derived operators and it can be used outside of the proof mode too. Note that this tactic does not work for sorted quantification. |
| `mlSortedSimpl`, `mlSortedSimpl in H` | Simplifies substitutions by preserving the structure of derived operators for sorted quantifiers. |
| `solve_fresh` | Uses heuristics to solve freshness goals shaped as `not (elem_of (fresh_evar phi) S)` (`S` is a set of variable names). |
| `use <reasoning> in H` | Replaces the reasoning type of the Coq hypothesis `H` with `<reasoning>`, if `<reasoning>` is less restrictive than the reasoning used in `H`. |
