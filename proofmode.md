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
| `mlAssert ("H" : phi)`                   | Creates an additional goal about the validity of `phi`, and puts `phi` as a hypothesis in the original proof state. |
| `mlTransitivity "H1" -> "H2" as "H3"`    | Composes `"H1"` and `"H2"` into a new hypothesis `"H3"`. Works with `=ml`, `--->` and `<--->`.


| Meta-level propositional tactics | |
|------------------------------------------------:|------------------------------------|
| `mlExactMeta`                                   | Finishes a proof by using a global hypothesis or a lemma which is the same as the goal. |
| `mlRewrite term at n`, `mlRewrite <- term at n` | Rewrites using a global hypothesis or a lemma that is a matching logic equivalence, where `term` is fully specialized. |
| `mlApplyMeta term`                              | Applies an implication (or a chain of implications) from a lemma or a Coq hypothesis to the goal. |
| `mlApplyMeta term in "H"`                       | Applies an implication (or a chain of implications) from a lemma or a Coq hypothesis to a local hypothesis. |
| `mlDeduct "H"`                                  | Uses the deduction theorem on hypothesis `"H"`. Note that `"H"` should be a totality pattern. |

| First-order tactics | |
|-----------------------------------------:|------------------------------------|
| `mlDestructEx "H" as x`                  | Uses the local hypothesis `"H"` to extract a witness `x`, where `x` already is a fresh variable - elimination of existential quantifier. |
| `mlDestructExManual "H" as x`            | Provides the same behaviour as the tactic above, but does not try to solve the freshness conditions automatically. |
| `mlIntroAll x`                           | Introduction of universal quantifier. |
| `mlIntroAllManual x`                     | Introduction of universal quantifier. This variant does not try to solve the freshness side conditions for `x`. |
| `mlSpecialize "H" with x`                | Specializes a local hypothesis `"H"` using a variable `x` - elimination of universal quantifier. |
| `mlExists x`                             | Uses `x` to specialize an existential goal - introduction of existential quantifier. |
| `mlRevertAll x`                          | Moves the free variable `x` back into the goal by quantifying over it. |

| Tactics for equational reasoning | |
|-----------------------------------------:|------------------------------------|
| `mlRewriteBy "H" at n`, `mlRewriteBy <- "H" at n` | Rewrites using a local hypothesis that is a matching logic equality (when working under the theory of definedness, and without restrictions on the reasoning, i.e., `AnyReasoning` is used) - elimination of equality. |
| `mlReflexivity`                          | Solves a goal of the shape `op phi phi` - for reflexive operators (e.g., `=ml`, `--->`, `<--->`). |
| `mlSymmetry`, `mlSymmetry in "H"`        | Swaps the sides of an equality. |

| Other tactics | |
|-----------------------------------------:|------------------------------------|
| `mlSimpl`, `mlSimpl in H` | Simplifies substitutions by preserving the structure of derived operators and it can be used outside of the proof mode too. Note that this tactic does not work for sorted quantification. |
| `mlSortedSimpl`, `mlSortedSimpl in H` | Simplifies substitutions by preserving the structure of derived operators for sorted quantifiers. |
| `mlFreshEvar as x`, `mlFreshSvar as X` | Creates a fresh element/set variable `x`/`X` which is different from all element/set variables in the context, and do not occur in any patterns in the context. These tactics are based on a `FreshnessManager` used to maintain fresh variables.  |
| `solve_fresh` | Uses heuristics to solve freshness goals shaped as `not (elem_of (fresh_evar phi) S)` (`S` is a set of variable names). |
| `use <reasoning> in H` | Replaces the reasoning type of the Coq hypothesis `H` with `<reasoning>`, if `<reasoning>` is less restrictive than the reasoning used in `H`. |
| `try_solve_pile` | Attempts to solve a proof constraint goal. |
| `ltac2:(fm_solve())` | Attempts to solve a freshness condition based on the `FreshnessManager` in the context. |
| `ltac2:(_fm_export_everything())` | Removes the `FreshnessManager` from the context, while explicitly generating hypotheses for all freshness conditions maintained by it. |
| `wf_auto2` | Attempts to solve any well-formedness condition. |
