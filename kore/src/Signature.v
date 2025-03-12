From Coq Require Export ssreflect ssrfun ssrbool String.
From stdpp Require Export
  base
  countable
  infinite.


Set Default Proof Mode "Classic".

Class Sorts := {
    sort : Set;
    sort_eqdec :: EqDecision sort;
    sort_countable :: Countable sort;
(*     subsort : relation sort;
    subsort_po :: PartialOrder subsort; *)
}.

Class Variables {Ss : Sorts} := {
  evar : Set;
  svar : Set;
  evar_eqdec :: EqDecision evar;
  evar_countable :: Countable evar;
  (* evar_infinite :: Infinite evar; *)
  svar_eqdec :: EqDecision svar;
  svar_countable :: Countable svar;
  (* svar_infinite :: Infinite svar; *)

  evar_sort : evar -> sort;
  svar_sort : svar -> sort;

  evar_infinite s ::
    Infinite {x : evar & decide (evar_sort x = s)};
  svar_infinite s ::
    Infinite {x : svar & decide (svar_sort x = s)}
}.

Class Symbols {Ss : Sorts} := {
  symbol : Set;
  sym_eqdec :: EqDecision symbol;
  sym_countable :: Countable symbol;
  arg_sorts : symbol -> list sort ;
  ret_sort : symbol -> sort ;
}.

Class Signature := {
  sorts :: Sorts ;
  variables :: Variables;
  symbols :: Symbols;
}.

Module StringVariables.
  Program Instance StringVariables {Ss : Sorts} : Variables := {|
    evar := sort * string;
    svar := sort * string;
    evar_sort := fun x => fst x;
    svar_sort := fun x => fst x;
  |}.
  Next Obligation.
    unshelve econstructor.
    * intro l.
      pose (map (snd ∘ projT1) l) as l_mapped.
      pose (fresh l_mapped) as new.
      apply (existT (s, new)). simpl.
      destruct decide. reflexivity. by simpl in n.
    * intros. unfold fresh.
      simpl.
      intro.
      apply (@infinite_is_fresh _ string_infinite (map (snd ∘ projT1) xs)).
      unfold fresh.
      epose proof elem_of_list_fmap_1 (snd ∘ projT1) _ _ H.
      simpl in H0. assumption.
    * unfold fresh.
      intros xs ys EQ.
      pose proof (@infinite_fresh_Permutation _ string_infinite (map (snd ∘ projT1) xs) (map (snd ∘ projT1) ys)).
      unfold fresh in H. rewrite H. 2: reflexivity.
      by apply Permutation_map.
  Defined.
  Final Obligation.
    unshelve econstructor.
    * intro l.
      pose (map (snd ∘ projT1) l) as l_mapped.
      pose (fresh l_mapped) as new.
      apply (existT (s, new)). simpl.
      destruct decide. reflexivity. by simpl in n.
    * intros. unfold fresh.
      simpl.
      intro.
      apply (@infinite_is_fresh _ string_infinite (map (snd ∘ projT1) xs)).
      unfold fresh.
      epose proof elem_of_list_fmap_1 (snd ∘ projT1) _ _ H.
      simpl in H0. assumption.
    * unfold fresh.
      intros xs ys EQ.
      pose proof (@infinite_fresh_Permutation _ string_infinite (map (snd ∘ projT1) xs) (map (snd ∘ projT1) ys)).
      unfold fresh in H. rewrite H. 2: reflexivity.
      by apply Permutation_map.
  Defined.
End StringVariables.


Ltac invt H :=
inversion H; subst; clear H.