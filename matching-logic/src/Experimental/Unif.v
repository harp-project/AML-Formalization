From MatchingLogic.Theories Require Export FOEquality_ProofSystem.
Import MatchingLogic.Logic.Notations.
Import MatchingLogic.Theories.Definedness_Syntax.Notations.
Require Import MatchingLogic.Experimental.Unification.

Set Default Proof Mode "Classic".

Close Scope equations_scope. (* Because of [!] *)
Open Scope ml_scope.

Section Unif.
  Context {Σ : Signature} {syntax : Syntax}.
  Definition many_ex := Nat.iter ^~_^~ patt_exists.

  Definition replace_with_bound p := (set_fold (λ x '(p, n), (p^[[evar:x↦patt_bound_evar n]], S n)) (p, 0) (free_evars p)).1.

  Context (t1 t2 : Pattern).
  Hypothesis (Hwft1 : well_formed t1) (Hwft2 : well_formed t2).

  Definition unifiable t1 t2 := ⌈ many_ex (max (length (elements (free_evars t1))) (length (elements (free_evars t2)))) (replace_with_bound t1 and replace_with_bound t2) ⌉.

  Context (Γ : Theory) (T : Set) (P : T).
  Hypothesis (HΓ : theory ⊆ Γ) (UPT : UP T).
  Hypothesis (Hrtc : USrtc (singletonUP (t1 ↾ Hwft1) (t2 ↾ Hwft2)) P).
  Hypothesis (Hfin : {P' : T & unification_step P P'} -> False).

  Goal P ≠ bottomUP -> Γ ⊢ unifiable t1 t2.
  Proof.
    intros.
    unfold unifiable.
    unfold replace_with_bound.
    remember (λ x '(p, n), _) as f.
    (* pattern (free_evars t1) at 1. *)
    (* pattern (set_fold f (t1, 0) (free_evars t1)). *)
    apply set_fold_ind' with (P := λ p e, Γ ⊢ ⌈ many_ex (length (elements e) `max` length (elements (free_evars t2))) (p.1 and (set_fold f (t2, 0) (free_evars t2)).1) ⌉).
    rewrite elements_empty. simpl. shelve.
    intros. replace (elements ({[x]} ∪ X)) with (x :: elements X)%list by admit. simpl. subst f. destruct r. simpl in *.
    remember (λ x '(p, n), _) as f.
    (* pattern (set_fold f (t2, 0) (free_evars t2)). *)
    (* pattern (free_evars t2) at 1. *)
    apply set_fold_ind' with (P := λ p0 e, Γ ⊢ ⌈ many_ex (S (length (elements X)) `max` length (elements e)) (p^[[evar:x↦patt_bound_evar d]] and p0.1) ⌉).
    rewrite elements_empty. simpl. shelve.
    intros.
    replace (elements ({[x0]} ∪ X0)) with (x0 :: elements X0)%list by admit. simpl. subst f. destruct r. simpl in *.
    Search patt_defined patt_exists.
    toMLGoal. admit.
    mlFreshEvar as y.
    epose proof ceil_propagation_exists_2 Γ _ y HΓ _ _.
    use AnyReasoning in H4.
    mlApplyMeta H4. mlExists x0. mlSimpl.
