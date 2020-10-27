Require Import Arith.
Require Import ZArith.
Require Import List.
Require Import Coq.micromega.Lia.
Require Export String.
Require Export Coq.Lists.ListSet.
Require Export Coq.Program.Wf.

Require Import extralibrary.
(*Require Import names.*)
Require Import ML.Signature.
Require Export locally_nameless.
Require Import Lattice.

Require Export Ensembles_Ext.


Import MLNotations.

Section soundness_lemmas.

  Context {sig : Signature}.

Definition respects_blacklist (phi : Pattern) (Bp Bn : Ensemble svar_name) : Prop :=
  forall (var : svar_name),
    (Bp var -> negative_occurrence var phi) /\ (Bn var -> @positive_occurrence sig var phi).

Definition ModelPowersetLattice (M : Model) := PowersetLattice (@Domain sig M).


Lemma respects_blacklist_implies_monotonic :
  forall (phi : Pattern) (Bp Bn : Ensemble svar_name),
    respects_blacklist phi Bp Bn ->
    forall (M : Model)
           (evar_val : evar_name -> Domain M)
           (svar_val : svar_name -> Power (Domain M))
           (X : svar_name)
           (S1 S2 : Ensemble (Domain M)),
      Included (Domain M) S1 S2 ->
      (Bp X ->
       Included (Domain M)
                (@ext_valuation sig M evar_val (update_svar_val X S2 svar_val) phi)
                (@ext_valuation sig M evar_val (update_svar_val X S1 svar_val) phi)
      ) /\ (Bn X ->
            Included (Domain M)
                     (@ext_valuation sig M evar_val (update_svar_val X S1 svar_val) phi)
                     (@ext_valuation sig M evar_val (update_svar_val X S2 svar_val) phi)
         )
.
Proof.
  induction phi.
  - (* EVar *)
    intros.
    assert (HEq : ext_valuation evar_val (update_svar_val X S2 svar_val) (patt_free_evar x)
                  = ext_valuation evar_val (update_svar_val X S1 svar_val) (patt_free_evar x)).
    { rewrite -> ext_valuation_free_evar_simpl. rewrite -> ext_valuation_free_evar_simpl. reflexivity. }
    rewrite -> HEq.
    split; intros; unfold Included; intros; assumption.
  - (* SVar *)
    intros. split; intros.
    * repeat rewrite -> ext_valuation_free_svar_simpl.
      assert (X <> x).
      { unfold respects_blacklist in H.
        specialize H with (var := X). destruct H.
        apply H in H1. inversion H1.
      }
      unfold update_svar_val.
      destruct (eq_svar_name X x). contradiction.
      unfold Included. auto.
    
Admitted.


(*
Lemma is_monotonic :
  forall (sm : Sigma_model)
         (evar_val : name -> M sm)
         (svar_val : db_index -> Power (M sm)) (phi : Sigma_pattern)
         (x : db_index),
    positive x phi ->
    well_formed phi ->
    forall (l r : Power (M sm)),
      Included (M sm) l r ->
      Included (M sm)
        (ext_valuation evar_val (change_val beq_nat 0 l db_val) phi)
        (ext_valuation freevar_val (change_val beq_nat 0 r db_val) phi).
Proof.
Admitted.
*)
(* if ext_valuation (phi1 --> phi2) = Full_set 
   then ext_valuation phi1 subset ext_valuation phi2
*)
Theorem ext_valuation_implies_subset {m : Model}
        (evar_val : evar_name -> Domain m) (svar_val : svar_name -> Power (Domain m))
        (phi1 : Pattern) (phi2 : Pattern) :
  Same_set (Domain m) (ext_valuation evar_val svar_val (phi1 --> phi2)) (Full_set (Domain m)) ->
  Included (Domain m) (ext_valuation evar_val svar_val phi1)
           (@ext_valuation sig m evar_val svar_val phi2).
Proof.
  intros; unfold Included; intros.
  rewrite ext_valuation_imp_simpl in H.
  remember (ext_valuation evar_val svar_val phi1) as Xphi1.
  remember (ext_valuation evar_val svar_val phi2) as Xphi2.
  assert (In (Domain m) (Union (Domain m) (Complement (Domain m) Xphi1) Xphi2) x).
  apply Same_set_to_eq in H. rewrite H. constructor.
  inversion H1. contradiction. assumption.
Qed.

(* evar_open of fresh name does not change *)
Lemma evar_open_fresh (phi : Pattern) :
  forall n, well_formed phi -> evar_open n (evar_fresh (variables sig) (free_evars phi)) phi = phi.
Proof. Admitted. (*
  intros. generalize dependent n. induction phi; intros; simpl; try eauto.
  * inversion H. inversion H1.
  *  rewrite IHphi1. rewrite IHphi2. reflexivity.
    split; inversion H. inversion H0; assumption. inversion H1; assumption.
    split; inversion H. inversion H0; assumption. inversion H1; assumption.
  * rewrite IHphi1. rewrite IHphi2. reflexivity.
    split; inversion H. inversion H0; assumption. inversion H1; assumption.
    split; inversion H. inversion H0; assumption. inversion H1; assumption.
  * rewrite IHphi. reflexivity.
    split; inversion H. assumption.
    unfold well_formed_closed in *. simpl in H1. admit.
Admitted.*)

(* update_valuation with fresh name does not change *)
(* TODO(jan.tusil): I think that we need to generalize this
   to work with any variable that is not free in psi.
*)
Lemma update_valuation_fresh {m : Model}
      (evar_val : evar_name -> Domain m) (svar_val : svar_name -> Power (Domain m))
      (psi : Pattern) (x : Domain m) (c : Domain m) :
  ext_valuation (update_valuation evar_name_eqb (evar_fresh (variables sig) (free_evars psi)) c evar_val) svar_val psi x
  = ext_valuation evar_val svar_val psi x.
Proof.
Admitted.

(* ext_valuation with free_svar_subst does not change *)
Lemma update_valuation_free_svar_subst {m : Model}
      (evar_val : evar_name -> Domain m) (svar_val : svar_name -> Power (Domain m))
      (phi : Pattern) (psi : Pattern) (X : svar_name) :
  ext_valuation evar_val svar_val phi
  = ext_valuation evar_val svar_val (@free_svar_subst sig phi psi X) .
Proof.
Admitted.

End soundness_lemmas.
