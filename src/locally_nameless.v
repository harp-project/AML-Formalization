Require Import Arith.
Require Import ZArith.
Require Import List.
Require Import extralibrary.

Require Import Coq.micromega.Lia.

(*From Equations Require Import Equations.*)
Require Export String.
Require Export Ensembles_Ext.

Require Export Coq.Program.Wf.
Require Import Coq.Logic.FunctionalExtensionality.
From Coq Require Import ssreflect ssrfun ssrbool.
From stdpp Require Import pmap gmap mapset fin_sets.

Require Import Lattice.
Require Import stdpp_ext.

Require Import MatchingLogic.Syntax.

(** ** Matching Logic Semantics *)
Section semantics.
  
    Context {signature : Signature}.
    Existing Instance variables.


(* Model of AML ref. snapshot: Definition 2 *)

Record Model := {
  Domain : Type;
  (* TODO think about whether or not to make it an existential formula. Because that would affect the equality,
     due to proof irrelevance. *)
  nonempty_witness : Domain;
  Domain_eq_dec : forall (a b : Domain), {a = b} + {a <> b};
  app_interp : Domain -> Domain -> Power Domain;
  sym_interp (sigma : symbols) : Power Domain;
}.

Lemma empty_impl_not_full : forall {M : Model} (S : Power (Domain M)),
    Same_set (Domain M) S (Empty_set (Domain M)) ->
    ~ Same_set (Domain M) S (Full_set (Domain M)).
Proof.
  unfold Same_set. unfold Included. unfold not. intros.
  assert (Hexin : Ensembles.In (Domain M) (Full_set (Domain M)) (nonempty_witness M)).
  { unfold In. constructor. }
  firstorder.
Qed.

Lemma full_impl_not_empty : forall {M : Model} (S : Power (Domain M)),
    Same_set (Domain M) S (Full_set (Domain M)) ->
    ~ Same_set (Domain M) S (Empty_set (Domain M)).
Proof.
  unfold Same_set. unfold Included. unfold not. intros.
  assert (Hexin : Ensembles.In (Domain M) (Full_set (Domain M)) (nonempty_witness M)).
  { unfold In. constructor. }
  firstorder.
Qed.

Definition EVarVal {m : Model} : Type := evar -> Domain m.
Definition SVarVal {m : Model} : Type := svar -> Power (Domain m).

Definition update_evar_val {m : Model} 
           (v : evar) (x : Domain m) (evar_val : @EVarVal m) : EVarVal :=
  fun v' : evar => if evar_eq v v' then x else evar_val v'.

Definition update_svar_val {m : Model}
           (v : svar) (X : Power (Domain m)) (svar_val : @SVarVal m)  : SVarVal :=
  fun v' : svar => if svar_eq v v' then X else svar_val v'.

Lemma update_svar_val_comm M :
  forall (X1 X2 : svar) (S1 S2 : Power (Domain M)) (svar_val : @SVarVal M),
    X1 <> X2 ->
    update_svar_val X1 S1 (update_svar_val X2 S2 svar_val)
    = update_svar_val X2 S2 (update_svar_val X1 S1 svar_val).
Proof.
  intros.
  unfold update_svar_val.
  apply functional_extensionality.
  intros.
  destruct (svar_eq X1 x),(svar_eq X2 x); subst.
  * unfold not in H. assert (x = x). reflexivity. apply H in H0. destruct H0.
  * reflexivity.
  * reflexivity.
  * reflexivity.
Qed.

Lemma update_svar_val_shadow M : forall (X : svar)
                                  (S1 S2 : Power (Domain M))
                                  (svar_val : @SVarVal M),
    update_svar_val X S1 (update_svar_val X S2 svar_val) = update_svar_val X S1 svar_val.
Proof.
  intros. unfold update_svar_val. apply functional_extensionality.
  intros. destruct (svar_eq X x); reflexivity.
Qed.


Lemma update_evar_val_comm M :
  forall (x1 x2 : evar) (m1 m2 : Domain M) (evar_val : @EVarVal M),
    x1 <> x2 ->
    update_evar_val x1 m1 (update_evar_val x2 m2 evar_val)
    = update_evar_val x2 m2 (update_evar_val x1 m1 evar_val).
Proof.
  intros.
  unfold update_evar_val.
  apply functional_extensionality.
  intros.
  destruct (evar_eq x1 x),(evar_eq x2 x); subst.
  * unfold not in H. assert (x = x). reflexivity. apply H in H0. destruct H0.
  * reflexivity.
  * reflexivity.
  * reflexivity.
Qed.

Lemma update_evar_val_shadow M : forall (x : evar)
                                  (m1 m2 : Domain M)
                                  (evar_val : @EVarVal M),
    update_evar_val x m1 (update_evar_val x m2 evar_val) = update_evar_val x m1 evar_val.
Proof.
  intros. unfold update_evar_val. apply functional_extensionality.
  intros. destruct (evar_eq x x0); reflexivity.
Qed.

Lemma update_evar_val_same M x m ρₑ : @update_evar_val M x m ρₑ x = m.
Proof.
  unfold update_evar_val. destruct (evar_eq x x); simpl.
  + reflexivity.
  + contradiction.
Qed.


Definition app_ext {m : Model}
           (l r : Power (Domain m)) :
  Power (Domain m) :=
fun e:Domain m => exists le re:Domain m, l le /\ r re /\ (app_interp m) le re e.

(* TODO move to examples in a different module *)
(*
Compute @app_ext {| Domain := Pattern |}
        (Singleton _ (evar "a")) (Singleton _ (evar "b")).
*)
(* S . empty = empty *)

Lemma app_ext_bot_r : forall (m : Model),
    forall S : Power (Domain m),
  Same_set (Domain m) (app_ext S (Empty_set (Domain m))) (Empty_set (Domain m)).
Proof.
  intros. unfold app_ext. unfold Same_set. unfold Included. unfold In. split; intros.
  * inversion H. inversion H0. inversion H1. inversion H3. contradiction.
  * contradiction.
Qed.

Lemma app_ext_bot_l : forall (m : Model),
    forall S : Power (Domain m),
  Same_set (Domain m) (app_ext (Empty_set (Domain m)) S) (Empty_set (Domain m)).
Proof.
  intros. unfold app_ext. unfold Same_set. unfold Included. unfold In. split; intros.
  * inversion H. inversion H0. inversion H1. contradiction.
  * contradiction.
Qed.

Lemma app_ext_monotonic_l : forall (m : Model),
    forall (S1 S2 S : Power (Domain m)),
      Included (Domain m) S1 S2 ->
      Included (Domain m) (app_ext S1 S) (app_ext S2 S).
Proof.
  intros. unfold app_ext. unfold Included. unfold Included in H.
  intros. unfold In in *. destruct H0 as [le [re [H1 [H2 H3]]]].
  apply H in H1. exists le. exists re. firstorder.
Qed.

Lemma app_ext_monotonic_r : forall (m : Model),
    forall (S S1 S2 : Power (Domain m)),
      Included (Domain m) S1 S2 ->
      Included (Domain m) (app_ext S S1) (app_ext S S2).
Proof.
  intros. unfold app_ext. unfold Included. unfold Included in H.
  intros. unfold In in *. destruct H0 as [le [re [H1 [H2 H3]]]].
  apply H in H2. exists le. exists re. firstorder.
Qed.

(* Semantics of AML ref. snapshot: Definition 3 *)



(*
Definition pattern_lt (p1 p2 : Pattern) :=
  size p1 < size p2.
Lemma pattern_lt_well_founded : well_founded (@pattern_lt).
Proof.
  apply well_founded_lt_compat with size; auto.
Qed.

Instance wf_pattern_lt : WellFounded (@pattern_lt).
apply pattern_lt_well_founded.
Defined.

Equations pattern_interpretation_aux {m : Model}
          (evar_val : evar -> Domain m) (svar_val : svar -> Power (Domain m))
          (p : Pattern) : Power (Domain m)
  by wf (size p) :=
  pattern_interpretation_aux evar_val svar_val (patt_free_evar x) := Singleton _ (evar_val x);
  pattern_interpretation_aux evar_val svar_val (patt_free_svar X) := svar_val X;
  pattern_interpretation_aux evar_val svar_val (patt_bound_evar x) := Empty_set _;
  pattern_interpretation_aux evar_val svar_val (patt_bound_svar x) := Empty_set _;
  pattern_interpretation_aux evar_val svar_val (patt_sym s) := (sym_interp m) s;
  pattern_interpretation_aux evar_val svar_val (patt_app ls rs) :=
    app_ext (pattern_interpretation_aux evar_val svar_val ls)
                  (pattern_interpretation_aux evar_val svar_val rs);
  pattern_interpretation_aux evar_val svar_val patt_bott := Empty_set _;
  pattern_interpretation_aux evar_val svar_val (patt_imp ls rs) :=
    Union _ (Complement _ (pattern_interpretation_aux evar_val svar_val ls))
            (pattern_interpretation_aux evar_val svar_val rs);
  pattern_interpretation_aux evar_val svar_val (patt_exists p') :=
    let x := evar_fresh variables (free_evars p') in
    FA_Union
      (fun e => pattern_interpretation_aux (update_evar_val x e evar_val) svar_val
                                  (evar_open 0 x p'));
  pattern_interpretation_aux evar_val svar_val (patt_mu p') :=
    let X := svar_fresh variables (free_svars p') in
    Ensembles_Ext.mu
      (fun S => pattern_interpretation_aux evar_val (update_svar_val X S svar_val)
                                  (svar_open 0 X p')).
Next Obligation. unfold pattern_lt. simpl. lia. Defined.
Next Obligation. unfold pattern_lt. simpl. lia. Defined.
Next Obligation. unfold pattern_lt. simpl. lia. Defined.
Next Obligation. unfold pattern_lt. simpl. lia. Defined.
Next Obligation. unfold pattern_lt. simpl. rewrite <- evar_open_size. lia. apply signature. Defined.
Next Obligation. unfold pattern_lt. simpl. rewrite <- svar_open_size. lia. apply signature. Defined.
*)

Section semantics.

  Context {m : Model}.
  Let OS := EnsembleOrderedSet (@Domain m).
  Let  L := PowersetLattice (@Domain m).

Program Fixpoint pattern_interpretation
        (evar_val : evar -> Domain m) (svar_val : svar -> Power (Domain m))
        (p : Pattern) {measure (size p)} :=
match p with
| patt_free_evar x => Ensembles.Singleton _ (evar_val x)
| patt_free_svar X => svar_val X
| patt_bound_evar x => Empty_set _
| patt_bound_svar X => Empty_set _
| patt_sym s => (sym_interp m) s
| patt_app ls rs => app_ext (pattern_interpretation evar_val svar_val ls)
                                  (pattern_interpretation evar_val svar_val rs)
| patt_bott => Empty_set _
| patt_imp ls rs => Ensembles.Union _ (Complement _ (pattern_interpretation evar_val svar_val ls))
                            (pattern_interpretation evar_val svar_val rs)
| patt_exists p' =>
  let x := fresh_evar p' in
  FA_Union
    (fun e => pattern_interpretation (update_evar_val x e evar_val)
                            svar_val
                            (evar_open 0 x p'))
| patt_mu p' =>
  let X := fresh_svar p' in
  @LeastFixpointOf (Ensemble (@Domain m)) OS L
    (fun S => pattern_interpretation evar_val
                            (update_svar_val X S svar_val)
                            (svar_open 0 X p'))
end.
Next Obligation. intros. subst. simpl; lia. Defined.
Next Obligation. intros. subst. simpl; lia. Defined.
Next Obligation. intros. subst. simpl; lia. Defined.
Next Obligation. intros. subst. simpl; lia. Defined.
Next Obligation. intros. subst. simpl; rewrite <- evar_open_size. lia. apply signature. Defined.
Next Obligation. intros. subst. simpl; rewrite <- svar_open_size. lia. apply signature. Defined.
Next Obligation. Tactics.program_simpl. Defined.

(* TODO: Need to be able to simplify Program Fixpoint definitions *)

Lemma pattern_interpretation_free_evar_simpl
      (evar_val : evar -> Domain m) (svar_val : svar -> Power (Domain m))
      (x : evar) :
  pattern_interpretation evar_val svar_val (patt_free_evar x) = Ensembles.Singleton _ (evar_val x).
Admitted.

Lemma pattern_interpretation_free_svar_simpl
      (evar_val : evar -> Domain m) (svar_val : svar -> Power (Domain m))
      (X : svar) :
  pattern_interpretation evar_val svar_val (patt_free_svar X) = svar_val X.
Admitted.

Lemma pattern_interpretation_bound_evar_simpl
      (evar_val : evar -> Domain m) (svar_val : svar -> Power (Domain m))
      (x : db_index) :
  pattern_interpretation evar_val svar_val (patt_bound_evar x) = Empty_set _ .
Admitted.

Lemma pattern_interpretation_bound_svar_simpl
      (evar_val : evar -> Domain m) (svar_val : svar -> Power (Domain m))
      (X : db_index) :
  pattern_interpretation evar_val svar_val (patt_bound_svar X) = Empty_set _ .
Admitted.

Lemma pattern_interpretation_sym_simpl
      (evar_val : @EVarVal m) (svar_val : @SVarVal m)
      (s : symbols) :
  pattern_interpretation evar_val svar_val (patt_sym s) = sym_interp m s.
Proof.

Admitted.


Lemma pattern_interpretation_app_simpl
      (evar_val : evar -> Domain m) (svar_val : svar -> Power (Domain m))
      (ls rs : Pattern) :
  pattern_interpretation evar_val svar_val (patt_app ls rs) =
  app_ext (pattern_interpretation evar_val svar_val ls)
                (pattern_interpretation evar_val svar_val rs).
Admitted.

Lemma pattern_interpretation_bott_simpl
      (evar_val : evar -> Domain m) (svar_val : svar -> Power (Domain m)) :
  pattern_interpretation evar_val svar_val patt_bott = Empty_set _ .
Admitted.

Lemma pattern_interpretation_imp_simpl
      (evar_val : evar -> Domain m) (svar_val : svar -> Power (Domain m))
      (ls rs : Pattern) :
  pattern_interpretation evar_val svar_val (patt_imp ls rs) =
  Ensembles.Union _ (Complement _ (pattern_interpretation evar_val svar_val ls))
          (pattern_interpretation evar_val svar_val rs).
Admitted.

Lemma pattern_interpretation_ex_simpl
      (evar_val : evar -> Domain m) (svar_val : svar -> Power (Domain m))
      (p : Pattern) :
  pattern_interpretation evar_val svar_val (patt_exists p) =
  let x := fresh_evar p in
  FA_Union 
    (fun e => pattern_interpretation (update_evar_val x e evar_val)
                            svar_val
                            (evar_open 0 x p)).
Admitted.

Lemma pattern_interpretation_mu_simpl
      (evar_val : evar -> Domain m) (svar_val : svar -> Power (Domain m))
      (p : Pattern) :
  pattern_interpretation evar_val svar_val (patt_mu p) =
  let X := fresh_svar p in
  @LeastFixpointOf (Ensemble (@Domain m)) OS L
    (fun S => pattern_interpretation evar_val
                            (update_svar_val X S svar_val)
                            (svar_open 0 X p)).
Admitted.

(*
Ltac proof_ext_val :=
simpl;intros;
repeat
  (* Normalize *)
   rewrite (Same_set_to_eq (Union_Empty_l _))
|| rewrite (Same_set_to_eq (Compl_Compl_Powers _ _))
|| rewrite
   (Same_set_to_eq (Compl_Union_Compl_Intes_Powers_alt _ _ _))
|| rewrite (Same_set_to_eq (FA_rel _ _ _))
  (* Apply *)
|| (eapply (proj1 Same_set_Compl) ; intros)
|| (eapply FA_Inters_same ; intros)
  (* Final step *)
|| exact Complement_Empty_is_Full
|| exact (Symdiff_val _ _)
|| exact (Same_set_refl _).
 *)

End semantics.

(**
   Proof of correct semantics for the derived operators
   ref. snapshot: Proposition 4
*)

(* Theory,axiom ref. snapshot: Definition 5 *)

Definition Theory := Power Pattern.

Definition satisfies_model (m : Model) (phi : Pattern) : Prop :=
forall (evar_val : evar -> Domain m) (svar_val : svar -> Power (Domain m)),
  Same_set _ (pattern_interpretation (m := m) evar_val svar_val phi) (Full_set _).

Definition satisfies_theory (m : Model) (theory : Theory)
: Prop := forall axiom : Pattern, Ensembles.In _ theory axiom -> (satisfies_model m axiom).

(* TODO rename *)
Definition satisfies (theory : Theory) (p: Pattern)
: Prop := forall m : Model, (satisfies_theory m theory) -> (satisfies_model m p).

(* End of definition 5. *)

Inductive Application_context : Type :=
| box
| ctx_app_l (cc : Application_context) (p : Pattern) (Prf : well_formed p)
| ctx_app_r (p : Pattern) (cc : Application_context) (Prf : well_formed p)
.

Fixpoint subst_ctx (C : Application_context) (p : Pattern)
  : Pattern :=
match C with
| box => p
| ctx_app_l C' p' prf => patt_app (subst_ctx C' p) p'
| ctx_app_r p' C' prf => patt_app p' (subst_ctx C' p)
end.

Fixpoint free_evars_ctx (C : Application_context)
  : (EVarSet) :=
match C with
| box => empty
| ctx_app_l cc p prf => union (free_evars_ctx cc) (free_evars p)
| ctx_app_r p cc prf => union (free_evars p) (free_evars_ctx cc)
end.

Lemma pattern_interpretation_not_simpl : forall {m : Model} (evar_val : @EVarVal m) (svar_val : @SVarVal m)(phi : Pattern),
    pattern_interpretation evar_val svar_val (patt_not phi) = Complement (Domain m) (pattern_interpretation evar_val svar_val phi).
Proof.
  intros. unfold patt_not.
  rewrite -> pattern_interpretation_imp_simpl.
  rewrite -> pattern_interpretation_bott_simpl.
  apply Extensionality_Ensembles.
  apply Union_Empty_l.
Qed.

Lemma pattern_interpretation_or_simpl : forall {m : Model} (evar_val : @EVarVal m) (svar_val : @SVarVal m)
                                      (phi1 phi2 : Pattern),
    pattern_interpretation evar_val svar_val (patt_or phi1 phi2)
    = Ensembles.Union (Domain m) (pattern_interpretation evar_val svar_val phi1) (pattern_interpretation evar_val svar_val phi2).
Proof.
  intros. unfold patt_or.
  rewrite -> pattern_interpretation_imp_simpl.
  rewrite -> pattern_interpretation_not_simpl.
  assert (H: Complement (Domain m) (Complement (Domain m) (pattern_interpretation evar_val svar_val phi1)) = pattern_interpretation evar_val svar_val phi1).
  { apply Extensionality_Ensembles. apply Compl_Compl_Ensembles. }
  rewrite -> H. reflexivity.
Qed.

Lemma pattern_interpretation_or_comm : forall {m : Model} (evar_val : @EVarVal m) (svar_val : @SVarVal m)
                                     (phi1 phi2 : Pattern),
    pattern_interpretation evar_val svar_val (patt_or phi1 phi2)
    = pattern_interpretation evar_val svar_val (patt_or phi2 phi1).
Proof.
  intros.
  repeat rewrite -> pattern_interpretation_or_simpl.
  apply Extensionality_Ensembles.
  apply Union_Symmetric.
Qed.

Lemma pattern_interpretation_and_simpl : forall {m : Model} (evar_val : @EVarVal m) (svar_val : @SVarVal m)
                                       (phi1 phi2 : Pattern),
    pattern_interpretation evar_val svar_val (patt_and phi1 phi2)
    = Ensembles.Intersection (Domain m) (pattern_interpretation evar_val svar_val phi1) (pattern_interpretation evar_val svar_val phi2).
Proof.
  intros. unfold patt_and.
  rewrite -> pattern_interpretation_not_simpl.
  rewrite -> pattern_interpretation_or_simpl.
  repeat rewrite -> pattern_interpretation_not_simpl.
  apply Extensionality_Ensembles.
  apply Compl_Union_Compl_Intes_Ensembles_alt.
Qed.

Lemma pattern_interpretation_and_comm : forall {m : Model} (evar_val : @EVarVal m) (svar_val : @SVarVal m)
                                     (phi1 phi2 : Pattern),
    pattern_interpretation evar_val svar_val (patt_and phi1 phi2)
    = pattern_interpretation evar_val svar_val (patt_and phi2 phi1).
Proof.
  intros.
  repeat rewrite -> pattern_interpretation_and_simpl.
  apply Extensionality_Ensembles.
  apply Intersection_Symmetric.
Qed.

Lemma pattern_interpretation_top_simpl : forall {m : Model} (evar_val : @EVarVal m) (svar_val : @SVarVal m),
    pattern_interpretation evar_val svar_val patt_top = Full_set (Domain m).
Proof.
  intros. unfold patt_top.
  rewrite -> pattern_interpretation_not_simpl.
  rewrite -> pattern_interpretation_bott_simpl.
  apply Extensionality_Ensembles.
  apply Complement_Empty_is_Full.
Qed.

(* TODO prove. Maybe some de-morgan laws could be helpful in proving this? *)
Lemma pattern_interpretation_iff_or : forall {m : Model} (evar_val : @EVarVal m) (svar_val : @SVarVal m)
                                     (phi1 phi2 : Pattern),
    pattern_interpretation evar_val svar_val (patt_iff phi1 phi2)
    = pattern_interpretation evar_val svar_val (patt_or (patt_and phi1 phi2) (patt_and (patt_not phi1) (patt_not phi2))).
Proof.

Admitted.

Lemma pattern_interpretation_iff_comm : forall {m : Model} (evar_val : @EVarVal m) (svar_val : @SVarVal m)
                                      (phi1 phi2 : Pattern),
    pattern_interpretation evar_val svar_val (patt_iff phi1 phi2)
    = pattern_interpretation evar_val svar_val (patt_iff phi2 phi1).
Proof.
  intros.
  unfold patt_iff.
  rewrite -> pattern_interpretation_and_comm.
  reflexivity.
Qed.

(* TODO: forall, nu *)

(* TODO prove *)
(*
Lemma pattern_interpretation_fa_simpl : forall {m : Model} (evar_val : @EVarVal m) (svar_val : @SVarVal m) (phi : Pattern),
    pattern_interpretation evar_val svar_val (patt_forall phi) =
    let x := evar_fresh (free_evars phi) in
    FA_Intersection (fun e : @Domain m => pattern_interpretation (update_evar_val x e evar_val) svar_val (evar_open 0 x phi) ).
Proof.
  intros.
  unfold patt_forall.
  rewrite -> pattern_interpretation_not_simpl.
  rewrite -> pattern_interpretation_ex_simpl.
  simpl.
  apply Extensionality_Ensembles.
  unfold Same_set. unfold Complement. unfold Included. unfold In.
  split; intros.
Admitted.
 *)

Lemma evar_open_not k x ϕ : evar_open k x (patt_not ϕ) = patt_not (evar_open k x ϕ).
Proof.
  simpl. unfold patt_not. reflexivity.
Qed.

Lemma evar_open_or k x ϕ₁ ϕ₂ : evar_open k x (patt_or ϕ₁ ϕ₂) = patt_or (evar_open k x ϕ₁) (evar_open k x ϕ₂).
Proof.
  simpl. unfold patt_or. unfold patt_not. reflexivity.
Qed.

Lemma evar_open_and k x ϕ₁ ϕ₂ : evar_open k x (patt_and ϕ₁ ϕ₂) = patt_and (evar_open k x ϕ₁) (evar_open k x ϕ₂).
Proof.
  simpl. unfold patt_and. unfold patt_not. reflexivity.
Qed.

Definition M_predicate (M : Model) (ϕ : Pattern) : Prop := forall ρₑ ρₛ,
    Same_set (Domain M) (pattern_interpretation ρₑ ρₛ ϕ) (Full_set (Domain M))
    \/ Same_set (Domain M) (pattern_interpretation ρₑ ρₛ ϕ) (Empty_set (Domain M)).


Lemma M_predicate_impl M ϕ₁ ϕ₂ : M_predicate M ϕ₁ -> M_predicate M ϕ₂ -> M_predicate M (patt_imp ϕ₁ ϕ₂).
Proof.
  unfold M_predicate. intros Hp1 Hp2 ρₑ ρₛ.
  specialize (Hp1 ρₑ ρₛ). specialize (Hp2 ρₑ ρₛ).
  rewrite -> pattern_interpretation_imp_simpl.
  destruct Hp1, Hp2; apply Same_set_to_eq in H; apply Same_set_to_eq in H0; rewrite -> H; rewrite -> H0.
  + left. apply Union_Compl_Fullset.
  + right.
    rewrite -> (Same_set_to_eq (Complement_Full_is_Empty)).
    apply Union_Empty_r.
  + left.
    rewrite -> (Same_set_to_eq (Complement_Empty_is_Full)).
    unfold Same_set. unfold Included. unfold In. split; intros; constructor; constructor.
  + left. apply Union_Compl_Fullset.
Qed.

Lemma M_predicate_bott M : M_predicate M patt_bott.
Proof.
  unfold M_predicate. intros. right.
  rewrite -> pattern_interpretation_bott_simpl.
  apply Same_set_refl.
Qed.

Lemma M_predicate_not M ϕ : M_predicate M ϕ -> M_predicate M (patt_not ϕ).
Proof.
  intros. unfold patt_not. auto using M_predicate_impl, M_predicate_bott.
Qed.

Lemma M_predicate_or M ϕ₁ ϕ₂ : M_predicate M ϕ₁ -> M_predicate M ϕ₂ -> M_predicate M (patt_or ϕ₁ ϕ₂).
Proof.
  intros. unfold patt_or. auto using M_predicate_not, M_predicate_impl.
Qed.

Lemma M_predicate_and M ϕ₁ ϕ₂ : M_predicate M ϕ₁ -> M_predicate M ϕ₂ -> M_predicate M (patt_and ϕ₁ ϕ₂).
Proof.
  intros. unfold patt_and. auto using M_predicate_or, M_predicate_not.
Qed.


Lemma M_predicate_exists M ϕ :
  let x := evar_fresh (elements (free_evars ϕ)) in
  M_predicate M (evar_open 0 x ϕ) -> M_predicate M (patt_exists ϕ).
Proof.
  simpl. unfold M_predicate. intros.
  rewrite -> pattern_interpretation_ex_simpl.
  simpl.
  pose proof (H' := classic (exists e : Domain M, Same_set (Domain M) (pattern_interpretation (update_evar_val (evar_fresh (elements (free_evars ϕ))) e ρₑ) ρₛ (evar_open 0 (evar_fresh (elements (free_evars ϕ))) ϕ)) (Full_set (Domain M)))).
  destruct H'.
  - (* For some member, the subformula evaluates to full set. *)
    left. apply Same_set_symmetric. apply Same_set_Full_set.
    unfold Included. intros. constructor.
    destruct H0. unfold Same_set in H0. destruct H0. clear H0.
    unfold Included in H2. specialize (H2 x H1).
    exists x0. unfold In in H2. apply H2.
  - (* The subformula does not evaluate to full set for any member. *)
    right.
    unfold Same_set.
    split.
    + unfold Included. intros.
      unfold In in H1. inversion H1. subst. clear H1. destruct H2.
      specialize (H (update_evar_val (evar_fresh (elements (free_evars ϕ))) x0 ρₑ) ρₛ).
      destruct H.
      * exfalso. apply H0. exists x0. apply H.
      * unfold Same_set in H. destruct H. clear H2.
        unfold Included in H. specialize (H x).
        auto.
    + unfold Included. intros. inversion H1.
Qed.

(* TODO top forall iff *)


Lemma predicate_not_empty_impl_full M ϕ ρₑ ρₛ :
  M_predicate M ϕ ->
  ~ Same_set (Domain M) (pattern_interpretation ρₑ ρₛ ϕ) (Empty_set _) ->
  Same_set (Domain M) (pattern_interpretation ρₑ ρₛ ϕ) (Full_set _).
Proof.
  intros Hmp Hne. specialize (Hmp ρₑ ρₛ).
  destruct Hmp.
  + assumption.
  + contradiction.
Qed.

Lemma predicate_not_full_impl_empty M ϕ ρₑ ρₛ :
  M_predicate M ϕ ->
  ~ Same_set (Domain M) (pattern_interpretation ρₑ ρₛ ϕ) (Full_set _) ->
  Same_set (Domain M) (pattern_interpretation ρₑ ρₛ ϕ) (Empty_set _).
Proof.
  intros Hmp Hne. specialize (Hmp ρₑ ρₛ).
  destruct Hmp.
  + contradiction.
  + assumption.
Qed.


(* ML's 'set comprehension'/'set building' scheme.
   Pattern `∃ x. x ∧ P(x)` gets interpreted as {m ∈ M | P(m) holds}
 *)
(* ϕ is expected to have dangling evar indices *)

Lemma pattern_interpretation_set_builder M ϕ ρₑ ρₛ :
  let x := fresh_evar ϕ in
  M_predicate M (evar_open 0 x ϕ) ->
  Same_set (Domain M)
           (pattern_interpretation ρₑ ρₛ (patt_exists (patt_and (patt_bound_evar 0) ϕ)))
           (fun m : (Domain M) => Same_set (Domain M)
                                           (pattern_interpretation (update_evar_val x m ρₑ) ρₛ (evar_open 0 x ϕ))
                                           (Full_set _)).
Proof.
  simpl. intros Hmp.
  rewrite -> pattern_interpretation_ex_simpl.
  red. unfold fresh_evar. simpl free_evars.
  repeat rewrite -> union_empty_r_L.
  rewrite -> union_empty_l_L.
  rewrite -> evar_open_and.
  remember (evar_fresh (elements (free_evars ϕ))) as x.
  unfold Included. unfold Ensembles.In. split; intros m H.
  - destruct H as [m [m' H]].
    rewrite -> pattern_interpretation_and_simpl in H.
    unfold Ensembles.In in H.
    destruct H as [m Hbound Hϕ].
    assert (Heqmm' : m = m').
    { unfold Ensembles.In in Hbound.
      simpl in Hbound.
      rewrite -> pattern_interpretation_free_evar_simpl in Hbound. destruct Hbound. 
      unfold update_evar_val.
      destruct (evar_eq x x).
      + simpl. reflexivity.
      + contradiction.
    }
    rewrite <- Heqmm' in Hϕ.
    apply predicate_not_empty_impl_full.
    + rewrite -> Heqx. unfold fresh_evar in Hmp. assumption.
    + apply Contains_Elements_Not_Empty.
      exists m. assumption.
  - constructor. exists m.
    rewrite -> pattern_interpretation_and_simpl. constructor.
    + simpl. rewrite -> pattern_interpretation_free_evar_simpl.
      unfold Ensembles.In. rewrite -> update_evar_val_same. constructor.
    + destruct H as [H1 H2]. unfold Included in H2.
      specialize (H2 m). apply H2. unfold Ensembles.In. constructor.
Qed.

End semantics.

Module MLNotations.
  Declare Scope ml_scope.
  Delimit Scope ml_scope with ml.
  (* TODO: change Bot and Top to unicode symbols *)
  Notation "a $ b" := (patt_app a b) (at level 65, right associativity) : ml_scope.
  Notation "'Bot'" := patt_bott : ml_scope.
  Notation "a ---> b"  := (patt_imp a b) (at level 90, right associativity,
                                         b at level 200) : ml_scope.
  Notation "'ex' , phi" := (patt_exists phi) (at level 70) : ml_scope.
  Notation "'mu' , phi" := (patt_mu phi) (at level 70) : ml_scope.

  Notation "¬ a"     := (patt_not   a  ) (at level 75, right associativity) : ml_scope.
  Notation "a 'or' b" := (patt_or    a b) (at level 85, right associativity) : ml_scope.
  Notation "a 'and' b" := (patt_and   a b) (at level 80, right associativity) : ml_scope.
  Notation "a <---> b" := (patt_iff a b) (at level 95, no associativity) : ml_scope.
  Notation "'Top'" := patt_top : ml_scope.
  Notation "'all' , phi" := (patt_forall phi) (at level 70) : ml_scope.
  Notation "'nu' , phi" := (patt_nu phi) (at level 70) : ml_scope.

  Notation "M ⊨ᴹ phi" := (satisfies_model M phi) (left associativity, at level 50) : ml_scope.
  (* FIXME this should not be called `satisfies` *)
Notation "G ⊨ phi" := (satisfies G phi) (left associativity, at level 50) : ml_scope.
Notation "M ⊨ᵀ Gamma" := (satisfies_theory M Gamma)
    (left associativity, at level 50) : ml_scope.
End MLNotations.

Section ml_proof_system.
  Import MLNotations.
  Open Scope ml_scope.

  Context {signature : Signature}.
(* Proof system for AML ref. snapshot: Section 3 *)
(* TODO: all propagation rules, framing, use left and right rules (no contexts) like in bott *)
(* TODO: add well-formedness of theory *)
(* TODO: use well-formedness as parameter in proof system *)

Reserved Notation "theory ⊢ pattern" (at level 1).
Inductive ML_proof_system (theory : Theory) :
  Pattern -> Prop :=

(* Hypothesis *)
  | hypothesis (axiom : Pattern) :
      well_formed axiom ->
      (Ensembles.In _ theory axiom) -> theory ⊢ axiom
  
(* FOL reasoning *)
  (* Propositional tautology *)
  | P1 (phi psi : Pattern) :
      well_formed phi -> well_formed psi ->
      theory ⊢ (phi ---> (psi ---> phi))
  | P2 (phi psi xi : Pattern) :
      well_formed phi -> well_formed psi -> well_formed xi ->
      theory ⊢ ((phi ---> (psi ---> xi)) ---> ((phi ---> psi) ---> (phi ---> xi)))
  | P3 (phi : Pattern) :
      well_formed phi ->
      theory ⊢ (((phi ---> Bot) ---> Bot) ---> phi)

  (* Modus ponens *)
  | Modus_ponens (phi1 phi2 : Pattern) :
      well_formed phi1 -> well_formed (phi1 ---> phi2) ->
      theory ⊢ phi1 ->
      theory ⊢ (phi1 ---> phi2) ->
      theory ⊢ phi2

  (* Existential quantifier *)
  | Ex_quan (phi : Pattern) (y : evar) :
      well_formed phi ->
      theory ⊢ (instantiate (patt_exists phi) (patt_free_evar y) ---> (patt_exists phi))

  (* Existential generalization *)
  | Ex_gen (phi1 phi2 : Pattern) (x : evar) :
      well_formed phi1 -> well_formed phi2 ->
      theory ⊢ (phi1 ---> phi2) ->
      x ∉ (free_evars phi2) ->
      theory ⊢ (exists_quantify x phi1 ---> phi2)

(* Frame reasoning *)
  (* Propagation bottom *)
  | Prop_bott_left (phi : Pattern) :
      well_formed phi ->
      theory ⊢ (patt_bott $ phi ---> patt_bott)

  | Prop_bott_right (phi : Pattern) :
      well_formed phi ->
      theory ⊢ (phi $ patt_bott ---> patt_bott)

  (* Propagation disjunction *)
  | Prop_disj_left (phi1 phi2 psi : Pattern) :
      well_formed phi1 -> well_formed phi2 -> well_formed psi ->
      theory ⊢ (((phi1 or phi2) $ psi) ---> ((phi1 $ psi) or (phi2 $ psi)))

  | Prop_disj_right (phi1 phi2 psi : Pattern) :
      well_formed phi1 -> well_formed phi2 -> well_formed psi ->
      theory ⊢ ((psi $ (phi1 or phi2)) ---> ((psi $ phi1) or (psi $ phi2)))

  (* Propagation exist *)
  | Prop_ex_left (phi psi : Pattern) :
      well_formed (ex , phi) -> well_formed psi ->
      theory ⊢ (((ex , phi) $ psi) ---> (ex , phi $ psi))

  | Prop_ex_right (phi psi : Pattern) :
      well_formed (ex , phi) -> well_formed psi ->
      theory ⊢ ((psi $ (ex , phi)) ---> (ex , psi $ phi))

  (* Framing *)
  | Framing_left (phi1 phi2 psi : Pattern) :
      theory ⊢ (phi1 ---> phi2) ->
      theory ⊢ ((phi1 $ psi) ---> (phi2 $ psi))

  | Framing_right (phi1 phi2 psi : Pattern) :
      theory ⊢ (phi1 ---> phi2) ->
      theory ⊢ ((psi $ phi1) ---> (psi $ phi2))

(* Fixpoint reasoning *)
  (* Set Variable Substitution *)
  | Svar_subst (phi psi : Pattern) (X : svar) :
      theory ⊢ phi -> theory ⊢ (free_svar_subst phi psi X)

  (* Pre-Fixpoint *)
  (* TODO: is this correct? *)
  | Pre_fixp (phi : Pattern) :
      theory ⊢ (instantiate (patt_mu phi) (patt_mu phi) ---> (patt_mu phi))

  (* Knaster-Tarski *)
  | Knaster_tarski (phi psi : Pattern) :
      theory ⊢ ((instantiate (patt_mu phi) psi) ---> psi) ->
      theory ⊢ ((@patt_mu signature phi) ---> psi)

  (* Technical rules *)
  (* Existence *)
  | Existence : theory ⊢ (ex , patt_bound_evar 0)

  (* Singleton *)
  | Singleton_ctx (C1 C2 : Application_context) (phi : Pattern) (x : evar) : 
      theory ⊢ (¬ ((subst_ctx C1 (patt_free_evar x and phi)) and
                    (subst_ctx C2 (patt_free_evar x and (¬ phi)))))

where "theory ⊢ pattern" := (ML_proof_system theory pattern).

Definition T_predicate Γ ϕ := forall M, (M ⊨ᵀ Γ) -> @M_predicate signature M ϕ.

Lemma T_predicate_impl Γ ϕ₁ ϕ₂ : T_predicate Γ ϕ₁ -> T_predicate Γ ϕ₂ -> T_predicate Γ (patt_imp ϕ₁ ϕ₂).
Proof.
  unfold T_predicate.
  intros.
  auto using M_predicate_impl.
Qed.

Lemma T_predicate_bot Γ : T_predicate Γ patt_bott.
Proof.
  unfold T_predicate.
  intros.
  auto using M_predicate_bott.
Qed.

Lemma T_predicate_not Γ ϕ : T_predicate Γ ϕ -> T_predicate Γ (patt_not ϕ).
Proof.
  unfold T_predicate.
  intros.
  auto using M_predicate_not.
Qed.

Lemma T_predicate_or Γ ϕ₁ ϕ₂ : T_predicate Γ ϕ₁ -> T_predicate Γ ϕ₂ -> T_predicate Γ (patt_or ϕ₁ ϕ₂).
Proof.
  unfold T_predicate.
  intros.
  auto using M_predicate_or.
Qed.

Lemma T_predicate_and Γ ϕ₁ ϕ₂ : T_predicate Γ ϕ₁ -> T_predicate Γ ϕ₂ -> T_predicate Γ (patt_and ϕ₁ ϕ₂).
Proof.
  unfold T_predicate.
  intros.
  auto using M_predicate_and.
Qed.

(* TODO: top iff exists forall *)


End ml_proof_system.


