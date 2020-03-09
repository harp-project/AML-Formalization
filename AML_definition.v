Require Import String.
Require Import Coq.Lists.ListSet.

Section AML.

Inductive EVar : Type := evar_c {id_ev : string}.
Inductive SVar : Type := svar_c {id_sv : string}.
Inductive Sigma : Type := sigma_c {id_si : string}.

Inductive Sigma_pattern : Type :=
  | sp_var (x : EVar)
  | sp_set (X : SVar)
  | sp_const (sigma : Sigma)
  | sp_app (phi1 phi2 : Sigma_pattern)
  | sp_bottom
  | sp_impl (phi1 phi2 : Sigma_pattern)
  | sp_exists (x : EVar) (phi : Sigma_pattern)
  | sp_mu (X : SVar) (phi : Sigma_pattern)
.

(* Definition is_svar_box (s : SVar) : bool :=
  match s with
  | svar_c id => eqb id "box"
  end
.

Inductive sp_context_e : Sigma_pattern -> Prop :=
  | c_box (x : SVar) (p : (is_svar_box x) = true ) : sp_context_e (sp_set x)
  | c_cons_l (spl spr : Sigma_pattern) (p : sp_context_e spl) : sp_context_e (sp_app spl spr)
  | s_cons_r (spl spr : Sigma_pattern) (p : sp_context_e spr) : sp_context_e (sp_app spl spr)
. *)

Definition evar_eq_dec : forall (x y : EVar), { x = y } + { x <> y }.
Proof. decide equality. exact (string_dec id_ev0 id_ev1). Defined.

Definition svar_eq_dec : forall (x y : SVar), { x = y } + { x <> y }.
Proof. decide equality. exact (string_dec id_sv0 id_sv1). Defined.

Definition sigma_eq_dec : forall (x y : Sigma), { x = y } + { x <> y }.
Proof. decide equality. exact (string_dec id_si0 id_si1). Defined.

Definition evar_eqb (x y : EVar) : bool := eqb (id_ev x) (id_ev y).
Definition svar_eqb (x y : SVar) : bool := eqb (id_sv x) (id_sv y).
Definition sigma_eqb (x y : Sigma) : bool := eqb (id_si x) (id_si y).

Fixpoint spos_accumulated (phi : Sigma_pattern) (X : SVar) (nc : nat) : bool :=
  match phi with
  | sp_var x => true
  | sp_set Y => if (svar_eq_dec Y X)
                then (Nat.even nc)
                else true
  | sp_const sigma => true
  | sp_app phi1 phi2 => andb (spos_accumulated phi1 X nc) (spos_accumulated phi2 X nc)
  | sp_bottom => true
  | sp_impl phi1 phi2 => andb (spos_accumulated phi1 X (S nc)) (spos_accumulated phi2 X nc)
  | sp_exists x phi => spos_accumulated phi X nc
  | sp_mu Y phi => if (svar_eq_dec Y X)
                      then true
                      else (spos_accumulated phi X nc)
end.

Fixpoint strictly_positive (phi : Sigma_pattern) (X : SVar) : bool :=  spos_accumulated phi X 0.

Definition sp_eq_dec : forall (x y : Sigma_pattern), { x = y } + { x <> y }.
Proof.
  decide equality.
  - exact (evar_eq_dec x0 x1).
  - exact (svar_eq_dec X X0).
  - exact (sigma_eq_dec sigma sigma0).
  - exact (evar_eq_dec x0 x1).
  - exact (svar_eq_dec X X0).
Defined.

Fixpoint e_subst_var (phi : Sigma_pattern) (psi : Sigma_pattern) (x : EVar) :=
  match phi with
  | sp_var x' =>
      if evar_eq_dec x x'
      then psi
      else sp_var x'
  | sp_set X => sp_set X
  | sp_const sigma => sp_const sigma
  | sp_app phi1 phi2 => sp_app (e_subst_var phi1 psi x)
                                (e_subst_var phi2 psi x)
  | sp_bottom => sp_bottom
  | sp_impl phi1 phi2 => sp_impl (e_subst_var phi1 psi x)
                                  (e_subst_var phi2 psi x)
  | sp_exists x' phi' =>
      if (evar_eq_dec x' x)
      then sp_exists x' phi'
      else sp_exists x' (e_subst_var phi' psi x)
  | sp_mu X phi' => sp_mu X (e_subst_var phi' psi x)
end.

Fixpoint e_subst_set (phi : Sigma_pattern) (psi : Sigma_pattern) (X : SVar) :=
  match phi with
  | sp_var x => sp_var x
  | sp_set X' =>
      if svar_eq_dec X X'
      then psi
      else sp_set X'
  | sp_const sigma => sp_const sigma
  | sp_app phi1 phi2 => sp_app (e_subst_set phi1 psi X)
                                (e_subst_set phi2 psi X)
  | sp_bottom => sp_bottom
  | sp_impl phi1 phi2 => sp_impl (e_subst_set phi1 psi X)
                                  (e_subst_set phi2 psi X)
  | sp_exists x' phi' => sp_exists x' (e_subst_set phi' psi X)
  | sp_mu X' phi' =>
      if (svar_eq_dec X' X)
      then sp_mu X' phi'
      else sp_mu X' (e_subst_set phi' psi X)
end.

Definition sp_not (phi : Sigma_pattern) := sp_impl phi sp_bottom.
Definition sp_or  (phi1 phi2 : Sigma_pattern) := sp_impl (sp_not phi1) phi2.
Definition sp_and (phi1 phi2 : Sigma_pattern) :=
  sp_not (sp_or (sp_not phi1) (sp_not phi2)).
Definition sp_top := sp_not sp_bottom.
Definition sp_only_if (phi1 phi2 : Sigma_pattern) := sp_and (sp_impl phi1 phi2) (sp_impl phi2 phi1).
Definition sp_forall (x : EVar) (phi : Sigma_pattern) :=
  sp_not (sp_exists x (sp_not phi)).
Definition sp_nu (X : SVar) (phi : Sigma_pattern) := sp_not (sp_mu X (sp_not (e_subst_set phi (sp_not (sp_set X)) X))).

Definition evar_eq (x y : EVar) : bool :=
  match x, y with
  | evar_c id_x, evar_c id_y => eqb id_x id_y
  end
.

Fixpoint free_vars (phi : Sigma_pattern) : (set EVar) :=
  match phi with
 | sp_var x => set_add evar_eq_dec x nil
 | sp_set X => nil
 | sp_const sigma => nil
 | sp_app phi1 phi2 =>
    set_union evar_eq_dec
      (free_vars phi1)
      (free_vars phi2)
 | sp_bottom => nil
 | sp_impl phi1 phi2 =>
    set_union evar_eq_dec
      (free_vars phi1)
      (free_vars phi2)
 | sp_exists y phi =>
    set_diff evar_eq_dec
      (free_vars phi)
      (set_add evar_eq_dec y nil)
 | sp_mu X phi => free_vars phi
end
.

(* Definition is_free (x : EVar) (phi : Sigma_pattern) : bool :=
  set_mem evar_eq_dec x (free_vars phi). *)

(* Inductive application_context : Set :=
  | pattern (p : Sigma_pattern)
  | box
.
 *)

Inductive context : Set :=
  | box
  | ctx_app_l (cc : context) (sp : Sigma_pattern)
  | ctx_app_r (sp : Sigma_pattern) (cc : context)
.

Fixpoint subst_ctx (cc : context) (sp : Sigma_pattern) : Sigma_pattern :=
  match cc with
  | box => sp
  | ctx_app_l cc' sp' => sp_app (subst_ctx cc' sp) sp'
  | ctx_app_r sp' cc' => sp_app sp' (subst_ctx cc' sp)
  end
.

(* FIXME Create Test File *)
Definition box_context := subst_ctx box sp_bottom.
Eval compute in box_context.

Definition tree_context := subst_ctx (
    ctx_app_l (ctx_app_r sp_bottom box) (sp_app sp_bottom sp_bottom)
  ) sp_bottom.
Eval compute in tree_context.

Definition free_vars_ctx (C : context) : (set EVar) :=
  match C with
  | box => nil
  | ctx_app_l cc sp => free_vars sp
  | ctx_app_r sp cc => free_vars sp
  end
.
(* Inductive got_tau : Sigma_pattern -> Prop :=
  | cons (phi : Sigma_pattern) : got_tau (sp_impl sp_bottom phi)
. *)

Inductive got : Sigma_pattern -> Prop :=
  (* Propositional tautology *)
  (* | E_prop_tau phi : phi is prop tau -> got phi *)

  (* Modus ponens *)
  | E_mod_pon (phi1 phi2 : Sigma_pattern) :
    got phi1 ->
    got (sp_impl phi1 phi2) ->
    got phi2

  (* Existential quantifier *)
  | E_ex_quan {phi : Sigma_pattern} (x y : EVar) :
    got (sp_impl (e_subst_var phi (sp_var y) x) (sp_exists x phi))

  (* Existential generalization *)
  | E_ex_gen (phi1 phi2 : Sigma_pattern) (x : EVar) :
    got (sp_impl phi1 phi2) ->
    negb (set_mem evar_eq_dec x (free_vars phi2)) = true ->
    got (sp_impl (sp_exists x phi1) phi2)

  (* Propagation bottom *)
  | E_prop_bot (C : context) :
    got (sp_impl (subst_ctx C sp_bottom) sp_bottom)

  (* Propagation disjunction *)
  | E_prop_dis (C : context) (phi1 phi2 : Sigma_pattern) :
      (* phi3 = context cs (sp_or phi1 phi2) ->
      phi4 = context cs phi1 ->
      phi5 = context cs phi2 ->
      got_c (sp_impl phi3 (sp_or phi4 phi5)) *)
      got (sp_impl
            (subst_ctx C (sp_or phi1 phi2))
            (sp_or
              (subst_ctx C phi1)
              (subst_ctx C phi2)))

  (* Propagation exist *)
  | E_prop_ex (C : context) (phi : Sigma_pattern) (x : EVar) :
    negb (set_mem evar_eq_dec x (free_vars_ctx C)) = true ->
    got (sp_impl
      (subst_ctx C (sp_exists x phi))
      (sp_exists x (subst_ctx C phi)))

  (* Framing *)
  | E_framing (C : context) (phi1 phi2 : Sigma_pattern) :
    got (sp_impl phi1 phi2) ->
    got (sp_impl (subst_ctx C phi1) (subst_ctx C phi2))

  (* Set Variable Substitution *)
  | E_svar_subst (phi : Sigma_pattern) (psi X : SVar) :
    got phi ->
    got (e_subst_set phi (sp_set psi) X)

  (* Pre-Fixpoint *)
  | E_pre_fixp (phi : Sigma_pattern) (X : SVar) :
    got (sp_impl
          (e_subst_set phi (sp_mu X phi) X)
          (sp_mu X phi))

  (* Knaster-Tarski *)
  | E_knaster_tarski (phi psi : Sigma_pattern) (X : SVar) :
    got (sp_impl (e_subst_set phi psi X) psi) ->
    got (sp_impl (sp_mu X phi) psi)

  (* Existence *)
  | E_existence (x : EVar) : got (sp_exists x (sp_var x))

  (* Singleton *)
  | E_singleton (C1 C2 : context) (x : EVar) (phi : Sigma_pattern) :
    got (sp_not (sp_and
            (subst_ctx C1 (sp_and (sp_var x) phi))
            (subst_ctx C2 (sp_and (sp_var x) (sp_not phi)))))
.

(* Inductive proof_result : ? :=
  | success (?)
  | fail
. *)

(* TO DO:
    - free variables: Context -> Set OK
    - eSubstitution for sets OK
x occurs free
x occurs bound
instance of x is bound or not -> identify the location in the tree

box, context : define inductively
 *)

(*
  2019.11.06.:
  Context 3 fajtaja:
    - inductive tipuskent OK
    - az amit Daviddal most elkezdtunk () -
    - a context egy fuggveny -
  Folyamatosan jegyzeteljunk!
*)
(*
  2019.11.13.:
  - the best choice: context as a separate inductive type
        reason: it is much simple to reason about an inductively defined structure, than to reason about a function of which we know nothing
  - discuss about Gamma |- Phi  (soundness theorem)
    - include it between proof rules
*)

End AML.

Require Import Coq.Sets.Ensembles.

Inductive FA_Intersection {T C : Type} (f : C -> Ensemble T) : Ensemble T :=
  FA_Int_intro : forall x : T,
      (forall c : C, f c x) -> In T (FA_Intersection f) x.

Inductive FA_Union {T C : Type} (f : C -> Ensemble T) : Ensemble T :=
  FA_Uni_intro : forall x : T,
      (exists c : C, f c x) -> In T (FA_Union f) x.

Axiom FA_rel : forall T C : Type, forall f fcomp : C -> Ensemble T,
(forall c : C, Same_set T (Complement T (f c)) (fcomp c))
-> Same_set T (Complement T (FA_Union f)) (FA_Intersection fcomp).

Definition mu {T : Type} (f : Ensemble T -> Ensemble T) : Ensemble T :=
  FA_Intersection (fun S => let S' := f S in fun x => Included T S' S -> S x).

Definition nu {T : Type} (f : Ensemble T -> Ensemble T) : Ensemble T :=
  FA_Union (fun S => let S' := f S in fun x => Included T S S' -> S x).

Definition change_val {T1 T2 : Type} (eqb : T1 -> T1 -> bool) (t1 : T1) (t2 : T2) (f : T1 -> T2) : T1 -> T2 :=
  fun x : T1 => if eqb x t1 then t2 else f x.

Section Model.

Record Sigma_model := {
  M : Type;
  A_eq_dec : forall (a b : M), {a = b} + {a <> b};
  app : M -> M -> Ensemble M;
  interpretation : Sigma -> Ensemble M;
}.

Definition pointwise_app {sm : Sigma_model} (l r : Ensemble (M sm)) : Ensemble (M sm) :=
  fun e:M sm => exists le re:M sm, l le -> r re -> (app sm) le re e.

Fixpoint ext_valuation {sm : Sigma_model} (evar_val : EVar -> M sm) (svar_val : SVar -> Ensemble (M sm)) (sp : Sigma_pattern) : Ensemble (M sm) :=
match sp with
  (* sp_var *)
  | sp_var x => Singleton _ (evar_val x)
  (* sp_set *)
  | sp_set X => svar_val X
  (* sp_const *)
  | sp_const s => (interpretation sm) s
  (* sp_app *)
  | sp_app ls rs =>
    pointwise_app (ext_valuation evar_val svar_val ls) (ext_valuation evar_val svar_val rs)
  (* sp_bottom *)
  | sp_bottom => Empty_set _
  (* sp_impl *)
  | sp_impl ls rs => Union _ (Complement _ (ext_valuation evar_val svar_val ls)) (ext_valuation evar_val svar_val rs)
  (* sp_exists *)
  | sp_exists x sp =>
    FA_Union (fun e => ext_valuation (change_val evar_eqb x e evar_val) svar_val sp)
  (* sp_mu *)
  | sp_mu X sp =>
    mu (fun S => ext_valuation evar_val (change_val svar_eqb X S svar_val) sp)
end
.

End Model.

(* Lemma union_empty_r {T : Type} : forall A : Ensemble T, Same_set T (Union T (Empty_set T) A) A.
Proof.
unfold Same_set. unfold Included. intros. apply conj;intros.
 * inversion H. inversion H0. exact H0.
 * unfold In in *. eapply Union_intror. exact H.
Qed. *)

Lemma union_empty_l {T : Type} : forall A : Ensemble T, Same_set T (Union T A (Empty_set T)) A.
Proof.
unfold Same_set. unfold Included. intros. apply conj;intros.
 * inversion H. exact H0. inversion H0.
 * unfold In in *. eapply Union_introl. exact H.
Qed.

Definition Symmetric_difference {T : Type} (A B : Ensemble T) : Ensemble T :=
  Union T (Setminus T A B) (Setminus T B A).

Axiom Compl_Compl_Ensembles : forall T :Type, forall A :Ensemble T, Same_set T (Complement T (Complement T A)) A.

Axiom Compl_Union_Coml_Intes_Ensembles : forall T :Type, forall L R : Ensemble T, Same_set T (Complement T (Union T (Complement T L) (Complement T R))) (Intersection T L R).

Axiom Empty_is_Empty : forall T : Type, forall x : T, ~ In T (Empty_set T) x.

Lemma Complement_Empty_is_Full {T : Type} : Same_set T (Complement T (Empty_set T)) (Full_set T).
Proof.
unfold Same_set. unfold Complement. unfold Included. unfold In. eapply conj.
* intros. eapply Full_intro.
* intros. eapply Empty_is_Empty.
Qed.

Lemma Ensemble_refl {T : Type} (A : Ensemble T) : Same_set T A A.
Proof. unfold Same_set;unfold Included;apply conj;intros;exact H. Qed.

Lemma Ensemble_Compl_trans {T : Type} (A B : Ensemble T) : Same_set T A B -> Same_set T (Complement T A) (Complement T B).
Proof.
unfold Same_set. unfold Included. unfold Complement. unfold not. unfold In.
intros. apply conj;intros;inversion H. exact (H0 (H3 _ H1)). exact (H0 (H2 _ H1)).
Qed.

Lemma Same_set_symmetric {T : Type} (A B : Ensemble T) : Same_set T A B -> Same_set T B A.
Proof. unfold Same_set. intros. inversion H. eapply conj;assumption. Qed.

Lemma Setmin_Val {T : Type} (A B : Ensemble T) : Same_set T (Complement T (Union T (Complement T A) B)) (Setminus T A B).
Proof.
unfold Same_set. unfold In.
rewrite <- (Extensionality_Ensembles _ _ _ (Compl_Compl_Ensembles _ B)).
rewrite (Extensionality_Ensembles _ _ _ (Compl_Union_Coml_Intes_Ensembles _ _ _)).
rewrite (Extensionality_Ensembles _ _ _ (Compl_Compl_Ensembles _ B)).
unfold Included. eapply conj;intros;inversion H;((unfold Setminus;apply conj)|| apply Intersection_intro);try exact H0; unfold Complement in *; unfold In in *; exact H1.
Qed.

Lemma Symdiff_val {T : Type} (A B : Ensemble T) : Same_set T (Intersection T (Union T (Complement T A) B) (Union T (Complement T B) A))
  (Complement T (Symmetric_difference A B)).
Proof. unfold Symmetric_difference.
rewrite <- (Extensionality_Ensembles _ _ _ (Compl_Union_Coml_Intes_Ensembles T _ _)).
rewrite (Extensionality_Ensembles _ _ _ (Setmin_Val A B)).
rewrite (Extensionality_Ensembles _ _ _ (Setmin_Val B A)).
eapply Ensemble_refl.
Qed.

Ltac proof_ext_val :=
simpl;intros;
repeat
  (* Normalize *)
   rewrite (Extensionality_Ensembles _ _ _ (union_empty_l _))
|| rewrite (Extensionality_Ensembles _ _ _ (Compl_Compl_Ensembles _ _))
|| rewrite (Extensionality_Ensembles _ _ _ (Compl_Union_Coml_Intes_Ensembles _ _ _))
  (* Apply *)
|| (eapply FA_rel ; idtac "FA_Rel" ; intros)
|| (eapply Ensemble_Compl_trans ; idtac "Ensemble_Compl_trans" ; intros) 
  (* Final step *)
|| exact Complement_Empty_is_Full
|| exact (Symdiff_val _ _)
|| exact (Ensemble_refl _).

Lemma not_ext_val_correct {sm : Sigma_model} {evar_val : EVar -> M sm} {svar_val : SVar -> Ensemble _} : forall sp : Sigma_pattern, Same_set _ (ext_valuation evar_val svar_val (sp_not sp)) (Complement _ (ext_valuation evar_val svar_val sp)).
Proof. proof_ext_val. Qed.

Lemma or_ext_val_correct {sm : Sigma_model} {evar_val : EVar -> M sm} {svar_val : SVar -> Ensemble _} : forall spl spr : Sigma_pattern, Same_set _ (ext_valuation evar_val svar_val (sp_or spl spr)) (Union _ (ext_valuation evar_val svar_val spl) (ext_valuation evar_val svar_val spr)).
Proof. proof_ext_val. Qed.

Lemma and_ext_val_correct {sm : Sigma_model} {evar_val : EVar -> M sm} {svar_val : SVar -> Ensemble _} : forall spl spr : Sigma_pattern, Same_set _ (ext_valuation evar_val svar_val (sp_and spl spr)) (Intersection _ (ext_valuation evar_val svar_val spl) (ext_valuation evar_val svar_val spr)).
Proof. proof_ext_val. Qed.

Lemma top_ext_val_correct {sm : Sigma_model} {evar_val : EVar -> M sm} {svar_val : SVar -> Ensemble _} : Same_set _ (ext_valuation evar_val svar_val (sp_top)) (Full_set _).
Proof. proof_ext_val. Qed.

Lemma only_if_ext_val_correct {sm : Sigma_model} {evar_val : EVar -> M sm} {svar_val : SVar -> Ensemble _} : forall spl spr : Sigma_pattern, Same_set _ (ext_valuation evar_val svar_val (sp_only_if spl spr)) (Complement _ (Symmetric_difference (ext_valuation evar_val svar_val spl) (ext_valuation evar_val svar_val spr))).
Proof. proof_ext_val. Qed.

Lemma forall_ext_val_correct {sm : Sigma_model} {evar_val : EVar -> M sm} {svar_val : SVar -> Ensemble _} : forall sp : Sigma_pattern, forall x : EVar, Same_set _ (ext_valuation evar_val svar_val (sp_forall x sp))
(FA_Intersection (fun a:M sm => ext_valuation (change_val evar_eqb x a evar_val) svar_val sp)).
Proof. proof_ext_val. Qed.

Lemma asd {sm : Sigma_model} {evar_val : EVar -> M sm} {svar_val : SVar -> Ensemble _} : forall x0 : (M sm), forall c : Ensemble (M sm), forall X : SVar,
     Complement _ (ext_valuation evar_val (change_val svar_eqb X c svar_val) (sp_not (sp_set X))) x0 <-> c x0.
Proof.
proof_ext_val.
unfold change_val. unfold svar_eqb. rewrite (eqb_refl _). reflexivity.
Qed.

Lemma nu_ext_val_correct {sm : Sigma_model} {evar_val : EVar -> M sm} {svar_val : SVar -> Ensemble _} : forall sp : Sigma_pattern, forall X : SVar, Same_set _ (ext_valuation evar_val svar_val (sp_nu X sp))
(nu (fun S => ext_valuation evar_val (change_val svar_eqb X S svar_val) sp)).
Proof.
proof_ext_val.
unfold mu. unfold nu.
rewrite <- (Extensionality_Ensembles _ _ _ (Compl_Compl_Ensembles _ (FA_Union _))).
eapply Ensemble_Compl_trans.
eapply Same_set_symmetric.
proof_ext_val.
unfold Same_set. unfold Included. unfold Complement. unfold In. unfold not. eapply conj;intros.
* eapply H0. intros. eapply H. intros.
Admitted.
