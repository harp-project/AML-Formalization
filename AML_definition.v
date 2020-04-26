Require Import String.
Require Import Coq.Lists.ListSet.
Require Import Coq.Init.Datatypes.
Require Import Coq.Vectors.Fin.
Require Import Coq.Vectors.VectorDef.
Require Import Coq.Sets.Ensembles.

Add LoadPath "E:\Egyetem\MSc\4. felev\Diplomamunka\AML-Formalization".
Require Import Ensembles_Ext.

Section AML.

(* Syntax of AML ref. snapshot: Section 2.1 *)

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

Notation "' v" := (sp_var v) (at level 3).
Notation "` s" := (sp_set s) (at level 3).
Notation "^ c" := (sp_const c) (at level 3).
Notation "a $ b" := (sp_app a b) (at level 50, left associativity).
Notation "'Bot'" := sp_bottom.
Notation "a ~> b"  := (sp_impl a b) (at level 90, right associativity,
                                      b at level 200).
Notation "'ex' x , phi" := (sp_exists x phi) (at level 55).
Notation "'mu' X , phi" := (sp_mu X phi) (at level 55).

(* Derived operators *)
Definition sp_not (phi : Sigma_pattern) := phi ~> sp_bottom.
Notation "¬ a"     := (sp_not   a  ) (at level 75).

Definition sp_or  (l r : Sigma_pattern) := (¬ l) ~> r.
Notation "a _|_ b" := (sp_or    a b) (at level 85, right associativity).

Definition sp_and (l r : Sigma_pattern) := ¬ ((¬ l) _|_ (¬ r)).
Notation "a _&_ b" := (sp_and   a b) (at level 80, right associativity).

Definition sp_iff (l r : Sigma_pattern) := ((l ~> r) _&_ (l ~> r)).
Notation "a <~> b" := (sp_iff a b) (at level 95, no associativity).

Definition sp_top := (¬ sp_bottom).
Notation "'Top'" := sp_top.

Definition sp_forall (x : EVar) (phi : Sigma_pattern) :=
  ¬ (sp_exists x (¬ phi)).
Notation "'all' x , phi" := (sp_forall x phi) (at level 55).


Definition evar_eq_dec : forall (x y : EVar), { x = y } + { x <> y }.
Proof. decide equality. exact (string_dec id_ev0 id_ev1). Defined.

Definition svar_eq_dec : forall (x y : SVar), { x = y } + { x <> y }.
Proof. decide equality. exact (string_dec id_sv0 id_sv1). Defined.

Definition sigma_eq_dec : forall (x y : Sigma), { x = y } + { x <> y }.
Proof. decide equality. exact (string_dec id_si0 id_si1). Defined.

Definition evar_eqb (x y : EVar) : bool := String.eqb (id_ev x) (id_ev y).
Definition svar_eqb (x y : SVar) : bool := String.eqb (id_sv x) (id_sv y).
Definition sigma_eqb (x y : Sigma) : bool := String.eqb (id_si x) (id_si y).

Fixpoint e_subst_var (phi : Sigma_pattern) (psi : Sigma_pattern) (x : EVar) :=
match phi with
| sp_var x' => if evar_eq_dec x x'
               then psi
               else sp_var x'
| sp_set X => sp_set X
| sp_const sigma => sp_const sigma
| sp_app phi1 phi2 => sp_app (e_subst_var phi1 psi x)
                              (e_subst_var phi2 psi x)
| sp_bottom => sp_bottom
| sp_impl phi1 phi2 => sp_impl (e_subst_var phi1 psi x) (e_subst_var phi2 psi x)
| sp_exists x' phi' => if (evar_eq_dec x' x)
                       then sp_exists x' phi'
                       else sp_exists x' (e_subst_var phi' psi x)
| sp_mu X phi' => sp_mu X (e_subst_var phi' psi x)
end.

Fixpoint e_subst_set (phi : Sigma_pattern) (psi : Sigma_pattern) (X : SVar) :=
match phi with
| sp_var x => sp_var x
| sp_set X' => if svar_eq_dec X X'
               then psi
               else sp_set X'
| sp_const sigma => sp_const sigma
| sp_app phi1 phi2 => sp_app (e_subst_set phi1 psi X) (e_subst_set phi2 psi X)
| sp_bottom => sp_bottom
| sp_impl phi1 phi2 => sp_impl (e_subst_set phi1 psi X) (e_subst_set phi2 psi X)
| sp_exists x' phi' => sp_exists x' (e_subst_set phi' psi X)
| sp_mu X' phi' => if (svar_eq_dec X' X)
                   then sp_mu X' phi'
                   else sp_mu X' (e_subst_set phi' psi X)
end.


Definition sp_nu (X : SVar) (phi : Sigma_pattern) :=
  ¬ (sp_mu X (¬ (e_subst_set phi (¬ (sp_set X)) X))).
Notation "'nu' X , phi" := (sp_nu X phi) (at level 55).
(* End of derived operators *)

Definition var (name : string) : Sigma_pattern := sp_var (evar_c name).
Definition set (name : string) : Sigma_pattern := sp_set (svar_c name).
Definition const (name : string) : Sigma_pattern := sp_const (sigma_c name).

(* Example patterns: *)

Definition simple := var ("x").
Definition more := set ("A") _|_ ¬ (set "A").
Definition complex :=
  var("A") ~> (var("B") ~> ¬(set("C"))) $
  ex (evar_c("x")) , set ("D") $ Bot _&_ Top.
Definition custom_constructor := const ("ctor") $ var ("a").
Definition predicate := const ("p") $ var ("x1") $ var ("x2").
Definition function :=
  const ("f") $ (var ("x")) $ (mu svar_c("X"), (set ("X"))).

(* End of examples. *)


Fixpoint spos_accumulated (phi : Sigma_pattern) (X : SVar) (nc : nat) : bool :=
match phi with
| sp_var x => true
| sp_set Y => if (svar_eq_dec Y X)
              then (Nat.even nc)
              else true
| sp_const sigma => true
| sp_app phi1 phi2 => andb (spos_accumulated phi1 X nc)
                           (spos_accumulated phi2 X nc)
| sp_bottom => true
| sp_impl phi1 phi2 => andb (spos_accumulated phi1 X (S nc))
                            (spos_accumulated phi2 X nc)
| sp_exists x phi => spos_accumulated phi X nc
| sp_mu Y phi => if (svar_eq_dec Y X)
                 then true
                 else (spos_accumulated phi X nc)
end.

Fixpoint strictly_positive (phi : Sigma_pattern) (X : SVar) : bool :=
spos_accumulated phi X 0.

Definition sp_eq_dec : forall (x y : Sigma_pattern), { x = y } + { x <> y }.
Proof.
decide equality.
- exact (evar_eq_dec x0 x1).
- exact (svar_eq_dec X X0).
- exact (sigma_eq_dec sigma sigma0).
- exact (evar_eq_dec x0 x1).
- exact (svar_eq_dec X X0).
Defined.

Definition evar_eq (x y : EVar) : bool :=
match x, y with
| evar_c id_x, evar_c id_y => String.eqb id_x id_y
end.

Definition set_singleton := fun x => set_add evar_eq_dec x List.nil.

Fixpoint free_vars (phi : Sigma_pattern) : (ListSet.set EVar) :=
match phi with
| sp_var x => set_singleton x
| sp_set X => List.nil
| sp_const sigma => List.nil
| sp_app phi1 phi2 => set_union evar_eq_dec (free_vars phi1) (free_vars phi2)
| sp_bottom => List.nil
| sp_impl phi1 phi2 => set_union evar_eq_dec (free_vars phi1) (free_vars phi2)
| sp_exists y phi => set_diff evar_eq_dec (free_vars phi) (set_singleton y )
| sp_mu X phi => free_vars phi
end.


Definition change_val {T1 T2 : Type} (eqb : T1 -> T1 -> bool)
                      (t1 : T1) (t2 : T2) (f : T1 -> T2) : T1 -> T2 :=
fun x : T1 => if eqb x t1 then t2 else f x.


(* Model of AML ref. snapshot: Definition 2 *)

Record Sigma_model := {
  M : Type;
  A_eq_dec : forall (a b : M), {a = b} + {a <> b};
  app : M -> M -> Ensemble M;
  interpretation : Sigma -> Ensemble M;
}.

Definition pointwise_app {sm : Sigma_model} (l r : Ensemble (M sm)) :
                         Ensemble (M sm) :=
fun e:M sm => exists le re:M sm, l le -> r re -> (app sm) le re e.

(* Semantics of AML ref. snapshot: Definition 3 *)

Fixpoint ext_valuation {sm : Sigma_model} (evar_val : EVar -> M sm)
(svar_val : SVar -> Ensemble (M sm)) (sp : Sigma_pattern) : Ensemble (M sm) :=
match sp with
| sp_var x => Singleton _ (evar_val x)
| sp_set X => svar_val X
| sp_const s => (interpretation sm) s
| sp_app ls rs => pointwise_app (ext_valuation evar_val svar_val ls)
                                (ext_valuation evar_val svar_val rs)
| sp_bottom => Empty_set _
| sp_impl ls rs => Union _ (Complement _ (ext_valuation evar_val svar_val ls))
                           (ext_valuation evar_val svar_val rs)
| sp_exists x sp => FA_Union
  (fun e => ext_valuation (change_val evar_eqb x e evar_val) svar_val sp)
| sp_mu X sp => Ensembles_Ext.mu
  (fun S => ext_valuation evar_val (change_val svar_eqb X S svar_val) sp)
end
.

(* Proof of correct semantics for the derived operators
ref. snapshot: Proposition 4 *)

Ltac proof_ext_val :=
simpl;intros;
repeat
  (* Normalize *)
   rewrite (Extensionality_Ensembles _ _ _ (Union_Empty_l _))
|| rewrite (Extensionality_Ensembles _ _ _ (Compl_Compl_Ensembles _ _))
|| rewrite
   (Extensionality_Ensembles _ _ _ (Compl_Union_Compl_Intes_Ensembles _ _ _))
|| rewrite (Extensionality_Ensembles _ _ _ (FA_rel _ _ _))
  (* Apply *)
|| (eapply (proj1 Same_set_Compl) ; intros)
  (* Final step *)
|| exact Complement_Empty_is_Full
|| exact (Symdiff_val _ _)
|| exact (Same_set_refl _).

Lemma not_ext_val_correct
{sm : Sigma_model} {evar_val : EVar -> M sm} {svar_val : SVar -> Ensemble _} :
forall sp : Sigma_pattern, Same_set _
  (ext_valuation evar_val svar_val (sp_not sp))
  (Complement _ (ext_valuation evar_val svar_val sp)).
Proof. proof_ext_val. Qed.

Lemma or_ext_val_correct
{sm : Sigma_model} {evar_val : EVar -> M sm} {svar_val : SVar -> Ensemble _} :
forall spl spr : Sigma_pattern, Same_set _
  (ext_valuation evar_val svar_val (sp_or spl spr))
  (Union _ (ext_valuation evar_val svar_val spl)
           (ext_valuation evar_val svar_val spr)).
Proof. proof_ext_val. Qed.

Lemma and_ext_val_correct
{sm : Sigma_model} {evar_val : EVar -> M sm} {svar_val : SVar -> Ensemble _} :
forall spl spr : Sigma_pattern, Same_set _
  (ext_valuation evar_val svar_val (sp_and spl spr))
  (Intersection _ (ext_valuation evar_val svar_val spl)
                  (ext_valuation evar_val svar_val spr)).
Proof. proof_ext_val. Qed.

Lemma top_ext_val_correct
{sm : Sigma_model} {evar_val : EVar -> M sm} {svar_val : SVar -> Ensemble _} :
Same_set _ (ext_valuation evar_val svar_val (sp_top)) (Full_set _).
Proof. proof_ext_val. Qed.

Lemma only_if_ext_val_correct
{sm : Sigma_model} {evar_val : EVar -> M sm} {svar_val : SVar -> Ensemble _} :
forall spl spr : Sigma_pattern, Same_set _
  (ext_valuation evar_val svar_val (sp_iff spl spr))
  (Complement _ (Symmetric_difference (ext_valuation evar_val svar_val spl)
                                      (ext_valuation evar_val svar_val spr))).
Proof. proof_ext_val. Admitted.

Lemma forall_ext_val_correct
{sm : Sigma_model} {evar_val : EVar -> M sm} {svar_val : SVar -> Ensemble _} :
forall sp : Sigma_pattern, forall x : EVar, Same_set _
  (ext_valuation evar_val svar_val (sp_forall x sp))
  (FA_Intersection
    (fun a => ext_valuation (change_val evar_eqb x a evar_val) svar_val sp)).
Proof. proof_ext_val. eapply FA_Inters_same. intros. proof_ext_val. Qed.

Lemma nu_ext_val_correct
{sm : Sigma_model} {evar_val : EVar -> M sm} {svar_val : SVar -> Ensemble _} :
forall sp : Sigma_pattern, forall X : SVar, Same_set _
  (ext_valuation evar_val svar_val (sp_nu X sp))
  (Ensembles_Ext.nu
    (fun S => ext_valuation evar_val (change_val svar_eqb X S svar_val) sp)).
Proof.
proof_ext_val.

unfold Ensembles_Ext.mu. unfold Ensembles_Ext.nu. unfold FA_Union_cond.
unfold FA_Inters_cond.

apply Same_set_symmetric. apply Same_set_Compl.
rewrite (Extensionality_Ensembles _ _ _ (Compl_Compl_Ensembles _ _)).
rewrite (Extensionality_Ensembles _ _ _ (FA_rel _ _ _)).
eapply FA_Inters_same. intros.
proof_ext_val.
unfold Same_set. unfold Included. unfold Complement. unfold not. unfold In.
eapply conj.
* intros. eapply H0. intros. refine (H _). split.
  - intros.
Admitted.


(* Theory,axiom ref. snapshot: Definition 5 *)

Definition satisfies_model (sm : Sigma_model) (axiom : Sigma_pattern) : Prop :=
forall (evar_val : EVar -> M sm) (svar_val : SVar -> Ensemble (M sm)),
  Same_set _ (ext_valuation (sm := sm) evar_val svar_val axiom) (Full_set _).

Notation "M |=M phi" := (satisfies_model M phi) (left associativity, at level 50).

Definition satisfies_theory (sm : Sigma_model) (theory : Ensemble Sigma_pattern)
: Prop := forall axiom : Sigma_pattern, In _ theory axiom -> (sm |=M axiom).

Notation "M |=T Gamma" := (satisfies_theory M Gamma)
    (left associativity, at level 50).

Definition satisfies (theory : Ensemble Sigma_pattern) (sp : Sigma_pattern)
: Prop := forall sm : Sigma_model, (sm |=T theory) -> (sm |=M sp).

Notation "G |= phi" := (satisfies G phi) (left associativity, at level 50).

(* Definition AML_theories : ListSet.set Sigma_pattern := List.nil. *)

(* End of definition 5. *)


(* Definition 6. Definedness and derived operators *)
(* Definedness: *)
Definition c_definedness := (const ("definedness")).
Definition Definedness (x : Sigma_pattern) : Sigma_pattern :=
  (c_definedness $ x).
Notation "|^ x ^|" := (Definedness 'x) (at level 100).

Definition x := evar_c("x").
Definition Definedness_Axiom : Sigma_pattern :=
  sp_forall x (Definedness (sp_var x)).

(* Totality *)
Definition c_totality := (const ("totality")).
Definition Totality (phi : Sigma_pattern) := (c_totality $ phi).
Notation "|_ phi _|" := (Totality phi).

(* Equality *)
Definition c_equality := (const ("equality")).
Definition Equality (l r : Sigma_pattern) := ((c_equality $ l) $ r).
Notation "phi1 ~=~ phi2" := (Equality phi1 phi2) (at level 100).

(* Non-equality *)
Definition c_non_equality := (const ("non-equality")).
Definition NonEquality (l r : Sigma_pattern) := ((c_non_equality $ l) $ r).
Notation "phi1 !=~ phi2" := (NonEquality phi1 phi2) (at level 100).

(* Membership *)
Definition c_membership := (const ("membership")).
Definition VarMembership (x : EVar) (phi : Sigma_pattern) :=
  ((c_membership $ (sp_var x)) $ phi).
Definition ConstMembership (x : Sigma) (phi : Sigma_pattern) :=
  ((c_membership $ (sp_const x)) $ phi).

(* Non-membership *)
Definition c_non_membership := (const ("non-membership")).
Definition VarNonMembership (x : EVar) (phi : Sigma_pattern) :=
  ((c_non_membership $ (sp_var x)) $ phi).
Notation "x =< phi" := (VarMembership x phi) (at level 30).
Definition ConstNonMembership (x : Sigma) (phi : Sigma_pattern) :=
  ((c_non_membership $ (sp_const x)) $ phi).
Notation "x -< phi" := (ConstMembership x phi) (at level 30).

(* Set inclusion *)
Definition c_set_incl := (const ("set inclusion")).
Definition SetInclusion (l r : Sigma_pattern) :=
  ((c_set_incl $ l) $ r).
Notation "phi1 <: phi2" := (SetInclusion phi1 phi2) (at level 100).

(* Set exclusion *)
Definition c_set_excl := (const ("set exclusion")).
Definition SetExclusion (l r : Sigma_pattern) :=
  ((c_set_excl $ l) $ r).
Notation "phi1 !<: phi2" := (SetExclusion phi1 phi2) (at level 100).

Reserved Notation "phi |-> phi'" (at level 80).
Inductive DefinednessOneStepEquivalence : Sigma_pattern -> Sigma_pattern -> Prop :=
| DOSE_totality {phi : Sigma_pattern} :
    (c_totality $ phi) |->
    (¬ (Definedness (¬ phi)))

| DOSE_equality {l r : Sigma_pattern} :
    ((c_equality $ l) $ r) |->
    (Totality (sp_iff l r))

| DOSE_var_membership {x : EVar} {phi : Sigma_pattern} :
    ((c_membership $ (sp_var x)) $ phi) |->
    (Totality ((sp_var x) _&_ phi))

| DOSE_const_membership {x : Sigma} {phi : Sigma_pattern} :
    ((c_membership $ (sp_const x)) $ phi) |->
    (Totality ((sp_const x) _&_ phi))

| DOSE_set_inclusion {l r : Sigma_pattern} :
    ((c_set_incl $ l) $ r) |->
    (Totality (sp_impl l r))

| DOSE_non_equality {l r : Sigma_pattern} :
    ((c_equality $ l) $ r) |->
    (¬ (Equality l r))

| DOSE_var_non_membership {x : EVar} {phi : Sigma_pattern} :
    ((c_non_membership $ (sp_var x)) $ phi) |->
    (¬ (VarMembership x phi))

| DOSE_non_membership {x : Sigma} {phi : Sigma_pattern} :
    ((c_non_membership $ (sp_const x)) $ phi) |->
    (¬ (ConstMembership x phi))

| DOSE_set_exclusion {l r : Sigma_pattern} :
    ((c_set_excl $ l) $ r) |->
    (sp_not (SetInclusion l r))
where "a |-> b" := (DefinednessOneStepEquivalence a b).

Reserved Notation "phi |->* phi'" (at level 100).
Inductive DefinednessAnyStepEquivalence : Sigma_pattern -> Sigma_pattern -> Prop :=
| DASE_refl {phi : Sigma_pattern} :
    phi |->* phi

| DASE_trans {phi phi'' : Sigma_pattern} (phi' : Sigma_pattern) :
    (phi |-> phi') -> (phi' |->* phi'') ->
    (phi |->* phi'')
where "phi |->* phi'" := (DefinednessAnyStepEquivalence phi phi').
(* End of Definedness derived operators and exuivalences *)

(* Introducing $ element, such as $ $ a = M *)
Definition spec_elem : Sigma_pattern := const ("$").

Lemma spec_app_a_eq_M
  {sm : Sigma_model} {evar_val : EVar -> M sm} {svar_val : SVar -> Ensemble _} :
    forall a : EVar, Same_set _
      (ext_valuation evar_val svar_val (sp_app spec_elem (sp_var a)))
      (Full_set _).
Admitted.

Lemma spec_app_A_eq_M
  {sm : Sigma_model} {evar_val : EVar -> M sm} {svar_val : SVar -> Ensemble _} :
    forall A : SVar,
      (* A is not empty *)
      (exists x, In _ x (ext_valuation evar_val svar_val (sp_set A))) ->
      Same_set _
        (ext_valuation evar_val svar_val (sp_app spec_elem (sp_set A)))
        (Full_set _).
Admitted.

(* Can be shown, that all notations in Definition 6 are predicates with the
 * expected semantics. For example: *)
Lemma definedness_correct01
  {sm : Sigma_model} {evar_val : EVar -> M sm} {svar_val : SVar -> Ensemble _} :
  forall phi : Sigma_pattern,
  (Same_set _ (ext_valuation evar_val svar_val (Totality(phi)))
              (Full_set _)) <->
  (Same_set _ (ext_valuation evar_val svar_val (¬Definedness(¬phi)))
              (Full_set _)).
Admitted.

Lemma definedness_correct02
  {sm : Sigma_model} {evar_val : EVar -> M sm} {svar_val : SVar -> Ensemble _} :
  forall phi : Sigma_pattern,
  (Same_set _ (ext_valuation evar_val svar_val (Totality(phi)))
              (Full_set _)) <->
  (Same_set _ (ext_valuation evar_val svar_val (Definedness(¬phi)))
              (Empty_set _)).
Admitted.

Lemma definedness_correct03
  {sm : Sigma_model} {evar_val : EVar -> M sm} {svar_val : SVar -> Ensemble _} :
  forall phi : Sigma_pattern,
  (Same_set _ (ext_valuation evar_val svar_val (Totality(phi)))
              (Full_set _)) <->
  (Same_set _ (ext_valuation evar_val svar_val (Definedness(¬phi)))
              (Empty_set _)).
Admitted.

Lemma equality_correct01
  {sm : Sigma_model} {evar_val : EVar -> M sm} {svar_val : SVar -> Ensemble _} :
  forall phi1 phi2 : Sigma_pattern,
  (Same_set _ (ext_valuation evar_val svar_val (Equality phi1 phi2))
              (Full_set _)) <->
  (Same_set _ (ext_valuation evar_val svar_val (Totality (sp_iff phi1 phi2)))
              (Full_set _)).
Admitted.

Lemma equality_correct02
  {sm : Sigma_model} {evar_val : EVar -> M sm} {svar_val : SVar -> Ensemble _} :
  forall phi1 phi2 : Sigma_pattern,
  (Same_set _ (ext_valuation evar_val svar_val (Equality phi1 phi2))
              (Full_set _)) <->
  (Same_set _ (ext_valuation evar_val svar_val (phi1))
              (ext_valuation evar_val svar_val (phi2))).
Admitted.

(* TODO: semantics of definedness operators *)

Definition z := evar_c("z").
Definition Functional_Constant (constant : Sigma) : Sigma_pattern :=
  (ex z , (^constant ~=~ 'z)).
(* Definition Functional_Application (constant : Sigma) (y : EVar)
: Sigma_pattern :=
  (ex z , (^constant $ 'y) ~=~ 'z). *)

Inductive Application_context : Set :=
| box
| ctx_app_l (cc : Application_context) (sp : Sigma_pattern)
| ctx_app_r (sp : Sigma_pattern) (cc : Application_context)
.

Fixpoint subst_ctx (C : Application_context) (sp : Sigma_pattern) : Sigma_pattern :=
match C with
| box => sp
| ctx_app_l C' sp' => sp_app (subst_ctx C' sp) sp'
| ctx_app_r sp' C' => sp_app sp' (subst_ctx C' sp)
end
.

Definition free_vars_ctx (C : Application_context) : (ListSet.set EVar) :=
match C with
| box => List.nil
| ctx_app_l cc sp => free_vars sp
| ctx_app_r sp cc => free_vars sp
end.


(* Proof system for AML ref. snapshot: Section 3 *)

(*
states
OneStepTransitionJudgement, AnyStepTransitionJudgement
*)

(* Auxiliary axiom schemes for proving propositional tautology *)
Reserved Notation "pattern 'tautology'" (at level 2).
Inductive Tautology_proof_rules : Sigma_pattern -> Prop :=
| P1 (phi : Sigma_pattern) :
    (phi ~> phi) tautology

| P2 (phi psi : Sigma_pattern) :
    (phi ~> (psi ~> phi)) tautology

| P3 (phi psi xi : Sigma_pattern) :
    ((phi ~> (psi ~> xi)) ~> ((phi ~> psi) ~> (phi ~> xi))) tautology

| P4 (phi psi : Sigma_pattern) :
    (((¬ phi) ~> (¬ psi)) ~> (psi ~> phi)) tautology
where "pattern 'tautology'" := (Tautology_proof_rules pattern).

(* Auxiliary axiom schemes for FOL resoning *)
Inductive Hilbert_style_proof : Sigma_pattern -> Prop :=
| P4m (phi psi : Sigma_pattern) :
    Hilbert_style_proof ((phi ~> psi) ~> ((phi ~> ¬psi) ~> ¬phi))

| P4i (phi : Sigma_pattern) :
    Hilbert_style_proof ((phi ~> ¬phi) ~> ¬phi)

| P5i (phi psi : Sigma_pattern) :
    Hilbert_style_proof (¬phi ~> (phi ~> psi))

| Q5 (phi t : Sigma_pattern) (x : EVar) :
    Hilbert_style_proof (all x, phi ~> (e_subst_var phi t x))

| Q6 (phi psi : Sigma_pattern) (x : EVar) :
    Hilbert_style_proof
      ((all x, (phi ~> psi)) ~> ((all x, phi) ~> (all x, psi)))

(* Rule to embed tautology axiom schemes *)
| Taut (pattern : Sigma_pattern):
    pattern tautology -> Hilbert_style_proof pattern
.

(* Proof system rules:
 * these can be used duting a proof by instantiating them *)
Reserved Notation "pattern 'proved'" (at level 2).
Inductive AML_proof_system : Sigma_pattern -> Prop :=
(* FOL reasoning *)
  (* Propositional tautology *)
  | Prop_tau (phi : Sigma_pattern) :
      phi tautology -> phi proved

  (* Modus ponens *)
  | Mod_pon {phi1 phi2 : Sigma_pattern} :
    phi1 proved -> (phi1 ~> phi2) proved -> phi2 proved

  (* Existential quantifier *)
  | Ex_quan {phi : Sigma_pattern} (x y : EVar) :
    ((e_subst_var phi (sp_var y) x) ~> (sp_exists x phi)) proved

  (* Existential generalization *)
  | Ex_gen (phi1 phi2 : Sigma_pattern) (x : EVar) :
    (phi1 ~> phi2) proved ->
    negb (set_mem evar_eq_dec x (free_vars phi2)) = true ->
    ((ex x, phi1) ~> phi2) proved

(* Frame reasoning *)
  (* Propagation bottom *)
  | Prop_bot (C : Application_context) :
    ((subst_ctx C sp_bottom) ~> sp_bottom) proved

  (* Propagation disjunction *)
  | Prop_disj (C : Application_context) (phi1 phi2 : Sigma_pattern) :
    ((subst_ctx C (phi1 _|_ phi2)) ~>
        ((subst_ctx C phi1) _|_ (subst_ctx C phi2))) proved

  (* Propagation exist *)
  | Prop_ex (C : Application_context) (phi : Sigma_pattern) (x : EVar) :
    negb (set_mem evar_eq_dec x (free_vars_ctx C)) = true ->
    ((subst_ctx C (sp_exists x phi)) ~> (sp_exists x (subst_ctx C phi))) proved

  (* Framing *)
  | Framing (C : Application_context) (phi1 phi2 : Sigma_pattern) :
    (phi1 ~> phi2) proved -> ((subst_ctx C phi1) ~> (subst_ctx C phi2)) proved

(* Fixpoint reasoning *)
  (* Set Variable Substitution *)
  | Svar_subst (phi : Sigma_pattern) (psi X : SVar) :
    phi proved -> (e_subst_set phi (sp_set psi) X) proved

  (* Pre-Fixpoint *)
  | Pre_fixp (phi : Sigma_pattern) (X : SVar) :
    ((e_subst_set phi (sp_mu X phi) X) ~> (sp_mu X phi)) proved

  (* Knaster-Tarski *)
  | Knaster_tarski (phi psi : Sigma_pattern) (X : SVar) :
    ((e_subst_set phi psi X) ~> psi) proved -> ((sp_mu X phi) ~> psi) proved

(* Technical rules *)
  (* Existence *)
  | Existence (x : EVar) : (ex x , ' x) proved

  (* Singleton *)
  | Singleton (C1 C2 : Application_context) (x : EVar) (phi : Sigma_pattern) :
    (¬ ((subst_ctx C1 ('x _&_ phi)) _&_ (subst_ctx C2 ('x _&_ (¬ phi))))) proved

(* Auxiliary rule *)
(*   | Use_as_axiom (axiom : Sigma_pattern) :
      axiom proved *)
where "pattern 'proved'" := (AML_proof_system pattern).

Lemma A_impl_A (A : Sigma_pattern) : (A ~> A) proved.
Proof.
  pose(_1' := P3 A (A ~> A) A).
  pose(_2' := P2 A (A ~> A)).
  pose(_4' := P2 A A).

  pose(_1 := Prop_tau ((A ~> (A ~> A) ~> A) ~> (A ~> A ~> A) ~> A ~> A) _1').
  pose(_2 := Prop_tau (A ~> (A ~> A) ~> A) _2').
  pose(_3 := Mod_pon _2 _1).
  pose(_4 := Prop_tau (A ~> A ~> A) _4').
  pose(_5 := Mod_pon _4 _3).
  exact _5.
Qed.

Theorem A_impl_A_equiv : forall A : Sigma_pattern,
  (A_impl_A A) = (Prop_tau (A ~> A) (P1 A)).
Proof.
  intros.
  induction A.
Admitted.

Check Ensembles.Singleton Sigma_pattern.
Definition empty_theory := Empty_set Sigma_pattern.

(* TODO: Define provability *)
Reserved Notation "theory |- pattern" (at level 40).
Inductive Provable : Ensemble Sigma_pattern -> Sigma_pattern -> Prop :=
(* Deduction theorem: inject axiom from theory *)
| inject {axiom pattern : Sigma_pattern} (theory : Ensemble Sigma_pattern) :
    In _ theory axiom -> theory |- pattern ->
    (Subtract _ theory axiom) |- (axiom ~> pattern)

(* Deduction theorem: extract back to theory *)
| extract (phi1 phi2 : Sigma_pattern) (theory : Ensemble Sigma_pattern) :
    (theory |- (phi1 ~> phi2)) ->
    (Add _ theory phi1) |- phi2

(* Using hypothesis from theory *)
| hypothesis (axiom : Sigma_pattern) (theory : Ensemble Sigma_pattern) :
    (* set_mem sp_eq_dec axiom theory = true *)
    (In _ theory axiom) -> theory |- axiom

(* AML_proof_system rule embedding *)

(* Introduce axiom rules *)
| empty (pattern : Sigma_pattern) :
    (pattern proved) -> empty_theory |- pattern

| ext (pattern : Sigma_pattern) (theory : Ensemble Sigma_pattern) :
    pattern proved -> theory |- pattern

(* Introduce step rules *)
| E_mod_pon (phi1 phi2 : Sigma_pattern) (theory : Ensemble Sigma_pattern) :
    (* T1 subsests T2 or T2 substes T1 or are equal *)
    theory |- phi1 -> theory |- (phi1 ~> phi2) -> theory |- phi2

| E_ex_gen (phi1 phi2 : Sigma_pattern) (theory : Ensemble Sigma_pattern) :
    theory |- (phi1 ~> phi2) ->
    negb (set_mem evar_eq_dec x (free_vars phi2)) = true ->
    theory |- ((ex x, phi1) ~> phi2)

| E_framing
  (C : Application_context) (phi1 phi2 : Sigma_pattern)
  (theory : Ensemble Sigma_pattern) :
    theory |-
      (phi1 ~> phi2) -> theory |- ((subst_ctx C phi1) ~> (subst_ctx C phi2))

| E_svar_subst
  (phi : Sigma_pattern) (psi X : SVar) (theory : Ensemble Sigma_pattern) :
    theory |- phi -> theory |- (e_subst_set phi (sp_set psi) X)

| E_knaster_tarski
  (phi psi : Sigma_pattern) (X : SVar) (theory : Ensemble Sigma_pattern) :
    theory |-
      ((e_subst_set phi psi X) ~> psi) -> theory |- ((sp_mu X phi) ~> psi)

(* Proposition 7: definedness related properties *)
| E_id (phi : Sigma_pattern) (theory : Ensemble Sigma_pattern) :
    theory |- (phi ~=~ phi)

| E_trans (phi1 phi2 phi3 : Sigma_pattern) (theory : Ensemble Sigma_pattern) :
    theory |- (phi1 ~=~ phi2) -> theory |- (phi2 ~=~ phi3) ->
    theory |- (phi1 ~=~ phi3)

| E_symm (phi1 phi2 : Sigma_pattern)  (theory : Ensemble Sigma_pattern) :
    theory |- (phi1 ~=~ phi2) -> theory |- (phi2 ~=~ phi1)

| E_evar_subst
  (* TODO: psi can be any pattern, not only Application_context *)
  (x : EVar) (phi1 phi2 psi : Sigma_pattern) (theory : Ensemble Sigma_pattern) :
    theory |- (phi1 ~=~ phi2) ->
    theory |- ((e_subst_var psi phi1 x) ~=~ (e_subst_var psi phi2 x))

where "theory |- pattern" := (Provable theory pattern).

(* Examples of use *)
(* Notation "[ x ; y ; .. ; z ]" := (cons _ x _ (cons _ y _ .. (cons _ z _ (nil _)) ..))  *)

(* TODO: Notation "'{{' a 'add' b 'add' .. 'add' z '}}'" := (Add _ a (Add _ b .. (Add _ z) ..))
  (at level 2). *)

Lemma not_not_A_proves_A : forall A : Sigma_pattern,
  (Add _ (Add _ empty_theory (¬(¬A)))
         ((¬A ~> ¬A) ~> (¬A ~> ¬(¬A)) ~> A) ) |- A.
Proof.
  intro A.

  pose(theory := (Add _ (Add _ empty_theory (¬(¬A)))
                 ((¬A ~> ¬A) ~> (¬A ~> ¬(¬A)) ~> A) )).

(*   pose(_1 := hypothesis (¬(¬A)) theory). (* getting axiom from hypothesises *)
  pose(_2 := ext (¬A ~> ¬A) theory (Prop_tau (¬A ~> ¬A) (P1 (¬A)))).
  pose(_3 := Mod_pon _2 _1).
  pose(_4 := Prop_tau (¬(¬A)) ~> (¬A ~> (¬(¬A))) (P2 (¬(¬A)) (¬A)).
  pose(_5 := _) (* getting axiom from hypothesises *)
  pose(_6 := Mod_pon _5 _4).
  pose(_7 := Mod_pon _6 _3). *)

  eapply E_mod_pon.
  - eapply E_mod_pon.
    * eapply (hypothesis (¬(¬A)) theory).
        (* TODO: write a tactic for this *)
      + unfold theory. unfold In in *. unfold Add.
        eapply Union_introl. eapply Union_intror. reflexivity.
    * eapply (ext ((¬(¬A)) ~> (¬A ~> ¬(¬A))) theory).
      + eapply (Prop_tau ((¬(¬A)) ~> (¬A ~> ¬(¬A)))).
        eapply (P2 (¬(¬A)) (¬A)).
  - eapply E_mod_pon.
    * eapply (ext (¬A ~> ¬A) theory (Prop_tau (¬A ~> ¬A) (P1 (¬A)))).
    * eapply (hypothesis ((¬A ~> ¬A) ~> (¬A ~> ¬(¬A)) ~> A)).
      + unfold Add. eapply Union_intror. reflexivity.
Qed.


Lemma empty_proves_A_impl_A (A : Sigma_pattern) : empty_theory |- (A ~> A).
Proof.
  eapply E_mod_pon.
  - eapply (empty (A ~> A ~> A) (Prop_tau (A ~> A ~> A) (P2 A A))).
  - eapply E_mod_pon.
    + eapply (empty (A ~> (A ~> A) ~> A)
                    (Prop_tau (A ~> (A ~> A) ~> A) (P2 A (A ~> A)))).
    + eapply (empty ((A ~> (A ~> A) ~> A) ~> (A ~> A ~> A) ~> A ~> A)
                    (Prop_tau ((A ~> (A ~> A) ~> A) ~> (A ~> A ~> A) ~> A ~> A)
                      (P3 A (A ~> A) A))).
Qed.


(* Theorem 8.: Soundness *)
Theorem Soundness :
  forall phi : Sigma_pattern, forall theory : Ensemble Sigma_pattern,
  (theory |- phi) -> (theory |= phi).
(* Proof.
  intros.
              TODO
  induction (proof_length (theory |= phi)). *)
Admitted.

Theorem Completeness :
  forall phi : Sigma_pattern, forall theory : Ensemble Sigma_pattern,
  (theory |= phi) -> (theory |- phi).
Abort.

(* ****************************New paper version**************************** *)

(* Definition 9. MSFOL definition *)
(* record MSFOL_Signature := {
  SortSet : Type
  Functions : SortSet* -> SortSet
  Predicates : SortSet*
}. *)

Inductive MSFOL_sorts : Set :=
| Nat
| List
| Cfg
| Term
.

Inductive MSFOL_var : Type :=
| M_var_c (id_M_var : string) (sort_M_var : MSFOL_sorts).
Inductive MSFOL_fun : Type := M_fun_c {id_M_fun : string}.

Definition msort_eq_dec : forall (x y : MSFOL_sorts), { x = y } + { x <> y }.
Proof. decide equality. Defined.

Definition mvar_eq_dec : forall (x y : MSFOL_var), { x = y } + { x <> y }.
Proof.
  decide equality.
  exact (msort_eq_dec sort_M_var sort_M_var0).
  exact (string_dec id_M_var id_M_var0).
Defined.

Inductive MSFOL_term : Type :=
| MT_var (x_s : MSFOL_var)
| MT_fun (f : MSFOL_fun) {n : nat} (params : VectorDef.t MSFOL_term n)
         (result_sort : MSFOL_sorts)
.

Inductive MSFOL_pred : Type := M_pred_c {id_M_pred : string}.

Inductive MSFOL_formula : Set :=
| MF_pred (p : MSFOL_pred) {n : nat} (params : VectorDef.t MSFOL_term n)
| MF_bottom
| MF_impl (l r : MSFOL_formula)
| MF_exists (x : MSFOL_var) (phi : MSFOL_formula)
.

Notation "'M_Bot'" := (MF_bottom).
Notation "a 'M~>' b" := (MF_impl a b) (at level 90, right associativity,
                                       b at level 200).
Notation "'M_ex' x , phi" := (MF_exists x phi) (at level 55).

(* Derived notations *)
Definition MF_not (phi : MSFOL_formula) := phi M~> M_Bot.
Notation "'M¬' phi" := (MF_not phi) (at level 75).

Definition MF_or  (l r : MSFOL_formula) := (M¬ l) M~> r.
Notation "a M|_ b" := (MF_or a b) (at level 85, right associativity).

Definition MF_and (l r : MSFOL_formula) := M¬ ((M¬ l) M|_ (M¬ r)).
Notation "a M&_ b" := (MF_and a b) (at level 80, right associativity).

Definition MF_iff (l r : MSFOL_formula) := ((l M~> r) M&_ (l M~> r)).
Notation "a <M~> b" := (MF_iff a b) (at level 95, no associativity).

Definition MF_top := (M¬ MF_bottom).
Notation "'M_Top'" := MF_top.

Definition MF_forall (x : MSFOL_var) (phi : MSFOL_formula) :=
  M¬ (MF_exists x (M¬ phi)).
Notation "'M_all' x , phi" := (MF_forall x phi) (at level 55).

(* auxiliaty functions for equality checking *)
Definition MSFOL_sorts_eqb (a b : MSFOL_sorts) : bool :=
match a, b with
| Nat, Nat => true
| List, List => true
| Cfg, Cfg => true
| Term, Term => true
| _, _ => false
end.

(* Definition mvar_eq (x y : MSFOL_var) : bool :=
match x, y with
| (M_var_c id_x sort_x), (M_var_c id_y sort_y) =>
    andb (String.eqb id_x id_y) (MSFOL_sorts_eqb sort_x sort_y)
end. *)


(* Substitue varibale in term *)
Fixpoint t_subst_var (term : MSFOL_term) (t : MSFOL_term) (x : MSFOL_var)
: MSFOL_term :=
match term with
| MT_var x' => if mvar_eq_dec x x' then t else (MT_var x')
| MT_fun f params result_sort =>
    MT_fun f (VectorDef.map (fun y => t_subst_var y t x) params) result_sort
end.

(* Substitue varibale in formula *)
Fixpoint f_subst_var (phi : MSFOL_formula) (t : MSFOL_term) (x : MSFOL_var)
: MSFOL_formula :=
match phi with
| MF_pred p params =>
    MF_pred p (VectorDef.map (fun y => t_subst_var y t x) params)
| MF_bottom => MF_bottom
| MF_impl lhs rhs => MF_impl (f_subst_var lhs t x) (f_subst_var rhs t x)
| MF_exists x' formula => if mvar_eq_dec x x'
                          then M_ex x', formula
                          else M_ex x', (f_subst_var formula t x)
end.


Definition M_set_singleton := fun x => set_add mvar_eq_dec x List.nil.

Fixpoint var_to_set (term : MSFOL_term)
: ListSet.set MSFOL_var -> ListSet.set MSFOL_var :=
match term with
| MT_var x' => set_add mvar_eq_dec x'
| MT_fun f _ _ => set_union mvar_eq_dec (empty_set MSFOL_var)
end.

(* free variables of a formula *)
Fixpoint f_free_vars (phi : MSFOL_formula) : (ListSet.set MSFOL_var) :=
match phi with
| MF_pred p params =>
    VectorDef.fold_right var_to_set params (empty_set MSFOL_var)
| MF_bottom => List.nil
| MF_impl lhs rhs => set_union mvar_eq_dec (f_free_vars lhs) (f_free_vars rhs)
| MF_exists y phi' => set_diff mvar_eq_dec (f_free_vars phi') (M_set_singleton y)
end.


(* record MSFOL_structure := {
  Domain : SortType (* subset of SortSet *)
  Function_interp : MSFOL_fun -> Domain* -> Domain -> value_type?
  Predicate_interp : MSFOL_pred -> Domain* -> value_type?
}. *)

(* Fixpoint MSFOL_term_valuation (t : MSFOL_term) : MSFOL_sorts :=
match t with
| MT_var x => (* result will have type: match x with M_var_c name sort => sort end *)
| MT_fun f params r_sort => (* result will have type: r_sort *)
end.

Fixpoint MSFOL_formula_valuation (formula : MSFOL_formula) : bool :=
match formula with
| MF_pred p params => ?
| MF_bottom => false
| MF_impl phi1 phi2 =>
    not (MSFOL_formula_valuation phi1) /\ (MSFOL_formula_valuation phi2)
| MP_exists x phi => ?
. *)

(* Deifinition satisfies_model (A : ?) (phi : MSFOL_formula) : Prop :=
  forall valutaion : ?, valuation phi A = true. *)

(* Definition satisfies_theory (A : ?) (Omega : Ensemle MSFOL_formula) : Prop :=
  forall axiom : MSFOL_formula, In _ axiom A -> satisfies_model A axiom. *)

(* Definition satisfies
(Omega : Ensemble MSFOL_formula) (phi : MSFOL_formula) : Prop :=
  forall A : ?, satisfies_theory A Omega -> stisfies_model A phi. *)

(* Auxiliary axiom schemes for proving propositional tautology *)
Reserved Notation "pattern 'MSFOL_tautology'" (at level 2).
Inductive MSFOL_tautology_proof_rules : MSFOL_formula -> Prop :=
| MSFOL_p1 (phi : MSFOL_formula) :
    (phi M~> phi) MSFOL_tautology

| MSFOL_p2 (phi psi : MSFOL_formula) :
    (phi M~> (psi M~> phi)) MSFOL_tautology

| MSFOL_p3 (phi psi xi : MSFOL_formula) :
    ((phi M~> (psi M~> xi)) M~> ((phi M~> psi) M~> (phi M~> xi))) MSFOL_tautology

| MSFOL_p4 (phi psi : MSFOL_formula) :
    (((M¬ phi) M~> (M¬ psi)) M~> (psi M~> phi)) MSFOL_tautology

where "pattern 'MSFOL_tautology'" := (MSFOL_tautology_proof_rules pattern).

Reserved Notation "pattern 'MSFOL_proved'" (at level 2).
Inductive MSFOL_proof_system : MSFOL_formula -> Prop :=
(* Propositional tautology *)
| MSFOL_prop_tau (phi : MSFOL_formula) :
    phi MSFOL_tautology -> phi MSFOL_proved

(* Modus ponens *)
| MSFOL_mod_pon {phi1 phi2 : MSFOL_formula} :
    phi1 MSFOL_proved -> (phi1 M~> phi2) MSFOL_proved -> phi2 MSFOL_proved

(* Existential quantifier *)
| MSFOL_ex_quan {phi : MSFOL_formula} {x : MSFOL_var} {t : MSFOL_term}:
    ((f_subst_var phi t x) M~> (M_ex x, phi)) MSFOL_proved

(* Existential generalization *)
| MSFOL_ex_gen (phi1 phi2 : MSFOL_formula) (x : MSFOL_var) :
    (phi1 M~> phi2) MSFOL_proved ->
    negb (set_mem mvar_eq_dec x (f_free_vars phi2)) = true ->
    ((M_ex x, phi1) M~> phi2) MSFOL_proved

where "phi 'MSFOL_proved'" := (MSFOL_proof_system phi).


(* Section 4.2 *)
Definition MSAFOL_Sort := const ("Sort").

(* a function which corresponds: constants of AML  to  sorts of MSFOL *)
Fixpoint sort_fun_constant (s : MSFOL_sorts) : Sigma_pattern :=
match s with
| Nat  => Functional_Constant (sigma_c("Nat"))
| List => Functional_Constant (sigma_c("List"))
| Cfg  => Functional_Constant (sigma_c("Cfg"))
| Term => Functional_Constant (sigma_c("Term"))
end.

Fixpoint sort_constant (s : MSFOL_sorts) : Sigma :=
match s with
| Nat  => (sigma_c("Nat"))
| List => (sigma_c("List"))
| Cfg  => (sigma_c("Cfg"))
| Term => (sigma_c("Term"))
end.

Definition Axiom_Sort (s : MSFOL_sorts) := (sort_constant s) -< MSAFOL_Sort.


Definition Domain_Symbol := const ("Domain symbol").
Definition Domain (sort : MSFOL_sorts) := Domain_Symbol $ ^(sort_constant sort).
Notation "'[[' s ']]'" := (Domain s) (at level 0).

(* Examples meanings: *)
(* x =< [[ s ]] states that x has sort s *)
Definition x_has_sort_s (x : EVar) (s : MSFOL_sorts) :=
  x =< [[ s ]].

(* phi <: [[ s ]] states that all elements matching phi have sort s*)
Definition pattern_has_sort (phi : Sigma_pattern) (s : MSFOL_sorts) :=
  phi <: [[ s ]].

Definition Nonempty_Domain (sort : MSFOL_sorts) :=  [[ sort ]] !=~ sp_bottom.

(* Introducing notations for Sorted quantification *)
(* For denoting "exists x : Nat . pattern" we introduce: *)
Notation "'ex_S' x : sort , phi" :=
  (sp_exists x ((x =< ([[ sort ]])) _&_ phi)) (at level 3, x at next level, sort at next level).
(* For denoting "forall x : Nat . pattern" we introduce: *)
Notation "'all_S' x : sort , phi" :=
  (sp_forall x ((x =< ([[ sort ]])) ~> phi)) (at level 3, x at next level, sort at next level).


(* Proposition 10. *)
Reserved Notation "a |--> b" (at level 40, left associativity).
Inductive QuantificationEquivalence : Sigma_pattern -> Sigma_pattern -> Prop :=
| QE_ex_to_all (x : EVar) (s : MSFOL_sorts) (phi : Sigma_pattern) :
    ((ex_S x : s, phi) |--> (¬ (all_S x : s, (¬ phi))))
| QE_all_to_ex (x : EVar) (s : MSFOL_sorts) (phi : Sigma_pattern) :
    ((all_S x : s, phi)  |--> (¬ (ex_S x : s, (¬ phi))))
where "a |--> b" := (QuantificationEquivalence a b).

Lemma forall_ex_equiv :
  forall s : MSFOL_sorts, forall x : EVar, forall phi : Sigma_pattern,
  empty_theory |- ((all_S x:s, phi) ~=~ (¬ (ex_S x:s, (¬ phi)))).
Admitted.


(* Many-sorted functions and terms *)
Section NatToStringConversion.

Local Open Scope string_scope.
Local Open Scope nat_scope.
Fixpoint string_of_nat_aux (time n : nat) (acc : string) : string :=
  let d := match Nat.modulo n 10 with
             | 0 => "0" | 1 => "1" | 2 => "2" | 3 => "3" | 4 => "4"
             | 5 => "5" | 6 => "6" | 7 => "7" | 8 => "8" | _ => "9"
           end in
  let acc' := d ++ acc in
  match time with
    | 0 => acc'
    | S time' =>
      match Nat.div n 10 with
        | 0 => acc'
        | n' => string_of_nat_aux time' n' acc'
      end
  end.

Definition string_of_nat (n : nat) : string := string_of_nat_aux n n "".

End NatToStringConversion.

Definition vc := VectorDef.cons.
Definition vn := VectorDef.nil.

Fixpoint _of_nat (n : nat) {m : nat} : Fin.t (S (n + m)) :=
match n with
 | O   => F1
 | S x => FS (_of_nat x)
end.

Program Fixpoint _gen_x_vec (n m : nat) : VectorDef.t EVar n :=
match n with
| O => (vn EVar)
| S n' => vc EVar (evar_c(String.append "x" (string_of_nat(m-n+1))))
            n' (_gen_x_vec n' m)
end.

Fixpoint gen_x_vec (n : nat) : VectorDef.t EVar n :=
  _gen_x_vec n n.

Fixpoint Function
  {n : nat} (fn : Sigma) (sorts : VectorDef.t MSFOL_sorts n) 
  (y_sort : MSFOL_sorts)
: Sigma_pattern :=
let vars := gen_x_vec n in
let var_patterns := VectorDef.map sp_var vars in
let applied_params := VectorDef.fold_left sp_app (sp_const fn) var_patterns in
let core := ex_S (evar_c("y")) : y_sort, (applied_params ~=~ (var ("y")) )in
let foralls := VectorDef.map2
                (fun var s => (fun phi => all_S var : s, phi))
                vars sorts in
  VectorDef.fold_right (fun spl spr => spl spr) foralls core.

(* Functional notation of the function *)
Notation "f : '-->' s" := (Function f (vn _) s) (at level 3).
Notation "f : s1 '-->' s" := (Function f (vc _ s1 0 (vn _)) s) (at level 3).
Notation "f : s1 'X' s2 'X' .. 'X' sn '-->' s" :=
  (Function f (vc _ s1 _ (vc _ s2 _ .. (vc _ sn _ (vn _)) .. )) s) (at level 3).

(* Example for functional notation *)
Definition f := (sigma_c "f") : --> List.
Definition fib := (sigma_c "fib") : Nat --> Nat.
Definition volume := (sigma_c "volume") : Nat X Nat --> Nat.


(* Many-sorted predicates and formulas *)
Definition Predicate
  {n : nat} (fn : Sigma) (sorts : VectorDef.t MSFOL_sorts n)
: Sigma_pattern :=
let vars := gen_x_vec n in
let var_patterns := VectorDef.map sp_var vars in
let applied_params := VectorDef.fold_left sp_app (sp_const fn) var_patterns in
let or_left := applied_params ~=~ Top in
let or_right := applied_params ~=~ Bot in
let core := or_left _|_ or_right in
let foralls := VectorDef.map2
                (fun var s => (fun phi => (all_S var : s, phi)))
                vars sorts in
  VectorDef.fold_right (fun spl spr => spl spr) foralls core.


(* well-sorted axiom scheme *)
Fixpoint get_vars (term : MSFOL_term) : Sigma_pattern -> Sigma_pattern :=
match term with
| MT_var x => match x with
    M_var_c id sort => sp_and ((evar_c(id)) =< [[ sort ]]) end
| MT_fun f params r_sort => VectorDef.fold_right get_vars params
end.

Fixpoint well_sorted_term (term : MSFOL_term) : Sigma_pattern :=
match term with
| MT_var x => match x with M_var_c id sort => ((evar_c(id)) =< [[ sort ]]) end
| MT_fun f params r_sort => VectorDef.fold_right get_vars params Top
end.

Fixpoint well_sorted_formula (formula : MSFOL_formula) : Sigma_pattern :=
match formula with
| MF_pred p params => VectorDef.fold_right get_vars params Top
| MF_bottom => Top
| MF_impl lhs rhs => sp_and (well_sorted_formula lhs) (well_sorted_formula rhs)
| MF_exists x phi =>
    sp_and (match x with M_var_c id sort => ((evar_c(id)) =< [[ sort ]]) end)
           (well_sorted_formula phi)
end.

(* Fixpoint and_gen {n : nat} (vec : VectorDef.t Sigma_pattern n)
: Sigma_pattern :=
match vec with
| VectorDef.nil  _                          => sp_top (* TODO: sp_top? *)
| VectorDef.cons _ elem _ (VectorDef.nil _) => elem
| VectorDef.cons _ elem _ rem               => elem _&_ (and_gen rem)
end.

Definition _well_sorted
  {n : nat} (vars : VectorDef.t EVar n) (sorts : VectorDef.t MSA_sorts n)
: Sigma_pattern :=
let domains := VectorDef.map Domain sorts in
let assoc := VectorDef.map2 Membership vars domains in
  and_gen assoc. *)

(* TODO: fix this and ask how to get types?
        Answer: from MSFOL format of variables, because they have the form of x:s
 *)(* Definition ws
  (phi : Sigma_pattern) {n : nat} (sorts : VectorDef.t MSA_sorts n) :=
let vars := of_list (free_vars phi) in
  _well_sorted vars sorts. *)


(* TODO: MSFOL theory conversion to AML conversion *)


(* Proposition 12. *)
Fixpoint M_var_id (var : MSFOL_var) : string :=
match var with M_var_c id _ => id end.

Fixpoint M_var_sort (var : MSFOL_var) : MSFOL_sorts :=
match var with M_var_c _ sort => sort end.

Fixpoint term_sort (term : MSFOL_term) : MSFOL_sorts :=
match term with
| MT_var x => match x with M_var_c _ sort => sort end
| MT_fun _ _ result_sort => result_sort
end.

Fixpoint term_to_AML (term : MSFOL_term) : Sigma_pattern:=
match term with
| MT_var x => match x with M_var_c id _ => var id end
| MT_fun f_id params result_sort =>
    match f_id with (M_fun_c id) =>
      Function (sigma_c id)
               (VectorDef.map term_sort params)
               result_sort
    end
end.

Fixpoint formula_to_AML (formula : MSFOL_formula) : Sigma_pattern :=
match formula with
| MF_pred p params => 
    match p with M_pred_c id =>
      Predicate (sigma_c id) (VectorDef.map term_sort params)
    end
| MF_bottom => Bot
| MF_impl lhs rhs => (formula_to_AML lhs) ~> (formula_to_AML rhs)
| MF_exists x phi =>
    ex_S (evar_c (M_var_id x)) : (M_var_sort x) , (formula_to_AML phi)
end.


Lemma MSFOL_wellformed_terms :
  forall Gamma_MSFOL : Ensemble Sigma_pattern, forall t : MSFOL_term,
  Gamma_MSFOL |- ((well_sorted_term t) ~>
    ex_S (evar_c("y")) : (term_sort t), (term_to_AML t) ~=~ (var "y")).
Admitted.

Lemma MSFOL_wellformed_formulas :
  forall Gamma_MSFOL : Ensemble Sigma_pattern, forall phi : MSFOL_formula,
  Gamma_MSFOL |- ((well_sorted_formula phi) ~>
    ((formula_to_AML phi) ~=~ sp_top) _|_ (((formula_to_AML phi) ~=~ sp_bottom))).
Admitted.

(* MSFOL theories *)

(* Theorem 13. *)
(* Theorem preservation :
  forall Omega : Ensemble MSFOL_formula, forall Gamma : Ensemble Sigma_pattern,
  forall phi : MSFOL_formula
  Omega |-MSFOL phi -> Gamma_MSFOL |- (formula_to_AML phi). *)

(* Definition 14. MSFOL restricted *)


(* Theorem 15. *)
(* Theorem 
  forall Omega : Ensemble MSFOL_formula, forall A : MSFOL_model,
  A |=MSFOL Omega -> exists M : Sigma_model, ... *)

(* Theorem 16. *)
(* Theorem holds :
  forall Omega : Ensemble MSFOL_formula, phi : MSFOL_formula,
  let Gamma := (theory_to_AML Omega) in
    (Omega |-MSFOL phi -> Gamma |- (formula_to_AML phi)) /\
    (Gamma |- (formula_to_AML phi) -> Gamma |= (formula_to_AML phi)) /\
    (Gamma |= (formula_to_AML phi) -> Omega |=MSFOL phi) /\
    (Omega |=MSFOL phi -> Omega |-MSFOL phi).
 *)


(* ************************************************************************** *)
(*                           ~= Natural numbers =~                            *)
(* ************************************************************************** *)

Definition zero : Sigma := sigma_c("zero").
Definition succ : Sigma := sigma_c("succ").
Definition plus : Sigma := sigma_c("plus'").
Definition mult : Sigma := sigma_c("mult").

Definition zero_fun := (zero : --> Nat).
Definition succ_fun := (succ : Nat --> Nat).
Definition plus_fun := (plus : Nat X Nat --> Nat).
Definition mult_fun := (mult : Nat X Nat --> Nat).

(* Helper functions for notation *)
Definition succ' (x : Sigma_pattern) := ^succ $ x.
Definition plus' (x y : Sigma_pattern) := ^plus $ x $ y.
Definition mult' (x y : Sigma_pattern) := ^mult $ x $ y.
(* End helper functions *)

Definition No_Confusion1 (x : EVar) :=
  all_M x : Nat, ((succ' 'x) !=~ (const ("zero"))).

Definition No_Confusion2 (x y : EVar) :=
  all_M x : Nat, (all_M y : Nat,
    ((((succ' 'x) ~=~ (succ' 'y))) ~> ((' x) ~=~ (' y)))).

Definition Inductive_Domain (D : SVar) :=
  [[ Nat ]] ~=~ (mu D, ((const ("zero")) _|_ ((const ("succ")) $ `D))).

(* This is an axiom schema. Before use it needs to be instanctiated, by giving
 * a pattern as parameter to it. *)
Definition Peano_Induction (n : EVar) (phi : Sigma_pattern -> Sigma_pattern) :=
  (((phi (const ("zero"))) _&_ (all n, ((phi 'n) ~> (phi (succ' 'n))))) ~>
  (all n, (phi 'n))).

Fixpoint app_inhabitant_sets {n : nat} (vec : VectorDef.t MSA_sorts n)
: Sigma_pattern :=
match vec with
| VectorDef.nil  _ => const ("cannot operate on empty parameters")
| VectorDef.cons _ elem _ (VectorDef.nil _) => [[ elem ]]
| VectorDef.cons _ elem _ vec' =>
    ([[ elem ]]) $ (app_inhabitant_sets vec')
end.

(* Definition Arity (sigma : Sigma_pattern) {n : nat}
                 (s_vec : VectorDef.t MSA_sorts n) (s : MSA_sorts)
: Sigma_pattern :=
  sigma $ (app_inhabitant_sets s_vec) <: InhabitantSetOf(s). *)


(* Examples: *)
Definition one := succ' ^zero.
Definition two := succ' one.
Definition three := succ' two.
Definition five := succ' (succ' three).
Definition six := succ' five.


Definition plus_1_2 := plus' one two.
Definition plus_1_2_eq_3 := ((plus' one two) ~=~ three).
Definition plus_1_plus_2_3_eq_6 := ((plus' one (plus' two three)) ~=~ six).

Definition plus_x_1_eq_5 :=
  (all_M x : Nat, ((plus' 'x one) ~=~ five)).

Definition plus_x_z_eq_y :=
  (all_M x : Nat, (all_M y : Nat, (all_M z : Nat,
        ((plus' 'x 'z) ~=~ 'y)))).

Definition plus_x_plus_z_3_eq_y :=
  (all_M x : Nat, (all_M y : Nat, (all_M z : Nat,
        ((plus' 'x (plus' 'z three))) ~=~ 'y))).


(* Example: x + 0 = x *)
Definition x_plus_0_eq_x :=
(all_M x : Nat, ((plus' 'x ^zero) ~=~ 'x)).

(* we have to specify the type of function parameters, because if not, the
* following statement about natural numbers also can be formalised: *)
Definition foo := plus' ^plus ^zero.


Fixpoint SumFromZeroTo (n : Sigma_pattern) : Sigma_pattern :=
match n with
| sp_const _ => ^zero
      (* succ b *)
| sp_app _    b => plus' (succ' b) (SumFromZeroTo b)
| _ => ^(sigma_c("non-exhaustive pattern"))
end.

(* 1 + ... + n = n * (n+1) / 2. *)
Definition n := evar_c("n").
Definition Sum_of_first_n : Sigma_pattern :=
  all_M n : Nat, (mult' two (SumFromZeroTo 'n) ~=~
  mult' 'n (succ' 'n)).


Fixpoint ProdFromOneTo (n : Sigma_pattern) : Sigma_pattern :=
match n with
| sp_const _ => ^zero
      (* succ _ *)
| sp_app _    b =>
  match b with
  | sp_const _ => one
  | sp_app _ _ => mult' (succ' b) (ProdFromOneTo b)
  | _ => const ("non-exhaustive pattern")
  end
| _ => const ("non-exhaustive pattern")
end.

Fixpoint SumOfSquaresFromZeroTo (n : Sigma_pattern) : Sigma_pattern :=
match n with
| sp_const _ => ^zero
      (* succ b *)
| sp_app _    b => plus' (mult' (succ' b) (succ' b)) (SumOfSquaresFromZeroTo b)
| _ => const ("non-exhaustive pattern")
end.

(* 1^2 + ... + n^2 = n(n+1)(2*n + 1) / 6. *)
Definition Sum_of_squares :=
  all_M n : Nat, (
    mult' six (SumOfSquaresFromZeroTo 'n) ~=~
    mult' 'n (mult' (succ' 'n) (plus' (mult' two 'n) one))).


(* <= relation *)
Definition less (l r : Sigma_pattern) :=
ex_M x : Nat, (plus' l (sp_var x) ~=~ r).

Definition less_or_equal (l r : Sigma_pattern) :=
  (l ~=~ r) _|_
  (ex_M x : Nat, (plus' l (sp_var x) ~=~ r)).

(* States that if:
- zero <= zero and
- for all n of sort Nat : 0 <= (n+1)
then for all n of sort Nat states 0 <= n *)
Definition every_number_is_positive : Sigma_pattern :=
Peano_Induction n (less_or_equal (sp_const zero)).

Definition less2 (a b : Sigma_pattern) := less a (succ' b).

(* States that if:
- zero < zero + 1 and
- for all n of sort Nat : 0 < ((n+1) + 1)
then for all n of sort Nat states 0 < (n+1) *)
Definition every_successor_is_strictly_positive : Sigma_pattern :=
Peano_Induction n (less2 ^zero).

(* Proof examples *)

Lemma ex1 : proved ('x ~> 'x).
Proof. apply E_prop_tau1. Qed.

Lemma ex2 : proved (sp_bottom ~> ((sp_var x) ~> sp_bottom)).
Proof. apply E_prop_tau2. Qed.

Lemma ex3 : proved (('x ~> ('y ~> 'z)) ~> (('x ~> 'y) ~> ('x ~> 'z))).
Proof. apply E_prop_tau3. Qed.

Lemma ex4 : proved (((sp_not 'x) ~> (sp_not 'y)) ~> ('y ~> 'x)).
Proof. apply E_prop_tau4. Qed.

(* Lemma ex5 : (proved 'x) -> (proved (' x ~> ' y)) -> (proved ' y).
Proof. apply (E_mod_pon 'x 'y). Qed. *)

Lemma ex6 : proved (e_subst_var sp_bottom 'y x ~> sp_exists x sp_bottom).
Proof. apply E_ex_quan. Qed.

Lemma ex7 :
  proved ('x ~> 'y) ->
  negb (set_mem evar_eq_dec z (free_vars 'y)) = true ->
  proved (ex z, 'x ~> 'y).
Proof. apply E_ex_gen. Qed.

(* TODO Ltac. *)

Lemma plus_x_0_eq_x : proved ( x_plus_0_eq_x ).
Proof.
(*   unfold x_plus_0_eq_x.
  pose(A := ((plus' 'x ^ zero ~=~ 'x) _&_ (plus' (succ' 'x) ^ zero ~=~ (succ' 'x)))).
  pose(gA := proved A). *)

(*   pose(BA := proved (Peano_Induction x (fun x => plus' x ^ zero ~=~ x))).
  pose(result := (E_mod_pon A BA)). *)
Admitted.

(* Lemma C3 (A B : Sigma_pattern) :
(*   proved (((sp_not A) ~> B) ~> (((sp_not A) ~> (sp_not B)) ~> A)). *)
Proof. *)
(*   pose(_1 := (E_prop_tau2 ((sp_not A) ~> B) ((sp_not A) ~> (sp_not B)))). *)

(* Lemma nn_A_imp_A (A : Sigma_pattern) (nna : proved (sp_not (sp_not A))) : proved ((sp_not (sp_not A)) ~> A).
Proof.
  pose(_1 := (E_prop_tau1 (sp_not (sp_not A)))).

  pose(_2 := E_prop_tau2 (sp_not (sp_not A)) (sp_not (sp_not (sp_not (sp_not A)))) ).

 Check E_mod_pon _ _2.
  pose()

  pose(_2 := (E_mod_pon  _  _1)).

  pose(_1 := (      A (sp_not A))).
  pose(_2 := (A_impl_A (sp_not A))).
  pose(_3 := (E_mod_pon _1 _2)).
 *)

(* Definition x := evar_c("x"). *)
(* Lemma ex : proved x_plus_0_eq_x.
Proof.
  unfold x_plus_0_eq_x. unfold sp_forall. unfold sp_not.

  pose(ex := sp_exists x ((x -< InhabitantSetOf Nat ~> (plus' ' x ^ zero ~=~ ' x)) ~> sp_bottom) ~> sp_bottom).
  pose(_1 := (E_ex_gen ex sp_bottom x)).

  eapply E_ex_gen.
  pose(ex := )
  - eapply E_mod_pon.
    + eapply E_
Qed. *)

(* TODO:
    commutativity
    n + 0 = n    -> by induction *)

End AML.
