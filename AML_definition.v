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

Definition evar_eq_dec : forall (x y : EVar), { x = y } + { x <> y }.
Proof. decide equality. exact (string_dec id_ev0 id_ev1). Defined.

Definition svar_eq_dec : forall (x y : SVar), { x = y } + { x <> y }.
Proof. decide equality. exact (string_dec id_sv0 id_sv1). Defined.

Definition sigma_eq_dec : forall (x y : Sigma), { x = y } + { x <> y }.
Proof. decide equality. exact (string_dec id_si0 id_si1). Defined.

Definition evar_eqb (x y : EVar) : bool := String.eqb (id_ev x) (id_ev y).
Definition svar_eqb (x y : SVar) : bool := String.eqb (id_sv x) (id_sv y).
Definition sigma_eqb (x y : Sigma) : bool := String.eqb (id_si x) (id_si y).

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

(* Derived operators *)
Notation "a _._ b" := (sp_app   a b) (at level 50, left associativity).

Notation "a ~> b"  := (sp_impl  a b) (at level 90, right associativity,
                                      b at level 200).

Definition sp_not (phi : Sigma_pattern) := phi ~> sp_bottom.
Notation "¬ a"     := (sp_not   a  ) (at level 75).

Definition sp_or  (l r : Sigma_pattern) := (¬ l) ~> r.
Notation "a _|_ b" := (sp_or    a b) (at level 85, right associativity).

Definition sp_and (l r : Sigma_pattern) := ¬ ((¬ l) _|_ (¬ r)).
Notation "a _&_ b" := (sp_and   a b) (at level 80, right associativity).

Definition sp_iff (l r : Sigma_pattern) := ((l ~> r) _&_ (l ~> r)).
Notation "a <~> b" := (sp_iff a b) (at level 95, no associativity).

Definition sp_top := (¬ sp_bottom).
Definition sp_forall (x : EVar) (phi : Sigma_pattern) :=
  ¬ (sp_exists x (¬ phi)).
Definition sp_nu (X : SVar) (phi : Sigma_pattern) :=
  ¬ (sp_mu X (¬ (e_subst_set phi (¬ (sp_set X)) X))).
(* End of derived operators *)



Definition var (name : string) : Sigma_pattern := sp_var (evar_c name).
Definition set (name : string) : Sigma_pattern := sp_set (svar_c name).
Definition const (name : string) : Sigma_pattern := sp_const (sigma_c name).

Definition evar_eq (x y : EVar) : bool :=
match x, y with
| evar_c id_x, evar_c id_y => String.eqb id_x id_y
end.

Fixpoint free_vars (phi : Sigma_pattern) : (ListSet.set EVar) :=
match phi with
| sp_var x => set_add evar_eq_dec x List.nil
| sp_set X => List.nil
| sp_const sigma => List.nil
| sp_app phi1 phi2 => set_union evar_eq_dec (free_vars phi1) (free_vars phi2)
| sp_bottom => List.nil
| sp_impl phi1 phi2 => set_union evar_eq_dec (free_vars phi1) (free_vars phi2)
| sp_exists y phi =>
    set_diff evar_eq_dec
      (free_vars phi)
      (set_add evar_eq_dec y List.nil)
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
| sp_mu X sp => mu
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
  (nu (fun S => ext_valuation evar_val (change_val svar_eqb X S svar_val) sp)).
Proof.
proof_ext_val.
unfold mu. unfold nu. unfold FA_Union_cond. unfold FA_Inters_cond.
apply Same_set_symmetric. apply Same_set_Compl.
rewrite (Extensionality_Ensembles _ _ _ (Compl_Compl_Ensembles _ _)).
rewrite (Extensionality_Ensembles _ _ _ (FA_rel _ _ _)).
eapply FA_Inters_same. intros.
proof_ext_val.
unfold Same_set. unfold Included. unfold Complement. unfold not. unfold In. eapply conj.
* intros. eapply H0. intros. refine (H _). split.
  - intros.
Admitted.


(* Theory,axiom ref. snapshot: Definition 5 *)

Definition satisfies (sm : Sigma_model) (axiom : Sigma_pattern) : Prop :=
forall (evar_val : EVar -> M sm) (svar_val : SVar -> Ensemble (M sm)),
 Same_set _ (ext_valuation (sm := sm) evar_val svar_val axiom) (Full_set _).

Definition satisfies_theory (sm : Sigma_model) (theory : Ensemble Sigma_pattern)
: Prop := forall axiom : Sigma_pattern, In _ theory axiom -> satisfies sm axiom.

Notation "M |= phi" := (satisfies M phi) (left associativity, at level 50).
Notation "M |=' Gamma" := (satisfies_theory M Gamma)
  (left associativity, at level 50).

Definition implies (theory : Ensemble Sigma_pattern) (sp : Sigma_pattern)
: Prop := forall sm : Sigma_model, (sm |=' theory) -> (sm |= sp).

Notation "G |~> phi" := (implies G phi) (left associativity, at level 50).

(* Definition 6. Definedness and derived operators *)
(* Definedness: *)
Definition c_definedness := (const ("definedness")).
Definition Definedness (phi : Sigma_pattern) : Sigma_pattern :=
  (c_definedness _._ phi).
Notation "|^ phi ^|" := (Definedness phi) (at level 100).

Definition x := evar_c("x").
Definition Definedness_Axiom : Sigma_pattern :=
  sp_forall x (Definedness (sp_var x)).

(* Totality *)
Definition c_totality := (const ("totality")).
Definition Totality (phi : Sigma_pattern) := (c_totality _._ phi).
Notation "|_ phi _|" := (Totality phi).

(* Equality *)
Definition c_equality := (const ("equality")).
Definition Equality (l r : Sigma_pattern) := ((c_equality _._ l) _._ r).
Notation "phi1 ~=~ phi2" := (Equality phi1 phi2) (at level 100).

(* Non-equality *)
Definition c_non_equality := (const ("non-equality")).
Definition NonEquality (l r : Sigma_pattern) := ((c_non_equality _._ l) _._ r).
Notation "phi1 !=~ phi2" := (NonEquality phi1 phi2) (at level 100).

(* Membership *)
Definition c_membership := (const ("membership")).
Definition Membership (x : EVar) (phi : Sigma_pattern) :=
  ((c_membership _._ (sp_var x)) _._ phi).
Notation "x -< phi" := (Membership x phi) (at level 30).

(* Non-membership *)
Definition c_non_membership := (const ("non-membership")).
Definition NonMembership (x : EVar) (phi : Sigma_pattern) :=
  ((c_non_membership _._ (sp_var x)) _._ phi).
Notation "x !-< phi" := (NonMembership x phi) (at level 30).

(* Set inclusion *)
Definition c_set_incl := (const ("set inclusion")).
Definition SetInclusion (l r : Sigma_pattern) :=
  ((c_set_incl _._ l) _._ r).
Notation "phi1 <: phi2" := (SetInclusion phi1 phi2) (at level 100).

(* Set exclusion *)
Definition c_set_excl := (const ("set exclusion")).
Definition SetExclusion (l r : Sigma_pattern) :=
  ((c_set_excl _._ l) _._ r).
Notation "phi1 !<: phi2" := (SetExclusion phi1 phi2) (at level 100).

Reserved Notation "phi |-> phi'" (at level 80).
Inductive OneStepTransition : Sigma_pattern -> Sigma_pattern -> Prop :=
| OST_totality {phi : Sigma_pattern} :
    (c_totality _._ phi) |->
    (¬ (Definedness (¬ phi)))

| OST_equality {l r : Sigma_pattern} :
    ((c_equality _._ l) _._ r) |->
    (Totality (sp_iff l r))

| OST_membership {x : EVar} {phi : Sigma_pattern} :
    ((c_membership _._ (sp_var x)) _._ phi) |->
    (Totality ((sp_var x) _&_ phi))

| OST_set_inclusion {l r : Sigma_pattern} :
    ((c_set_incl _._ l) _._ r) |->
    (Totality (sp_impl l r))

| OST_non_equality {l r : Sigma_pattern} :
    ((c_equality _._ l) _._ r) |->
    (¬ (Equality l r))

| OST_non_membership {x : EVar} {phi : Sigma_pattern} :
    ((c_non_membership _._ (sp_var x)) _._ phi) |->
    (¬ (Membership x phi))

| OST_set_exclusion {l r : Sigma_pattern} :
    ((c_set_excl _._ l) _._ r) |->
    (sp_not (SetInclusion l r))
where "a |-> b" := (OneStepTransition a b).

Reserved Notation "phi |->* phi'" (at level 100).
Inductive AnyStepTransition : Sigma_pattern -> Sigma_pattern -> Prop :=
| AST_refl {phi : Sigma_pattern} :
    phi |->* phi

| AST_trans {phi phi'' : Sigma_pattern} (phi' : Sigma_pattern) :
    (phi |-> phi') -> (phi' |->* phi'') ->
    (phi |->* phi'')
where "phi |->* phi'" := (AnyStepTransition phi phi').
(* End of Definedness derived operators and exuivalences *)

(* Introducing $ element, such as $ _._ a = M *)
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
Definition Functional_Constant (Sigma : Sigma_pattern) : Sigma_pattern :=
  (sp_exists z Sigma) ~=~ (sp_var z).
Definition Functional_Application (x y : EVar) : Sigma_pattern :=
  (sp_exists z ((sp_var x) _._ (sp_var y))) ~=~ (sp_var z).

Inductive context : Set :=
| box
| ctx_app_l (cc : context) (sp : Sigma_pattern)
| ctx_app_r (sp : Sigma_pattern) (cc : context)
.

Fixpoint subst_ctx (C : context) (sp : Sigma_pattern) : Sigma_pattern :=
match C with
| box => sp
| ctx_app_l C' sp' => sp_app (subst_ctx C' sp) sp'
| ctx_app_r sp' C' => sp_app sp' (subst_ctx C' sp)
end
.

Definition free_vars_ctx (C : context) : (ListSet.set EVar) :=
match C with
| box => List.nil
| ctx_app_l cc sp => free_vars sp
| ctx_app_r sp cc => free_vars sp
end.

(* TODO: Define provability *)
(* Definition provable (axioms : Ensemble Sigma_pattern) (phi : Sigma_pattern)
: Prop := *)

(* Notation "Gamma |- phi" := (provable Gamma phi). *)

(* Proof system for AML ref. snapshot: Section 3 *)
Inductive got : Sigma_pattern -> Prop :=
(* FOL reasoning *)
(* Propositional tautology *)
(* Auxiliary rules for proving propositional tautology *)
| E_prop_tau1 (phi : Sigma_pattern) :
    got (phi ~> phi)

| E_prop_tau2 (phi psi : Sigma_pattern) :
    got (phi ~> (psi ~> phi))

| E_prop_tau3 (phi psi xi : Sigma_pattern) :
    got ((phi ~> (psi ~> xi)) ~>
        ((phi ~> psi) ~> (phi ~> xi)))

| E_prop_tau4 (phi psi : Sigma_pattern) :
    got (((¬ phi) ~> (¬ psi)) ~> (psi ~> phi))

(* Modus ponens *)
| E_mod_pon {phi1 phi2 : Sigma_pattern} :
  got phi1 -> got (phi1 ~> phi2) -> got phi2

(* Existential quantifier *)
| E_ex_quan {phi : Sigma_pattern} (x y : EVar) :
  got ((e_subst_var phi (sp_var y) x) ~> (sp_exists x phi))

(* Existential generalization *)
| E_ex_gen (phi1 phi2 : Sigma_pattern) (x : EVar) :
  got (phi1 ~> phi2) ->
  negb (set_mem evar_eq_dec x (free_vars phi2)) = true ->
  got ((sp_exists x phi1) ~> phi2)

(* Frame reasoning *)
(* Propagation bottom *)
| E_prop_bot (C : context) :
  got ((subst_ctx C sp_bottom) ~> sp_bottom)

(* Propagation disjunction *)
| E_prop_dis (C : context) (phi1 phi2 : Sigma_pattern) :
  got ((subst_ctx C (phi1 _|_ phi2)) ~>
       ((subst_ctx C phi1) _|_ (subst_ctx C phi2)))

(* Propagation exist *)
| E_prop_ex (C : context) (phi : Sigma_pattern) (x : EVar) :
  negb (set_mem evar_eq_dec x (free_vars_ctx C)) = true ->
  got ((subst_ctx C (sp_exists x phi)) ~> (sp_exists x (subst_ctx C phi)))

(* Framing *)
| E_framing (C : context) (phi1 phi2 : Sigma_pattern) :
  got (phi1 ~> phi2) -> got ((subst_ctx C phi1) ~> (subst_ctx C phi2))

(* Fixpoint reasoning *)
(* Set Variable Substitution *)
| E_svar_subst (phi : Sigma_pattern) (psi X : SVar) :
  got phi -> got (e_subst_set phi (sp_set psi) X)

(* Pre-Fixpoint *)
| E_pre_fixp (phi : Sigma_pattern) (X : SVar) :
  got ((e_subst_set phi (sp_mu X phi) X) ~> (sp_mu X phi))

(* Knaster-Tarski *)
| E_knaster_tarski (phi psi : Sigma_pattern) (X : SVar) :
  got ((e_subst_set phi psi X) ~> psi) -> got ((sp_mu X phi) ~> psi)

(* Existence *)
| E_existence (x : EVar) : got (sp_exists x (sp_var x))

(* Singleton *)
| E_singleton (C1 C2 : context) (x : EVar) (phi : Sigma_pattern) :
  got (¬ ((subst_ctx C1 ((sp_var x) _&_    phi))   _&_
          (subst_ctx C2 ((sp_var x) _&_ (¬ phi)))))
.

Lemma A_impl_A (A : Sigma_pattern) : got (A ~> A).
Proof.
  pose(_1 := E_prop_tau3 A (A ~> A) A).
  pose(_2 := E_prop_tau2 A (A ~> A)).
  pose(_3 := E_mod_pon _2 _1).
  pose(_4 := E_prop_tau2 A A).
  pose(_5 := E_mod_pon _4 _3).
  exact _5.
Qed.

(* Inductive proof_result : Set :=
  | success ( _ )
  | fail
. *)

(* Proposition 7: *)
(* Inductive rule : ? -> Prop :=
| PR_id (Ensemble Sigma_pattern : Gamma) (phi : Sigma_pattern) :
  rule (Gamma |- (phi ~=~ phi))

| PR_trans (Ensemble Sigma_pattern : Gamma) (phi1 phi2 phi3 : Sigma_pattern) :
  Gamma |- phi1 ~=~ phi2 ->
  Gamma |- phi2 ~=~ phi3 ->
  rule (Gamma |- phi1 ~=~ phi3)

| PR_symm (Ensemble Sigma_pattern : Gamma) (phi1 phi2 : Sigma_pattern) :
  Gamma |- phi1 ~=~ phi2 ->
  rule (Gamma |- phi2 ~=~ phi1)

| PR_subst (Ensemble Sigma_pattern : Gamma) (phi1 phi2 : Sigma_pattern) :
  Gamma |- phi1 ~=~ phi2 ->
  rule (Gamma |- e_subst_var psi phi1 x ~=~ e_subst_var psi phi2 x) *)

(* Theorem 8.: Soundness *)
(* Theorem Soundness :
  forall phi : Sigma_pattern : (Gamma |- phi) -> (Gamma |= phi). *)

(* Theorem Completeness :
  forall phi : Sigma_pattern : (Gamma |= phi) -> (Gamma |- phi). *)

(* ****************************New paper version**************************** *)

(* Definition 9. MSFOL definition *)

(* Section 4.2 *)

(* further axioms need to be appended to this axiom set *)
Definition Gamma_MSFOL := Empty_set Sigma_pattern.

Definition MSAFOL_Sort := const ("Sort").

Definition Axiom_Sort (s : EVar) := s -< MSAFOL_Sort.

(* Sorts of many-sorted algebra*)
Inductive MSA_sorts : Set :=
| Nat
| List
| Cfg
| Term
.

(* a function which corresponds: constants of AML  to  sorts of MSA *)
Fixpoint AML_sort_name (s : MSA_sorts) : Sigma_pattern :=
match s with
| Nat  => const ("Nat")
| List => const ("List")
| Cfg  => const ("Cfg")
| Term => const ("Term")
end.

Definition Domain_Symbol := const ("Domain symbol").

Definition Domain (sort : MSA_sorts) := Domain_Symbol _._ (AML_sort_name sort).
Notation "'[[' s ']]'" := (Domain s) (at level 0).

Definition Nonempty_Domain (sort : MSA_sorts) :=  [[ sort ]] !=~ sp_bottom.

(* Instead of notation "forall x : Nat . pattern" we introduce: *)
Notation "'for_some' x 'of_sort' sort 'states' phi" :=
  (sp_exists x ((Membership x ([[ sort ]])) _&_ phi)) (at level 5).
Notation "'for_all' x 'of_sort' sort 'states' phi" :=
  (sp_forall x ((Membership x ([[ sort ]])) ~> phi)) (at level 5).

Notation "' v" := (sp_var v) (at level 3).
Notation "^ c" := (sp_const c) (at level 3).
Notation "` s" := (sp_set s) (at level 3).

Reserved Notation "a |--> b" (at level 40, left associativity).
Inductive QuantificationEquivalence : Sigma_pattern -> Sigma_pattern -> Prop :=
| QE_ex_to_all (xc : EVar) (sort : MSA_sorts) (pattern : Sigma_pattern) :
    ((for_some xc of_sort sort states pattern) |-->
     (sp_not (for_all xc of_sort sort states (sp_not pattern))))
| QE_all_to_ex (xc : EVar) (sort : MSA_sorts) (pattern : Sigma_pattern) :
    ((for_all xc of_sort sort states pattern)  |-->
     (¬ (for_some xc of_sort sort states (¬ pattern))))
where "a |--> b" := (QuantificationEquivalence a b).

(* Proposition 10. *)
(* Lemma forall_ex_equiv :
  forall s : MSA_sorts, forall x : EVar, forall phi : Sigma_pattern,
  (Empty_set _) |-
    (for_all x of_sort sort states phi) ~=~
    (¬ (for_some x of_sort sort states (¬ phi))). *)

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

Program Fixpoint _gen_x_vec (n m : nat) : VectorDef.t EVar n :=
match n with
| O => (VectorDef.nil EVar)
| S n' => VectorDef.cons EVar (evar_c(String.append "x" (string_of_nat(m-n+1))))
            n' (_gen_x_vec n' m)
end.

Fixpoint gen_x_vec (n : nat) : VectorDef.t EVar n :=
  _gen_x_vec n n.

Definition y := evar_c("y").
Fixpoint Function
  {n : nat} (fn : Sigma) (sorts : VectorDef.t MSA_sorts n) (y_sort : MSA_sorts)
: Sigma_pattern :=
let vars := gen_x_vec n in
let var_pats := VectorDef.map sp_var vars in
let applied_params := VectorDef.fold_left sp_app (sp_const fn) var_pats in
let core := for_some y of_sort y_sort states applied_params in
let foralls := VectorDef.map2
                (fun var s => (fun phi => for_all var of_sort s states phi))
                vars sorts in
  VectorDef.fold_right (fun spl spr => spl spr) foralls core.

Definition vc := VectorDef.cons.
Definition vn := VectorDef.nil.

Fixpoint _of_nat (n : nat) {m : nat} : Fin.t (S (n + m)) :=
match n with
 | O   => F1
 | S x => FS (_of_nat x)
end.

(* Functional notation of the function *)
Notation "f '_:_' '-->' s" := (Function f (vn _) s) (at level 0).
Notation "f '_:_' s1 '-->' s" := (Function f (vc _ s1 0 (vn _)) s) (at level 0).
(* f : s1 x s2 x ... x sn -> s *)
Notation "f '_:_' s1 'X' s2 'X' .. 'X' sn '-->' s" :=
  (Function f (vc _ s1 _ (vc _ s2 _ .. (vc _ sn _ (vn _)) .. )) s) (at level 0).

Definition Predicate
  {n : nat} (fn : Sigma) (sorts : VectorDef.t MSA_sorts n)
: Sigma_pattern :=
let vars := gen_x_vec n in
let var_pats := VectorDef.map sp_var vars in
let applied_params := VectorDef.fold_left sp_app (sp_const fn) var_pats in
let or_left := applied_params ~=~ sp_top in
let or_right := applied_params ~=~ sp_bottom in
let core := or_left _|_ or_right in
let foralls := VectorDef.map2
                (fun var s => (fun phi => for_all var of_sort s states phi))
                vars sorts in
  VectorDef.fold_right (fun spl spr => spl spr) foralls core.

Fixpoint and_gen {n : nat} (vec : VectorDef.t Sigma_pattern n)
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
  and_gen assoc.

(* TODO: fix this and ask how to get types
 *)(* Definition ws
  (phi : Sigma_pattern) {n : nat} (sorts : VectorDef.t MSA_sorts n) :=
let vars := of_list (free_vars phi) in
  _well_sorted vars sorts. *)

(* Proposition 12. *)
(* Theorem MSFOL_wellformed : forall phi : Sigma_pattern,
  Gamma_MSFOL |- (ws phi) ~> ((phi ~=~ sp_top) _|_ (phi ~=~ sp_bottom)). *)

(* Theorem 13. *)
(* Theorem Omega |- MSFOL phi -> Gamma_MSFOL |- phiMSFOL. *)

(* Definition 14. MSFOL restricted *)

(* Theorem 15. *)

(* Theorem 16. *)

(* Natural numbers *)
Definition zero : Sigma := sigma_c("zero").
Definition succ : Sigma := sigma_c("succ").
Definition plus : Sigma := sigma_c("plus'").
Definition mult : Sigma := sigma_c("mult").

Definition zero_fun := (zero _:_ --> Nat).
Definition succ_fun := (succ _:_ Nat --> Nat).
Definition plus_fun := (plus _:_ Nat X Nat --> Nat).
Definition mult_fun := (mult _:_ Nat X Nat --> Nat).

Definition succ' (x : Sigma_pattern) := ^succ _._ x.
Definition plus' (x y : Sigma_pattern) := ^plus _._ x _._ y.
Definition mult' (x y : Sigma_pattern) := ^mult _._ x _._ y.

Definition No_Confusion1 (x : EVar) :=
  for_all x of_sort Nat states
    ((const ("succ") _._ (' x)) !=~ (const ("zero"))).

Definition No_Confusion2 (x y : EVar) :=
  for_all x of_sort Nat states (for_all y of_sort Nat states
  (((const ("succ") _._ (' x)) ~=~ (const ("succ") _._ (' y))) ~>
  ((' x) ~=~ (' y)))).

Definition Inductive_Domain (D : SVar) :=
  (Domain Nat) ~=~
  (sp_mu D ((const ("zero")) _|_ ((const ("succ")) _._ (` D)))).

Definition Peano_Induction (n : EVar) (phi : Sigma_pattern -> Sigma_pattern) :=
  (((phi (const ("zero"))) _&_
  (sp_forall n ((phi (' n)) ~>
    (phi ((const ("succ")) _._ (' n))))) ) ~>
  (sp_forall n (phi (' n)))).

Fixpoint app_inhabitant_sets {n : nat} (vec : VectorDef.t MSA_sorts n)
: Sigma_pattern :=
match vec with
| VectorDef.nil _ => const ("cannot operate on empty parameters")
| VectorDef.cons _ elem _ (VectorDef.nil _) => [[ elem ]]
| VectorDef.cons _ elem _ vec' =>
    ([[ elem ]]) _._ (app_inhabitant_sets vec')
end.

Definition Arity (sigma : Sigma_pattern) {n : nat}
                 (s_vec : VectorDef.t MSA_sorts n) (s : MSA_sorts)
: Sigma_pattern :=
  sigma _._ (app_inhabitant_sets s_vec) <: InhabitantSetOf(s).


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
  (for_all x of_sort Nat states ((plus' 'x one) ~=~ five)).

Definition plus_x_z_eq_y :=
  (for_all x of_sort Nat states
    (for_all y of_sort Nat states
      (for_all z of_sort Nat states
        ((plus' 'x 'z) ~=~ 'y)))).

Definition plus_x_plus_z_3_eq_y :=
  (for_all x of_sort Nat states
    (for_all y of_sort Nat states
      (for_all z of_sort Nat states
        ((plus' 'x (plus' 'z three))) ~=~ 'y))).


(* Example: x + 0 = x *)
Definition x_plus_0_eq_x :=
(for_all x of_sort Nat states ((plus' 'x ^zero) ~=~ 'x)).

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
  for_all n of_sort Nat states (mult' two (SumFromZeroTo 'n) ~=~
  mult' 'n (succ' 'n)).


Fixpoint ProdFromOneTo (n : Sigma_pattern) : Sigma_pattern :=
match n with
| sp_const _ => ^zero
      (* succ _ *)
| sp_app _    b =>
  match b with
  | sp_const _ => one
  | sp_app _ _ => mult' (succ' b) (ProdFromOneTo b)
  | _ => ^(sigma_c("non-exhaustive pattern"))
  end
| _ => ^(sigma_c("non-exhaustive pattern"))
end.

Fixpoint SumOfSquaresFromZeroTo (n : Sigma_pattern) : Sigma_pattern :=
match n with
| sp_const _ => ^zero
      (* succ b *)
| sp_app _    b => plus' (mult' (succ' b) (succ' b)) (SumOfSquaresFromZeroTo b)
| _ => ^(sigma_c("non-exhaustive pattern"))
end.

(* 1^2 + ... + n^2 = n(n+1)(2*n + 1) / 6. *)
Definition Sum_of_squares :=
  for_all n of_sort Nat states (
    mult' six (SumOfSquaresFromZeroTo 'n) ~=~
    mult' 'n (mult' (succ' 'n) (plus' (mult' two 'n) one))).


(* <= relation *)
Definition less (l r : Sigma_pattern) :=
for_some x of_sort Nat states (plus' l (sp_var x) ~=~ r).

Definition less_or_equal (l r : Sigma_pattern) :=
sp_or
  (l ~=~ r)
  for_some x of_sort Nat states (plus' l (sp_var x) ~=~ r).

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

Lemma ex1 : got ('x ~> 'x).
Proof. apply E_prop_tau1. Qed.

Lemma ex2 : got (sp_bottom ~> ((sp_var x) ~> sp_bottom)).
Proof. apply E_prop_tau2. Qed.

Lemma ex3 : got (('x ~> ('y ~> 'z)) ~> (('x ~> 'y) ~> ('x ~> 'z))).
Proof. apply E_prop_tau3. Qed.

Lemma ex4 : got (((sp_not 'x) ~> (sp_not 'y)) ~> ('y ~> 'x)).
Proof. apply E_prop_tau4. Qed.

(* Lemma ex5 : (got 'x) -> (got (' x ~> ' y)) -> (got ' y).
Proof. apply (E_mod_pon 'x 'y). Qed. *)

Lemma ex6 : got (e_subst_var sp_bottom 'y x ~> sp_exists x sp_bottom).
Proof. apply E_ex_quan. Qed.

Lemma ex7 :
  got ('x ~> 'y) ->
  negb (set_mem evar_eq_dec z (free_vars 'y)) = true ->
  got (sp_exists z 'x ~> 'y).
Proof. apply E_ex_gen. Qed.

(* TODO Ltac. *)

Lemma A_impl_A (A : Sigma_pattern) : got (A ~> A).
Proof.
  pose(_1 := E_prop_tau3 A (A ~> A) A).
  pose(_2 := E_prop_tau2 A (A ~> A)).
  pose(_3 := E_mod_pon _2 _1).
  pose(_4 := E_prop_tau2 A A).
  pose(_5 := E_mod_pon _4 _3).
  exact _5.
Qed.

(* Theorem A_impl_A_equiv : forall A : Sigma_pattern, (A_impl_A A) = (E_prop_tau1 A).
Proof.
  intros.
  induction A.
Admitted. *)


(* Lemma C3 (A B : Sigma_pattern) :
(*   got (((sp_not A) ~> B) ~> (((sp_not A) ~> (sp_not B)) ~> A)). *)
Proof. *)
(*   pose(_1 := (E_prop_tau2 ((sp_not A) ~> B) ((sp_not A) ~> (sp_not B)))). *)

(* Lemma nn_A_imp_A (A : Sigma_pattern) (nna : got (sp_not (sp_not A))) : got ((sp_not (sp_not A)) ~> A).
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
(* Lemma ex : got x_plus_0_eq_x.
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
