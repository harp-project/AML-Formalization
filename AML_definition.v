Require Export String.
Require Export Coq.Lists.ListSet.
Require Export Ensembles_Ext.

Section AML.

(* Syntax of AML ref. snapshot: Section 2.1 *)

Inductive EVar : Type := evar_c {id_ev : string}.
Inductive SVar : Type := svar_c {id_sv : string}.
Inductive Sigma : Type := sigma_c {id_si : string}.

Definition evar_eq_dec : forall (x y : EVar), { x = y } + { x <> y }.
Proof. decide equality. exact (string_dec id_ev0 id_ev1). Defined.

Definition svar_eq_dec : forall (x y : SVar), { x = y } + { x <> y }.
Proof. decide equality. exact (string_dec id_sv0 id_sv1). Defined.

Definition sigma_eq_dec : forall (x y : Sigma), { x = y } + { x <> y }.
Proof. decide equality. exact (string_dec id_si0 id_si1). Defined.

Definition evar_eqb (x y : EVar) : bool := String.eqb (id_ev x) (id_ev y).
Definition svar_eqb (x y : SVar) : bool := String.eqb (id_sv x) (id_sv y).
Definition sigma_eqb (x y : Sigma) : bool := String.eqb (id_si x) (id_si y).

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

Inductive strictly_positive : SVar -> Sigma_pattern -> Prop :=
| sp_sp_var (x : EVar) (X : SVar) : strictly_positive X (sp_var x)
| sp_sp_set (Y : SVar) (X : SVar) : strictly_positive X (sp_set Y)
| sp_sp_const (sigma : Sigma) (X : SVar) : strictly_positive X (sp_const sigma)
| sp_sp_app (phi1 phi2 : Sigma_pattern) (X : SVar) :
  strictly_positive X phi1 -> strictly_positive X phi2 ->
  strictly_positive X (sp_app phi1 phi2)
| sp_sp_bottom (X : SVar) : strictly_positive X sp_bottom
| sp_sp_impl (phi1 phi2 : Sigma_pattern) (X : SVar) :
  strictly_negative X phi1 -> strictly_positive X phi2 ->
  strictly_positive X (sp_impl phi1 phi2)
| sp_sp_exists (x : EVar) (phi : Sigma_pattern) (X : SVar) :
  strictly_positive X phi ->
  strictly_positive X (sp_exists x phi)
| sp_sp_mu (Y : SVar) (phi : Sigma_pattern) (X : SVar) :
  (Y = X) \/ (Y <> X /\ strictly_positive X phi) ->
  strictly_positive X (sp_mu Y phi)
with strictly_negative : SVar -> Sigma_pattern -> Prop :=
| sn_sp_var (x : EVar) (X : SVar) : strictly_negative X (sp_var x)
| sn_sp_set (Y : SVar) (X : SVar) : Y <> X -> strictly_negative X (sp_set Y)
| sn_sp_const (sigma : Sigma) (X : SVar) : strictly_negative X (sp_const sigma)
| sn_sp_app (phi1 phi2 : Sigma_pattern) (X : SVar) :
  strictly_negative X phi1 -> strictly_negative X phi2 ->
  strictly_negative X (sp_app phi1 phi2)
| sn_sp_bottom (X : SVar) : strictly_negative X sp_bottom
| sn_sp_impl (phi1 phi2 : Sigma_pattern) (X : SVar) :
  strictly_positive X phi1 -> strictly_negative X phi2 ->
  strictly_negative X (sp_impl phi1 phi2)
| sn_sp_exists (x : EVar) (phi : Sigma_pattern) (X : SVar) :
  strictly_negative X phi ->
  strictly_negative X (sp_exists x phi)
| sn_sp_mu (Y : SVar) (phi : Sigma_pattern) (X : SVar) :
  (Y = X) \/ (Y <> X /\ strictly_negative X phi) ->
  strictly_negative X (sp_mu Y phi)
.

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

Definition set_singleton {T : Type}
  (eq : forall (x y : T), { x = y } + { x <> y })
  := fun x : T => set_add eq x List.nil.

Fixpoint free_evars (phi : Sigma_pattern) : (ListSet.set EVar) :=
match phi with
| sp_var x => set_singleton evar_eq_dec x
| sp_set X => List.nil
| sp_const sigma => List.nil
| sp_app phi1 phi2 => set_union evar_eq_dec (free_evars phi1) (free_evars phi2)
| sp_bottom => List.nil
| sp_impl phi1 phi2 => set_union evar_eq_dec (free_evars phi1) (free_evars phi2)
| sp_exists y phi => set_remove evar_eq_dec y (free_evars phi)
| sp_mu X phi => free_evars phi
end.

Fixpoint free_svars (phi : Sigma_pattern) : (ListSet.set SVar) :=
match phi with
| sp_var x => List.nil
| sp_set X => set_singleton svar_eq_dec X
| sp_const sigma => List.nil
| sp_app phi1 phi2 => set_union svar_eq_dec (free_svars phi1) (free_svars phi2)
| sp_bottom => List.nil
| sp_impl phi1 phi2 => set_union svar_eq_dec (free_svars phi1) (free_svars phi2)
| sp_exists y phi => free_svars phi
| sp_mu X phi => set_remove svar_eq_dec X (free_svars phi)
end.

(* Derived operators *)
Definition sp_not (phi : Sigma_pattern) := phi ~> sp_bottom.
Notation "¬ a"     := (sp_not   a  ) (at level 75).

Definition sp_or  (l r : Sigma_pattern) := (¬ l) ~> r.
Notation "a _|_ b" := (sp_or    a b) (at level 85, right associativity).

Definition sp_and (l r : Sigma_pattern) := ¬ ((¬ l) _|_ (¬ r)).
Notation "a _&_ b" := (sp_and   a b) (at level 80, right associativity).

Definition sp_iff (l r : Sigma_pattern) := ((l ~> r) _&_ (r ~> l)).
Notation "a <~> b" := (sp_iff a b) (at level 95, no associativity).

Definition sp_top := (¬ sp_bottom).
Notation "'Top'" := sp_top.

Definition sp_forall (x : EVar) (phi : Sigma_pattern) :=
  ¬ (sp_exists x (¬ phi)).
Notation "'all' x , phi" := (sp_forall x phi) (at level 55).

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

Definition change_val {T1 T2 : Type} (eqb : T1 -> T1 -> bool)
                      (t1 : T1) (t2 : T2) (f : T1 -> T2) : T1 -> T2 :=
fun x : T1 => if eqb x t1 then t2 else f x.


(* Model of AML ref. snapshot: Definition 2 *)

Record Sigma_model := {
  M : Type;
  example : M; (* so M can not be empty *)
  A_eq_dec : forall (a b : M), {a = b} + {a <> b};
  app : M -> M -> Ensemble M;
  interpretation : Sigma -> Ensemble M;
}.

Definition pointwise_app {sm : Sigma_model} (l r : Ensemble (M sm)) :
                         Ensemble (M sm) :=
fun e:M sm => exists le re:M sm, l le /\ r re /\ (app sm) le re e.

Compute @pointwise_app {| M := Sigma_pattern |} (Singleton _ (var "a")) (Singleton _ (var "b")).

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
   rewrite (Same_set_to_eq (Union_Empty_l _))
|| rewrite (Same_set_to_eq (Compl_Compl_Ensembles _ _))
|| rewrite
   (Same_set_to_eq (Compl_Union_Compl_Intes_Ensembles_alt _ _ _))
|| rewrite (Same_set_to_eq (FA_rel _ _ _))
  (* Apply *)
|| (eapply (proj1 Same_set_Compl) ; intros)
|| (eapply FA_Inters_same ; intros)
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
Proof. proof_ext_val. Qed.

Lemma forall_ext_val_correct
{sm : Sigma_model} {evar_val : EVar -> M sm} {svar_val : SVar -> Ensemble _} :
forall sp : Sigma_pattern, forall x : EVar, Same_set _
  (ext_valuation evar_val svar_val (sp_forall x sp))
  (FA_Intersection
    (fun a => ext_valuation (change_val evar_eqb x a evar_val) svar_val sp)).
Proof. proof_ext_val. Qed.

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
rewrite (Same_set_to_eq (Compl_Compl_Ensembles _ _)).
rewrite (Same_set_to_eq (FA_rel _ _ _)).
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

Definition AML_theories : Ensemble Sigma_pattern := Empty_set Sigma_pattern.

(* End of definition 5. *)


(* Definition 6. Definedness and derived operators *)
Definition definedness_symbol := (const ("definedness")).
Definition defined (x : Sigma_pattern) := (definedness_symbol $ x).
Notation "|^ phi ^|" := (defined phi) (at level 100).

(* Definition Definedness_var (x : EVar) : Sigma_pattern :=
  |^ 'x ^|. *)

Definition Definedness_forall (x : EVar) : Sigma_pattern :=
  all x, |^ 'x ^|.

(* Totality *)
Definition total (sp : Sigma_pattern) := (¬ (|^ (¬ sp) ^|)).
Notation "|_ phi _|" := (total phi) (at level 100).

(* Equality *)
Definition equal (a b : Sigma_pattern) := (|_ (a <~> b) _|).
Notation "a ~=~ b" := (equal a b) (at level 100).

(* Non-equality *)
Definition not_equal (a b : Sigma_pattern) := (¬ (equal a b)).
Notation "a !=~ b" := (not_equal a b) (at level 100).

(* Membership *)
Definition member (x sp : Sigma_pattern) := (|^ (x _&_ sp) ^|).
Notation "x -< phi" := (member x phi) (at level 100).

(* Non-membership *)
Definition non_member (x sp : Sigma_pattern) := (¬ (member x sp)).
Notation "x !-< phi" := (non_member x phi) (at level 100).

(* Set inclusion *)
Definition includes (a b : Sigma_pattern) := (|_ (a ~> b) _|).
Notation "a <: b" := (includes a b) (at level 100).

(* Set exclusion *)
Definition not_includes (a b : Sigma_pattern) := (¬ (includes a b)).
Notation "a !<: b" := (not_includes a b) (at level 100).


(* Introducing '$' element, such as '$' $ a = M *)
Definition spec_elem : Sigma_pattern := const ("$").

Definition spec_app_a_eq_M (a : EVar) :=
  ((spec_elem $ 'a) ~=~ Top).

Definition spec_app_A_eq_M (A : SVar) :=
  ((spec_elem $ `A) ~=~ Bot) <~> (`A !=~ Bot).


(**
  $ . S = M iff S is not empty
  See: paragraph after Definition 6.
 *)
Axiom semantics_of_definedness : forall sm : Sigma_model, forall S : Ensemble (M sm),
  ~ (Same_set (M sm) S (Empty_set (M sm))) <->
  Same_set (M sm) (pointwise_app (interpretation sm {| id_si := "definedness" |}) S) (Full_set (M sm))
.

Lemma pointwise_app_bot : forall sm : Sigma_model, forall S : Ensemble (M sm),
  Same_set (M sm) (pointwise_app S (Empty_set (M sm))) (Empty_set (M sm)).
Proof.
  intros. unfold pointwise_app. unfold Same_set. unfold Included. unfold In. split; intros.
  * inversion H. inversion H0. inversion H1. inversion H3. contradiction.
  * contradiction.
Qed.

Lemma semantics_of_definedness_2 : forall sm : Sigma_model, forall S : Ensemble (M sm),
  (Same_set (M sm) S (Empty_set (M sm))) <->
  Same_set (M sm) (pointwise_app (interpretation sm {| id_si := "definedness" |}) S) (Empty_set (M sm)).
Proof.
  split; intros.
  * apply Extensionality_Ensembles in H. subst.
    apply pointwise_app_bot.
  * unfold Same_set, Included, In in H. inversion H.
    case_eq (Same_set_dec S (Empty_set (M sm))).
    - intros. assumption.
    - intros. pose (Not_Empty_Contains_Elements S n). inversion e.
      pose (semantics_of_definedness sm S). destruct i. pose (H4 n).
      apply Extensionality_Ensembles in s. rewrite s in *.
      assert (Full_set (M sm) x). { apply Full_intro. }
      pose (H0 x H6). contradiction.
Qed.


(* Can be shown, that all notations in Definition 6 are predicates with the
 * expected semantics. For example: *)
Lemma totality_eq_step1
  {sm : Sigma_model} {evar_val : EVar -> M sm} {svar_val : SVar -> Ensemble _} :
  forall phi : Sigma_pattern,
  (Same_set _ (ext_valuation evar_val svar_val (|_ phi _|))
              (Full_set _)) <->
  (Same_set _ (ext_valuation evar_val svar_val (¬ (|^ (¬phi) ^|)))
              (Full_set _)).
Proof. proof_ext_val. reflexivity. Qed.

Lemma totality_eq_step2
  {sm : Sigma_model} {evar_val : EVar -> M sm} {svar_val : SVar -> Ensemble _} :
  forall phi : Sigma_pattern,
  (Same_set _ (ext_valuation evar_val svar_val (|_ phi _|))
              (Full_set _)) <->
  (Same_set _ (ext_valuation evar_val svar_val (|^ (¬phi) ^|))
              (Empty_set _)).
Proof.
  proof_ext_val. remember ((pointwise_app (interpretation sm {| id_si := "definedness" |})
        (Complement (M sm) (ext_valuation evar_val svar_val phi)))) as S.
  pose (CMF := @Complement_Empty_is_Full (M sm)).
  pose (Ext := Extensionality_Ensembles (M sm) _ _ CMF).
  rewrite <- Ext.
  pose (COMPL := @Same_set_Compl (M sm) S (Empty_set (M sm))).
  destruct COMPL.
  split; intros.
  * pose (H0 H1). assumption.
  * pose (H H1). assumption.
Qed.

Lemma totality_eq_step3
  {sm : Sigma_model} {evar_val : EVar -> M sm} {svar_val : SVar -> Ensemble _} :
  forall phi : Sigma_pattern,
  (Same_set _ (ext_valuation evar_val svar_val (|_ phi _|))
              (Full_set _)) <->
  (Same_set _ (ext_valuation evar_val svar_val ((¬phi)))
              (Empty_set _)).
Proof.
  proof_ext_val.
  remember ((ext_valuation evar_val svar_val phi)) as S.
  rewrite <- (Same_set_to_eq (@Complement_Empty_is_Full (M sm))).
  rewrite <- Same_set_Compl.
  rewrite <- semantics_of_definedness_2.
  reflexivity.
Qed.

Lemma total_sem
  {sm : Sigma_model} {evar_val : EVar -> M sm} {svar_val : SVar -> Ensemble _} :
  forall phi : Sigma_pattern,
  (Same_set _ (ext_valuation evar_val svar_val (|_ phi _|)) (Full_set _)) <->
  (Same_set _ (ext_valuation evar_val svar_val (phi)) (Full_set _)).
Proof.
  proof_ext_val.
  rewrite <- (Same_set_to_eq (@Complement_Empty_is_Full (M sm))).
  rewrite <- Same_set_Compl.
  rewrite <- semantics_of_definedness_2.
  rewrite <- (Same_set_to_eq (@Complement_Full_is_Empty (M sm))).
  rewrite <- Same_set_Compl.
  rewrite (Same_set_to_eq (Compl_Compl_Ensembles _ (Full_set (M sm)))).
  reflexivity.
Qed.

Lemma equality_eq_step1
  {sm : Sigma_model} {evar_val : EVar -> M sm} {svar_val : SVar -> Ensemble _} :
  forall phi1 phi2 : Sigma_pattern,
  (Same_set _ (ext_valuation evar_val svar_val (phi1 ~=~ phi2))
              (Full_set _)) <->
  (Same_set _ (ext_valuation evar_val svar_val (|_ (phi1 <~> phi2) _|))
              (Full_set _)).
Proof. proof_ext_val. reflexivity. Qed.

Lemma equality_eq_step2
  {sm : Sigma_model} {evar_val : EVar -> M sm} {svar_val : SVar -> Ensemble _} :
  forall phi1 phi2 : Sigma_pattern,
  (Same_set _ (ext_valuation evar_val svar_val (phi1 ~=~ phi2))
              (Full_set _)) <->
  (Same_set _ (ext_valuation evar_val svar_val (phi1 <~> phi2))
              (Full_set _)).
Proof.
  proof_ext_val.
  remember (ext_valuation evar_val svar_val phi1) as S1.
  remember (ext_valuation evar_val svar_val phi2) as S2.
  rewrite <- (Same_set_to_eq (@Complement_Empty_is_Full (M sm))).
  rewrite <- Same_set_Compl.
  rewrite <- semantics_of_definedness_2.
  rewrite (Same_set_to_eq (Compl_Union_Intes_Compl_Ensembles _ (Complement (M sm) S1) S2)).
  rewrite (Same_set_to_eq (Compl_Union_Intes_Compl_Ensembles _ (Complement (M sm) S2) S1)).
  rewrite (Same_set_to_eq (Compl_Compl_Ensembles _ S2)).
  rewrite (Same_set_to_eq (Compl_Compl_Ensembles _ S1)).
  rewrite Same_set_Compl.
  rewrite (Same_set_to_eq (Compl_Union_Intes_Compl_Ensembles _ (Intersection (M sm) S1 (Complement (M sm) S2)) (Intersection (M sm) S2 (Complement (M sm) S1)))).
  rewrite (Same_set_to_eq (Compl_Intes_Union_Compl_Ensembles _ (S1) (Complement (M sm) S2))).
  rewrite (Same_set_to_eq (Compl_Intes_Union_Compl_Ensembles _ (S2) (Complement (M sm) S1))).
  rewrite (Same_set_to_eq (Compl_Compl_Ensembles _ S2)).
  rewrite (Same_set_to_eq (Compl_Compl_Ensembles _ S1)).
  reflexivity.
Qed.

Lemma equality_eq_step3
  {sm : Sigma_model} {evar_val : EVar -> M sm} {svar_val : SVar -> Ensemble _} :
  forall phi1 phi2 : Sigma_pattern,
  (Same_set _ (ext_valuation evar_val svar_val (phi1 ~=~ phi2))
              (Full_set _)) <->
  (Same_set _ (Symmetric_difference (ext_valuation evar_val svar_val phi1) (ext_valuation evar_val svar_val phi2))
              (Empty_set _)).
Admitted.

Lemma equality_eq_step4
  {sm : Sigma_model} {evar_val : EVar -> M sm} {svar_val : SVar -> Ensemble _} :
  forall phi1 phi2 : Sigma_pattern,
  (Same_set _ (ext_valuation evar_val svar_val (phi1 ~=~ phi2))
              (Full_set _)) <->
  (Same_set _ (ext_valuation evar_val svar_val (phi1))
              (ext_valuation evar_val svar_val (phi2))).
Proof.
  proof_ext_val.
  remember (ext_valuation evar_val svar_val phi1) as S1.
  remember (ext_valuation evar_val svar_val phi2) as S2.
  rewrite <- (Same_set_to_eq (@Complement_Empty_is_Full (M sm))).
  rewrite <- Same_set_Compl.
  rewrite (Same_set_to_eq (Compl_Union_Intes_Compl_Ensembles _ (Complement (M sm) S1) S2)).
  rewrite (Same_set_to_eq (Compl_Union_Intes_Compl_Ensembles _ (Complement (M sm) S2) S1)).
  rewrite (Same_set_to_eq (Compl_Compl_Ensembles _ S2)).
  rewrite (Same_set_to_eq (Compl_Compl_Ensembles _ S1)).
  rewrite (Same_set_to_eq (Intersection_Setminus S1 S2)).
  rewrite (Same_set_to_eq (Intersection_Setminus S2 S1)).
  rewrite <- semantics_of_definedness_2.
  rewrite Union_Minus_Empty.
  reflexivity.
Qed.

(* Proposition 20.: Semantics of definedness operators *)
Lemma defined_sem
  {sm : Sigma_model} {evar_val : EVar -> M sm} {svar_val : SVar -> Ensemble _} :
  forall phi : Sigma_pattern,
  (Same_set _ (ext_valuation evar_val svar_val (|^ phi ^|)) (Full_set _)) <->
  ~ (Same_set _ (ext_valuation evar_val svar_val (phi)) (Empty_set _)).
Proof.
  proof_ext_val. 
  rewrite <- semantics_of_definedness.
  reflexivity.
Qed.

Lemma not_defined_sem
  {sm : Sigma_model} {evar_val : EVar -> M sm} {svar_val : SVar -> Ensemble _} :
  forall phi : Sigma_pattern,
  (Same_set _ (ext_valuation evar_val svar_val (|^ phi ^|)) (Empty_set _)) <->
  (Same_set _ (ext_valuation evar_val svar_val (phi)) (Empty_set _)).
Proof.
  proof_ext_val.
  rewrite <- semantics_of_definedness_2.
  reflexivity.
Qed.

Lemma not_total_sem
  {sm : Sigma_model} {evar_val : EVar -> M sm} {svar_val : SVar -> Ensemble _} :
  forall phi : Sigma_pattern,
  (Same_set _ (ext_valuation evar_val svar_val (|_ phi _|)) (Empty_set _)) <->
  ~ (Same_set _ (ext_valuation evar_val svar_val (phi)) (Full_set _)).
Proof.
  proof_ext_val.
  rewrite <- (Same_set_to_eq (@Complement_Full_is_Empty (M sm))).
  rewrite <- Same_set_Compl.
  rewrite <- semantics_of_definedness.
  rewrite <- (Same_set_to_eq (@Complement_Full_is_Empty (M sm))).
  rewrite <- Same_set_Compl. reflexivity.
Qed.

Lemma not_equal_sem
  {sm : Sigma_model} {evar_val : EVar -> M sm} {svar_val : SVar -> Ensemble _} :
  forall a b : Sigma_pattern,
  (Same_set _ (ext_valuation evar_val svar_val (a ~=~ b)) (Empty_set _)) <->
  ~ (Same_set _ (ext_valuation evar_val svar_val a)
              (ext_valuation evar_val svar_val b)).
Proof.
  proof_ext_val.
  remember (ext_valuation evar_val svar_val a) as S1.
  remember (ext_valuation evar_val svar_val b) as S2.
  rewrite <- (Same_set_to_eq (@Complement_Full_is_Empty (M sm))).
  rewrite <- Same_set_Compl.
  rewrite (Same_set_to_eq (Compl_Union_Intes_Compl_Ensembles _ (Complement (M sm) S1) S2)).
  rewrite (Same_set_to_eq (Compl_Union_Intes_Compl_Ensembles _ (Complement (M sm) S2) S1)).
  rewrite (Same_set_to_eq (Compl_Compl_Ensembles _ S2)).
  rewrite (Same_set_to_eq (Compl_Compl_Ensembles _ S1)).
  rewrite (Same_set_to_eq (Intersection_Setminus S1 S2)).
  rewrite (Same_set_to_eq (Intersection_Setminus S2 S1)).
  rewrite <- semantics_of_definedness.
  rewrite Union_Minus_Empty.
  reflexivity.
Qed.

Lemma membership_sem
  {sm : Sigma_model} {evar_val : EVar -> M sm} {svar_val : SVar -> Ensemble _} :
  forall x : EVar, forall sp : Sigma_pattern,
  (Same_set _ (ext_valuation evar_val svar_val ('x -< sp)) (Full_set _)) <->
  (In _ (ext_valuation evar_val svar_val sp) (evar_val x)).
Proof.
  proof_ext_val.
  remember (ext_valuation evar_val svar_val sp) as S.
  rewrite <- semantics_of_definedness.
  rewrite <- Intersection_singleton.
  reflexivity.
Qed.

Lemma non_membership_sem
  {sm : Sigma_model} {evar_val : EVar -> M sm} {svar_val : SVar -> Ensemble _} :
  forall x : EVar, forall sp : Sigma_pattern,
  (Same_set _ (ext_valuation evar_val svar_val ('x -< sp)) (Empty_set _)) <->
  ~ (In _ (ext_valuation evar_val svar_val sp) (evar_val x)).
Proof.
  proof_ext_val.
  proof_ext_val.
  remember (ext_valuation evar_val svar_val sp) as S.
  rewrite <- semantics_of_definedness_2.
  rewrite <- Intersection_singleton_empty.
  reflexivity.
Qed.

Lemma set_inculsion_sem
  {sm : Sigma_model} {evar_val : EVar -> M sm} {svar_val : SVar -> Ensemble _} :
  forall a b : Sigma_pattern,
  (Same_set _ (ext_valuation evar_val svar_val (a <: b)) (Full_set _)) <->
  ((Same_set _ (ext_valuation evar_val svar_val a)
               (ext_valuation evar_val svar_val b)) \/
   (Strict_Included _ (ext_valuation evar_val svar_val a)
                      (ext_valuation evar_val svar_val b))).
Proof.
  proof_ext_val.
  remember (ext_valuation evar_val svar_val a) as S1.
  remember (ext_valuation evar_val svar_val b) as S2.
  rewrite <- (Same_set_to_eq (@Complement_Empty_is_Full (M sm))).
  rewrite <- Same_set_Compl.
  rewrite <- semantics_of_definedness_2.
  rewrite (Same_set_to_eq (Compl_Union_Intes_Compl_Ensembles _ (Complement (M sm) S1) S2)).
  rewrite (Same_set_to_eq (Compl_Compl_Ensembles _ S1)).
  rewrite <- Intersection_Comple_Strinct_Included.
  reflexivity.
Qed.

Lemma set_exclusion_sem
  {sm : Sigma_model} {evar_val : EVar -> M sm} {svar_val : SVar -> Ensemble _} :
  forall a b : Sigma_pattern,
  (Same_set _ (ext_valuation evar_val svar_val (a <: b)) (Empty_set _)) <->
  ~ ((Same_set _ (ext_valuation evar_val svar_val a)
               (ext_valuation evar_val svar_val b)) \/
   (Strict_Included _ (ext_valuation evar_val svar_val a)
                      (ext_valuation evar_val svar_val b))).
Proof.
  proof_ext_val.
  remember (ext_valuation evar_val svar_val a) as S1.
  remember (ext_valuation evar_val svar_val b) as S2.
  rewrite <- (Same_set_to_eq (@Complement_Full_is_Empty _)).
  rewrite <- Same_set_Compl.
  rewrite <- semantics_of_definedness.
  rewrite (Same_set_to_eq (Compl_Union_Intes_Compl_Ensembles _ (Complement (M sm) S1) S2)).
  rewrite (Same_set_to_eq (Compl_Compl_Ensembles _ S1)).
  rewrite <- Not_Intersection_Comple_Strinct_Included.
  reflexivity.
Qed.

(* Functional Constant axiom *)
Definition Functional_Constant (constant : Sigma) (z : EVar) : Sigma_pattern :=
  (ex z , (^constant ~=~ 'z)).


Inductive Application_context : Set :=
| box
| ctx_app_l (cc : Application_context) (sp : Sigma_pattern)
| ctx_app_r (sp : Sigma_pattern) (cc : Application_context)
.

Fixpoint subst_ctx (C : Application_context) (sp : Sigma_pattern)
: Sigma_pattern :=
match C with
| box => sp
| ctx_app_l C' sp' => sp_app (subst_ctx C' sp) sp'
| ctx_app_r sp' C' => sp_app sp' (subst_ctx C' sp)
end
.

Fixpoint free_vars_ctx (C : Application_context) : (ListSet.set EVar) :=
match C with
| box => List.nil
| ctx_app_l cc sp => set_union evar_eq_dec (free_vars_ctx cc) (free_evars sp)
| ctx_app_r sp cc => set_union evar_eq_dec (free_evars sp) (free_vars_ctx cc)
end.


(* Proof system for AML ref. snapshot: Section 3 *)

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
    negb (set_mem evar_eq_dec x (free_evars phi2)) = true ->
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

where "pattern 'proved'" := (AML_proof_system pattern).

Definition empty_theory := Empty_set Sigma_pattern.

Reserved Notation "theory |- pattern" (at level 1).
Inductive Provable : Ensemble Sigma_pattern -> Sigma_pattern -> Prop :=
(* Using hypothesis from theory 
   CAUTION: According to deduction theorem, the totality can be proved, not the formula itself
*)
| hypothesis
  (axiom : Sigma_pattern) (theory : Ensemble Sigma_pattern) :
    (In _ theory axiom) -> theory |- axiom

(* AML_proof_system rule embedding *)
(* Introduce proof system rules *)
| proof_sys_intro
  (pattern : Sigma_pattern) (theory : Ensemble Sigma_pattern) :
    pattern proved -> theory |- pattern

(* Introduce step rules *)
| E_mod_pon
  (phi1 phi2 : Sigma_pattern) (theory : Ensemble Sigma_pattern) :
    theory |- phi1 -> theory |- (phi1 ~> phi2) -> theory |- phi2

| E_ex_gen
  (x : EVar) (phi1 phi2 : Sigma_pattern) (theory : Ensemble Sigma_pattern) :
    theory |- (phi1 ~> phi2) ->
    negb (set_mem evar_eq_dec x (free_evars phi2)) = true ->
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

where "theory |- pattern" := (Provable theory pattern).

(* Deduction theorem 
   see: mML TR Theorem 14
*)
Theorem deduction_intro
  (axiom pattern : Sigma_pattern) (theory : Ensemble Sigma_pattern) :
    (Add _ theory axiom) |- pattern ->
    theory |- (|_ axiom _| ~> pattern).
Admitted.

Theorem deduction_elim
  (axiom pattern : Sigma_pattern) (theory : Ensemble Sigma_pattern) :
    (theory |- (|_ axiom _| ~> pattern)) ->
    (Add _ theory axiom) |- pattern.
Admitted.

Theorem deduction
  {axiom pattern : Sigma_pattern} (theory : Ensemble Sigma_pattern) :
    (Add _ theory axiom) |- pattern <->
    theory |- (|_ axiom _| ~> pattern).
Admitted.

(* Theorem deduction_intro_with_sub
  (axiom pattern : Sigma_pattern) (theory : Ensemble Sigma_pattern) :
    In _ theory axiom -> theory |- pattern ->
    (Subtract _ theory axiom) |- (|_ axiom _| ~> pattern).
Admitted.

Theorem deduction_with_sub
  {axiom pattern : Sigma_pattern} (theory : Ensemble Sigma_pattern) :
    In _ theory axiom -> theory |- pattern <->
    (Subtract _ theory axiom) |- (|_ axiom _| ~> pattern).
Admitted. *)

(* Examples of use *)

(* Notation "'{{' a 'add' b 'add' .. 'add' z '}}'" :=
    (Add _ a (Add _ b .. (Add _ z) ..)) (at level 2). *)


(* Theorem 8.: Soundness *)
Theorem Soundness :
  forall phi : Sigma_pattern, forall theory : Ensemble Sigma_pattern,
  (theory |- phi) -> (theory |= phi).
Proof.
  intros. unfold "|=". unfold "|=T", "|=M".
  intros.
  induction H.
  * apply H0. assumption.
(*
Proof.
  intros.
  induction (proof_length (theory |- phi)).
*)
Admitted.

End AML.

Module AML_notations.

Notation "' v" := (sp_var v) (at level 3).
Notation "` s" := (sp_set s) (at level 3).
Notation "^ c" := (sp_const c) (at level 3).
Notation "a $ b" := (sp_app a b) (at level 50, left associativity).
Notation "'Bot'" := sp_bottom.
Notation "a ~> b"  := (sp_impl a b) (at level 90, right associativity,
                                      b at level 200).
Notation "'ex' x , phi" := (sp_exists x phi) (at level 55).
Notation "'mu' X , phi" := (sp_mu X phi) (at level 55).

Notation "¬ a"     := (sp_not   a  ) (at level 75).
Notation "a _|_ b" := (sp_or    a b) (at level 85, right associativity).
Notation "a _&_ b" := (sp_and   a b) (at level 80, right associativity).
Notation "a <~> b" := (sp_iff a b) (at level 95, no associativity).
Notation "'Top'" := sp_top.
Notation "'all' x , phi" := (sp_forall x phi) (at level 55).

Notation "'nu' X , phi" := (sp_nu X phi) (at level 55).

Notation "M |=M phi" := (satisfies_model M phi)
                        (left associativity, at level 50).
Notation "M |=T Gamma" := (satisfies_theory M Gamma)
    (left associativity, at level 50).
Notation "G |= phi" := (satisfies G phi) (left associativity, at level 50).

Notation "|^ phi ^|" := (defined phi) (at level 100).
Notation "|_ phi _|" := (total phi) (at level 100).
Notation "a ~=~ b" := (equal a b) (at level 100).
Notation "a !=~ b" := (not_equal a b) (at level 100).
Notation "x -< phi" := (member x phi) (at level 100).
Notation "x !-< phi" := (non_member x phi) (at level 100).
Notation "a <: b" := (includes a b) (at level 100).
Notation "a !<: b" := (not_includes a b) (at level 100).

Notation "pattern 'tautology'" := (Tautology_proof_rules pattern) (at level 2).
Notation "pattern 'proved'" := (AML_proof_system pattern) (at level 2).
Notation "theory |- pattern"  := (Provable theory pattern) (at level 1).

End AML_notations.
