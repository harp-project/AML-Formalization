(* *******************************~= MSFOL =~******************************* *)
Require Export FOL_helpers.
Import AML_notations.
Require Import Coq.Sets.Ensembles.
Require Import Coq.Vectors.Fin.
Require Import Coq.Vectors.VectorDef.
Import VectorNotations.
Open Scope string_scope.


Section MSFOL.

(* Definition 9. MSFOL definition *)
Inductive MSFOL_sorts : Set :=
| Nat
| List
| Cfg
| Term
.

Inductive MSFOL_var : Type :=
| M_var_c (id_M_var : string) (sort_M_var : MSFOL_sorts).
Inductive MSFOL_fun : Type := M_fun_c {id_M_fun : string}.
Inductive MSFOL_pred : Type := M_pred_c {id_M_pred : string}.

(* Record MSFOL_Structure := {
  SortSet : Ensemble MSFOL_sorts;
  Functions : MSFOL_fun -> _;
  Predicates : MSFOL_pred -> _;
}. *)

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


(* Substitue variable in term *)
Fixpoint t_subst_var (term : MSFOL_term) (t : MSFOL_term) (x : MSFOL_var)
: MSFOL_term :=
match term with
| MT_var x' => if mvar_eq_dec x x' then t else (MT_var x')
| MT_fun f params result_sort =>
    MT_fun f (VectorDef.map (fun y => t_subst_var y t x) params) result_sort
end.

(* Substitue variable in formula *)
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
  Domain : Type (* non-empty subset of SortSet *)
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
                             (* it is stated phi2 in paper *)
    negb (set_mem mvar_eq_dec x (f_free_vars phi1)) = true ->
    ((M_ex x, phi1) M~> phi2) MSFOL_proved

where "phi 'MSFOL_proved'" := (MSFOL_proof_system phi).


(* Section 4.2 *)
Definition MSAFOL_Sort := (AML_definition.const ("Sort")).

(* a function which corresponds: constants of AML  to  sorts of MSFOL *)
Fixpoint sort_fun_constant (s : MSFOL_sorts) (x : EVar) : Sigma_pattern :=
match s with
| Nat  => Functional_Constant (sigma_c("Nat")) x
| List => Functional_Constant (sigma_c("List")) x
| Cfg  => Functional_Constant (sigma_c("Cfg")) x
| Term => Functional_Constant (sigma_c("Term")) x
end.

Fixpoint sort_constant (s : MSFOL_sorts) : Sigma_pattern :=
match s with
| Nat  => (AML_definition.const ("Nat"))
| List => (AML_definition.const ("List"))
| Cfg  => (AML_definition.const ("Cfg"))
| Term => (AML_definition.const ("Term"))
end.

Definition Axiom_Sort (s : MSFOL_sorts) := (sort_constant s) -< MSAFOL_Sort.


Definition domain_symbol := AML_definition.const ("Domain symbol").
Definition Domain (sort : MSFOL_sorts) := domain_symbol $ (sort_constant sort).
Notation "'[[' s ']]'" := (Domain s) (at level 0).

(* Examples meanings: *)
Definition x_has_sort_s (x : EVar) (s : MSFOL_sorts) :=
  'x -< [[ s ]].

(* phi <: [[ s ]] states that all elements matching phi have sort s*)
Definition pattern_in_sort (phi : Sigma_pattern) (s : MSFOL_sorts) :=
  phi <: [[ s ]].

Definition Nonempty_Domain (s : MSFOL_sorts) :=  [[ s ]] !=~ Bot.

(* Introducing notations for Sorted quantification *)
(* For denoting "exists x : Nat . pattern" we introduce: *)
Definition sorted_ex_quan (x : EVar) (s : MSFOL_sorts) (phi : Sigma_pattern) :=
  (ex x, (('x -< [[ s ]]) _&_ phi)).
Notation "'ex_S' x : s , phi" :=
  (sorted_ex_quan x s phi) (at level 3, x at next level, s at next level).

(* For denoting "forall x : Nat . pattern" we introduce: *)
Definition sorted_all_quan (x : EVar) (s : MSFOL_sorts) (phi : Sigma_pattern) :=
  (all x, (('x -< [[ s ]]) ~> phi)).
Notation "'all_S' x : s , phi" :=
  (sorted_all_quan x s phi) (at level 3, x at next level, s at next level).

Lemma neg_cong G a b:
  G |- ( a ~=~  b) ->
  G |- (¬a ~=~ ¬b).
Proof.
  intros.
  pose (EQ := eq_evar_subst (evar_c "y") a b (¬' (evar_c "y")) G H).
  simpl in EQ. assumption.
Qed.

Lemma equal_unwrap (theory : Ensemble Sigma_pattern) (A B : Sigma_pattern) :
  theory |- (A ~=~ B) -> theory |- (A <~> B).
Admitted.
(*Proof.
  intros.
  unfold equal in H.
*)

(* (* Proposition 10. *)
Lemma forall_ex_equiv (theory : Ensemble Sigma_pattern):
  forall s : MSFOL_sorts, forall x : EVar, forall phi : Sigma_pattern,
  theory |- ((all_S x:s, phi) ~=~ (¬ (ex_S x:s, (¬ phi))) ).
Admitted.
(* Proof.
    intros.
    eapply proof_sys_intro.
    unfold equal. unfold sp_iff. unfold sp_and.
    eapply (Prop_disj (ctx_app_r definedness_symbol box)).

    unfold sorted_ex_quan. unfold sorted_all_quan. unfold sp_forall.
     unfold sp_or.

    unfold equal.  unfold sp_and. unfold sp_or.
*)*)

Example a x :
if evar_eq_dec x {| id_ev := "y" |} then True else False
.
Proof.
  destruct (evar_eq_dec x {| id_ev := "y" |}).
Abort.


Lemma ex_cong G a b x:
  G |- (       a  ~=~        b ) ->
  G |- ((ex x, a) ~=~ (ex x, b)).
Proof.
  intros.
  pose (EQ := eq_evar_subst (evar_c "y") a b (ex x, ' (evar_c "y")) G H).
  simpl in EQ. Check id_ev {| id_ev := "y" |}.
  Check evar_eq_dec x {| id_ev := "y" |}.
  
  case_eq (evar_eq_dec x {| id_ev := "y" |});
  intros.
  * pose (@left).
Admitted.

Lemma impl_congl G a b c:
  G |- ( a       ~=~  b      ) ->
  G |- ((a ~> c) ~=~ (b ~> c)).
Proof.
  intros.
  pose (EQ := eq_evar_subst (evar_c "y") a b ('(evar_c "y") ~> c) G H).
  simpl in EQ.
Admitted.

Lemma impl_congr G a b c:
  G |- (      a  ~=~       b ) ->
  G |- ((c ~> a) ~=~ (c ~> b)).
Admitted.

(* Proposition 10. *)
Lemma forall_ex_equiv G s x phi:
  G |- ((all_S x:s, phi) ~=~ (¬ (ex_S x:s, (¬ phi))) ).
Proof.
    intros.
    unfold sorted_ex_quan. unfold sorted_all_quan. unfold sp_forall.
    unfold sp_and. unfold sp_or. remember (' x -< [[s]]) as MSHIP.
    apply neg_cong.
    apply ex_cong.
    apply neg_cong.
    apply (eq_trans _ (¬(¬MSHIP) ~> phi) _ G).
    * apply impl_congl. apply (proof_sys_intro _ G (e_eq_nne _)).
    * apply impl_congr. apply (proof_sys_intro _ G (e_eq_nne _)).
Qed.

Lemma forall_ex_equiv_rev G s x phi:
  G |- (¬(all_S x:s, ¬phi) ~=~ (ex_S x:s, phi)).
Proof.
    intros.
    unfold sorted_ex_quan. unfold sorted_all_quan. unfold sp_forall.
    unfold sp_and. unfold sp_or. remember (' x -< [[s]]) as MSHIP.
    apply eq_symm.
    apply (eq_trans _ (¬ (¬ ex x, (¬ (¬ (¬ MSHIP) ~> ¬ phi)))) _ G).
    * apply (proof_sys_intro _ G (e_eq_nne _)).
    * apply neg_cong.
      apply neg_cong.
      apply ex_cong.
      apply neg_cong.
      apply impl_congl.
      apply eq_symm.
      apply (proof_sys_intro _ G (e_eq_nne _)).
Qed.

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

Local Open Scope vector_scope.
Program Fixpoint _gen_x_vec (n m : nat) : VectorDef.t EVar n :=
match n with
| O => []
| S n' => [(evar_c(String.append "x" (string_of_nat(m-n+1))))] ++
          (_gen_x_vec n' m)
end.

Fixpoint gen_x_vec (n : nat) : VectorDef.t EVar n :=
  _gen_x_vec n n.

Fixpoint Function
  {n : nat} (fn : Sigma) (sorts : VectorDef.t MSFOL_sorts n)
  (y_sort : MSFOL_sorts)
: Sigma_pattern :=
let y := (evar_c("y")) in
let vars := gen_x_vec n in
let var_patterns := VectorDef.map sp_var vars in
let applied_params := VectorDef.fold_left sp_app (sp_const fn) var_patterns in
let core := ex_S y : y_sort, (applied_params ~=~ 'y )in
let foralls := VectorDef.map2
                (fun var s => (fun phi => all_S var : s, phi))
                vars sorts in
  VectorDef.fold_right (fun spl spr => spl spr) foralls core.

(* Functional notation of the function *)
Notation "f : '-->' s" := (Function f [] s) (at level 3).
Notation "f : s1 '-->' s" := (Function f [ s1 ] s) (at level 3).
Notation "f : s1 'X' s2 'X' .. 'X' sn '-->' s" :=
  (Function f (vc _ s1 _ (vc _ s2 _ .. (vc _ sn _ (vn _)) .. )) s) (at level 3).

(* Example for functional notation *)
Definition f := (sigma_c "f") : --> List.
Definition fib := (sigma_c "fib") : Nat --> Nat.
Definition volume := (sigma_c "volume") : Nat X Nat X Nat --> Nat.


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
    M_var_c id sort => sp_and ((AML_definition.const (id)) -< [[ sort ]]) end
| MT_fun f params r_sort => VectorDef.fold_right get_vars params
end.

Fixpoint well_sorted_term (term : MSFOL_term) : Sigma_pattern :=
match term with
| MT_var x => match x with M_var_c id sort =>
  ((AML_definition.const (id)) -< [[ sort ]]) end
| MT_fun f params r_sort => VectorDef.fold_right get_vars params Top
end.

Fixpoint well_sorted_formula (formula : MSFOL_formula) : Sigma_pattern :=
match formula with
| MF_pred p params => VectorDef.fold_right get_vars params Top
| MF_bottom => Top
| MF_impl lhs rhs => sp_and (well_sorted_formula lhs) (well_sorted_formula rhs)
| MF_exists x phi =>
    sp_and (match x with M_var_c id sort =>
              ((AML_definition.const (id)) -< [[ sort ]])
            end)
           (well_sorted_formula phi)
end.


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


Lemma MSFOL_wellformed_terms y :
  forall Gamma_MSFOL : Ensemble Sigma_pattern, forall t : MSFOL_term,
  Gamma_MSFOL |- ((well_sorted_term t) ~>
    ex_S y : (term_sort t), (term_to_AML t) ~=~ 'y).
Admitted.

Definition MSFOL_wellformed_formulas :=
  forall Gamma_MSFOL : Ensemble Sigma_pattern, forall phi : MSFOL_formula,
  Gamma_MSFOL |- ((well_sorted_formula phi) ~>
    ((formula_to_AML phi) ~=~ Top) _|_ (((formula_to_AML phi) ~=~ Bot))).



(* MSFOL theories *)
Definition MSFOL_axiom_to_AML (phi : MSFOL_formula) :=
  well_sorted_formula(phi) ~> ((formula_to_AML phi) ~=~ Top).

(* for theories conversion for each element of the theory will be done *)
(* Fixpoint MSFOL_to_AML' (theory : Ensembles MSFOL_formula)
: Coq.Sets.Ensembles Sigma_pattern:=
match theory with
| Add _ elem => Add _ (MSFOL_to_AML elem)
| Empty_set _ => Empty_set Sigma_pattern
end. *)


(* Theorem 13. *)
(* Theorem preservation :
  forall Omega : Ensemble MSFOL_formula, forall Gamma : Ensemble Sigma_pattern,
  forall phi : MSFOL_formula
  Omega |-MSFOL phi -> Gamma_MSFOL |- (formula_to_AML phi). *)


(* Definition 14. MSFOL restricted *)
(*  *)


(* Theorem 15. *)
(* TODO: MSFOL theory conversion to AML conversion *)
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
End MSFOL.

Module MSFOL_notations.
Notation "'M_Bot'" := (MF_bottom).
Notation "a 'M~>' b" := (MF_impl a b) (at level 90, right associativity,
                                       b at level 200).
Notation "'M_ex' x , phi" := (MF_exists x phi) (at level 55).

Notation "'M¬' phi" := (MF_not phi) (at level 75).
Notation "a M|_ b" := (MF_or a b) (at level 85, right associativity).
Notation "a M&_ b" := (MF_and a b) (at level 80, right associativity).
Notation "a <M~> b" := (MF_iff a b) (at level 95, no associativity).
Notation "'M_Top'" := MF_top.
Notation "'M_all' x , phi" := (MF_forall x phi) (at level 55).

Notation "pattern 'MSFOL_tautology'" :=
  (MSFOL_tautology_proof_rules pattern) (at level 2).
Notation "phi 'MSFOL_proved'" := (MSFOL_proof_system phi) (at level 2).

Notation "'[[' s ']]'" := (Domain s) (at level 0).

Notation "'ex_S' x : s , phi" :=
  (sorted_ex_quan x s phi) (at level 3, x at next level, s at next level).

Notation "'all_S' x : s , phi" :=
  (sorted_all_quan x s phi) (at level 3, x at next level, s at next level).

Notation "f : '-->' s" := (Function f [] s) (at level 3).
Notation "f : s1 '-->' s" := (Function f [ s1 ] s) (at level 3).
Notation "f : s1 'X' s2 'X' .. 'X' sn '-->' s" :=
  (Function f (vc _ s1 _ (vc _ s2 _ .. (vc _ sn _ (vn _)) .. )) s) (at level 3).

Notation "p 'pred'" := (Predicate p []) (at level 3).
Notation "p '<::' s1" := (Predicate p [ s1 ]) (at level 3).
Notation "p '=<' s1 'X' s2 'X' .. 'X' sn" :=
  (Predicate p (vc _ s1 _ (vc _ s2 _ .. (vc _ sn _ (vn _)) .. ))) (at level 3).

End MSFOL_notations.
