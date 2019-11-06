Require Import String.

Inductive EVar : Set := evar_c (id : string).
Inductive SVar : Set := svar_c (id : string).
Inductive Sigma : Set := sigma_c (id : string).

Inductive Sigma_pattern : Set :=
  | sp_var (x : EVar)
  | sp_set (X : SVar)
  | sp_const (sigma : Sigma)
  | sp_app (phi1 phi2 : Sigma_pattern)
  | sp_bottom
  | sp_impl (phi1 phi2 : Sigma_pattern)
  | sp_exists (x : EVar) (phi : Sigma_pattern)
  | sp_mu (X : SVar) (phi : Sigma_pattern)
.

Definition is_svar_box (s : SVar) : bool :=
  match s with
  | svar_c id => eqb id "box"
  end
.

Inductive sp_context_e : Sigma_pattern -> Prop :=
  | c_box (x : SVar) (p : (is_svar_box x) = true ) : sp_context_e (sp_set x)
  | c_cons_l (spl spr : Sigma_pattern) (p : sp_context_e spl) : sp_context_e (sp_app spl spr)
  | s_cons_r (spl spr : Sigma_pattern) (p : sp_context_e spr) : sp_context_e (sp_app spl spr)
.

Definition evar_eq_dec : forall (x y : EVar), { x = y } + { x <> y }.
Proof.
  decide equality.
  exact (string_dec id id0).
Defined.

Definition svar_eq_dec : forall (x y : SVar), { x = y } + { x <> y }.
Proof.
  decide equality.
  exact (string_dec id id0).
Defined.

Definition sigma_eq_dec : forall (x y : Sigma), { x = y } + { x <> y }.
Proof.
  decide equality.
  exact (string_dec id id0).
Defined.

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

Definition sp_not (phi : Sigma_pattern) := sp_impl phi sp_bottom.
Definition sp_or  (phi1 phi2 : Sigma_pattern) := sp_impl (sp_not phi1) phi2.
Definition sp_and (phi1 phi2 : Sigma_pattern) :=
  sp_not (sp_or (sp_not phi1) (sp_not phi2)).
Definition sp_tatu := sp_not sp_bottom.
Definition sp_forall (x : EVar) (phi : Sigma_pattern) :=
  sp_not (sp_exists x (sp_not phi)).
(*nuX.phi*)

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

Definition var (name : string) : Sigma_pattern :=
  sp_var (evar_c name).

Definition set (name : string) : Sigma_pattern :=
  sp_set (svar_c name).

Definition simple_neg := (sp_not (set "X")).
Eval compute in (strictly_positive simple_neg (svar_c "X") = false).

Definition X_imp_X := (sp_impl (set "X") (set "X")).
Eval compute in (strictly_positive X_imp_X (svar_c "X") = false).
Eval compute in (strictly_positive (sp_not X_imp_X) (svar_c "X") = false).

Definition X_i_X_i_X := (sp_impl (set "X") ((sp_impl (set "X") (set "X")))).

Eval compute in (strictly_positive X_i_X_i_X (svar_c "X") = false).
Eval compute in (strictly_positive (sp_not X_i_X_i_X)(svar_c "X") = false).

Definition X_i_X_i_nX := (sp_impl (set "X") ((sp_impl (set "X") (sp_not (set "X"))))).

Eval compute in (strictly_positive X_i_X_i_nX (svar_c "X") = false).
Eval compute in (strictly_positive (sp_not X_i_X_i_nX) (svar_c "X") = true).
Check negb.

(* Fixpoint is_free (phi : Sigma_pattern) (x : EVar) : bool :=
  match phi with
  | sp_var y => negb (x = y)
  | sp_set X => true
  | sp_const sigma => true
  | sp_app phi1 phi2 => andb (is_free phi1 x) (is_free phi2 x)
  | sp_bottom => true
  | sp_impl phi1 phi2 => andb (is_free phi1 x) (is_free phi2 x)
  | sp_exists y phi => andb (negb (x = y)) (is_free phi x)
  end
. *)

Check e_subst_var.

(* Inductive application_context : Set :=
  | pattern (p : Sigma_pattern)
  | box
.
 *)
(* Inductive context : Sigma_pattern -> Set :=
  | box
  | ctx_app_l context Sigma_pattern
  | ctx_app_r Sigma_pattern context
.
 *)

Inductive got_tau : Sigma_pattern -> Prop :=
  | cons (phi : Sigma_partern) : got_tau (sp_impl sp_bottom phi)
.

Inductive got : Sigma_pattern -> Prop :=
  (* Modus ponens *)
  | E_mod_pon phi1 phi2 : got phi1 -> got (sp_impl phi1 phi2) -> got phi2

  (* Existential quantifier*)
  | E_ex_quan phi x y:
    got (sp_impl (e_subst_var phi y x) (sp_exists x phi))

  (* Existential generalization *)
  | E_ex_gen phi1 phi2 :
    got (sp_impl phi1 phi2) -> 
     ->
    got (sp_impl (sp_exists x phi1) phi2)


  (* Set Variable Substitution *)
  | E_svar_subst phi psi X : 
    got phi -> 
    got (e_subst_set phi psi X)

  (* Pre-Fixpoint *)
  | E_pre_fixp phi X :
    got (sp_impl
          (e_subst_set phi (sp_mu X phi) X)
          (sp_mu X phi))

  | E_kt phi psi X :
    got (sp_impl 
          (e_subst_set phi psi X)
          psi) ->
    got (sp_impl
          (sp_mu X phi)
          psi)

  (* Existence *)
  | E_existence x : got (sp_var x) -> got (sp_exists x (sp_var x))
.

Inductive got_c : sp_context_e -> Prop :=
   (* Propagation bottom *)
  | E_prop_bot context : 
    got_c (sp_impl context sp_bottom)

  (* Propagation disjunction *)
  | E_prop_dis phi1 phi2 C : 
    got_c (sp_impl _ (_ /\ _))

  (* Propagation exist *)
  | E_prop_ex phi x C :
    _ ->
    got_c (sp_impl _ (sp_exists x _))

  (* Framing *)
  | E_framing phi1 phi2 C :
    got (sp_impl phi1 phi2) ->
    got_c (sp_impl _ _)

  (* Singleton *)
  | E_singleton ? : 
    got_c (sp_not (
            _ /\ _))
.

Inductive got' : Sigma_partern -> Prop :=
  (* Existential quatifier*)
  | E_ex_quan : got' (sp_impl (e_subst_var phi y x) _)
.


(* Definition E_modus_ponens (phi1 phi2 : Sigma_partern) (p : forall phi1 phi2 : Sigma_pattern : sp_impl phi1 phi2)
  := phi2. *)

(* Inductive proof_step : Sigma_pattern -> Sigma_pattern -> Prop :=
(*   (* Propositional tautology*)
  | E_prop_tau phi : phi  *)

  (* Modus ponens *)
  | E_mod_pon (phi1 phi2 : Sigma_pattern) :
    proof_step
      (sp_and phi1 (sp_impl phi1 phi2))
      phi2

 (*  (* Existential quatifier*)
  | E_ex {phi y : Sigma_pattern} {x : EVar} (p : x : EVar, ) :
    proof_step (e_subst_var phi y x) (sp_exists x phi)
 *)
(*    (* Existential generalization *)
  | E_gen phi1 phi2 x :
    if not (FV x phi2) then
      proof_step
        (sp_impl phi1 phi2)
        (sp_impl (sp_exists x phi1) phi2)
    else
      fail_state
 *)
  (* Set variable substitution *)
  | E_subst (phi psi : Sigma_pattern) (X : SVar) :
    proof_step
      phi
      (e_subst_set phi psi X)

(*
  (* Existence *)
  | E_existence x :
    sp_exists x x

  (* Propagation bottom *)
  | E_prop_bot C :

  (* Propagation disjunction *)
  | E_prop_dis phi1 phi2 C

  (* Propagation exist *)
  | E_prop_ex phi x C

  (* Framing *)
  | E_framing phi1 phi2 C

  (* Pre-fixpoint *)
  | E_pre_fixp phi X

  (* Knaster-Tarski *)
  | E_KT phi psi X

  (* Singleton *)
  | E_singleton c1 c2 x phi *)
.

(*
Inductive context : Sigma_pattern -> Set :=
  | box
  | sp_app context Sigma_pattern
  | sp_app Sigma_pattern context
.
 *)
(* Inductive proof_result : ? :=
  | success (?)
  | fail
. *)

(* TO DO:
    - free variables: Context -> Set
    - eSubstitution for sets OK
x occurs free
x occurs bound
instance of x is bound or not -> identify the location in the tree

box, context : define inductively
 *)
 *)