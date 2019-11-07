Require Import String.

Section AML.

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
  | sp_mu (X : SVar) (phi : Sigma_pattern).

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

Fixpoint eSubstitution (phi : Sigma_pattern) (psi : Sigma_pattern) (x : EVar) :=
  match phi with
  | sp_var x' => if evar_eq_dec x x' 
                  then psi 
                  else sp_var x'
  | sp_set X => sp_set X
  | sp_const sigma => sp_const sigma
  | sp_app phi1 phi2 => sp_app (eSubstitution phi1 psi x)
                                (eSubstitution phi2 psi x)
  | sp_bottom => sp_bottom
  | sp_impl phi1 phi2 => sp_impl (eSubstitution phi1 psi x)
                                  (eSubstitution phi2 psi x)
  | sp_exists x' phi' => if (evar_eq_dec x' x) 
                          then sp_exists x' phi'
                          else sp_exists x' (eSubstitution phi' psi x)
  | sp_mu X phi' => sp_mu X (eSubstitution phi' psi x)
end.

Definition var (name : string) : Sigma_pattern :=
  sp_var (evar_c name).

Definition set (name : string) : Sigma_pattern :=
  sp_set (svar_c name).

End AML.
