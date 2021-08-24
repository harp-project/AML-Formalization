From Coq Require Import ssreflect ssrfun ssrbool.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From stdpp Require Import base pmap gmap.
From MatchingLogic Require Import Syntax.

Section named.
  Context {Σ : Signature}.
  Existing Instance variables.

  Inductive NamedPattern : Set :=
  | npatt_evar (x : evar)
  | npatt_svar (X : svar)
  | npatt_sym (sigma : symbols)
  | npatt_app (phi1 phi2 : NamedPattern)
  | npatt_bott
  | npatt_imp (phi1 phi2 : NamedPattern)
  | npatt_exists (x : evar) (phi : NamedPattern)
  | npatt_mu (X : svar) (phi : NamedPattern)
  .

  Instance NamedPattern_eqdec : EqDecision NamedPattern.
  Proof.
    unfold EqDecision. intros. unfold Decision. decide equality.
    - apply evar_eqdec.
    - apply svar_eqdec.
    - apply sym_eq.
    - apply evar_eqdec.
    - apply svar_eqdec.
  Qed.

  Check gmap.
  Definition EVarMap := gmap db_index evar.
  Definition SVarMap := gmap db_index svar.

  (* TODO: use kmap. Check kmap. *)
  Definition evm_incr (evm : EVarMap) : EVarMap :=
    list_to_map (map (fun kv => (S (fst kv), snd kv)) (map_to_list evm)).

  Definition svm_incr (svm : SVarMap) : SVarMap :=
    list_to_map (map (fun kv => (S (fst kv), snd kv)) (map_to_list svm)).

  Definition evm_fresh (evm : EVarMap) (ϕ : Pattern) : evar
    := evar_fresh (elements (free_evars ϕ ∪ (list_to_set (map snd (map_to_list evm))))).

  Definition svm_fresh (svm : SVarMap) (ϕ : Pattern) : svar
    := svar_fresh (elements (free_svars ϕ ∪ (list_to_set (map snd (map_to_list svm))))).
  
  Fixpoint to_NamedPattern' (ϕ : Pattern) (evm : EVarMap) (svm : SVarMap)
    : NamedPattern * EVarMap * SVarMap :=
    match ϕ with
    | patt_free_evar x => (npatt_evar x, evm, svm)
    | patt_free_svar X => (npatt_svar X, evm, svm)
    | patt_bound_evar n =>
      (if (evm !! n) is Some x then npatt_evar x else npatt_bott, evm, svm)
    | patt_bound_svar n =>
      (if (svm !! n) is Some X then npatt_svar X else npatt_bott, evm, svm)
    | patt_sym s => (npatt_sym s, evm, svm)
    | patt_app phi1 phi2 =>
      let: (nphi1, evm', svm') := to_NamedPattern' phi1 evm svm in
      let: (nphi2, evm'', svm'') := to_NamedPattern' phi2 evm' svm' in
      (npatt_app nphi1 nphi2, evm'', svm'')
    | patt_bott => (npatt_bott, evm, svm)
    | patt_imp phi1 phi2 =>
      let: (nphi1, evm', svm') := to_NamedPattern' phi1 evm svm in
      let: (nphi2, evm'', svm'') := to_NamedPattern' phi2 evm' svm' in
      (npatt_imp nphi1 nphi2, evm'', svm'')
    | patt_exists phi =>
      let: x := evm_fresh evm phi in
      let: evm_ex := <[0:=x]>(evm_incr evm) in
      let: (nphi, evm', svm') := to_NamedPattern' phi evm_ex svm in
      (npatt_exists x nphi, evm', svm')
    | patt_mu phi =>
      let: X := svm_fresh svm phi in
      let: svm_ex := <[0:=X]>(svm_incr svm) in
      let: (nphi, evm', svm') := to_NamedPattern' phi evm svm_ex in
      (npatt_mu X nphi, evm', svm')
    end.

  
  
End named.
