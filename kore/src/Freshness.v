From Kore Require Export Syntax.

Section Freshness.

  Context {Σ : Signature}.

  Fixpoint free_evars (φ : Pattern) {struct φ} : gset evar :=
  match φ with
   | kore_fevar x => {[x]}
   | kore_imp φ1 φ2 | kore_iff φ1 φ2
   | kore_and φ1 φ2 | kore_or φ1 φ2
   | kore_equals _ _ φ1 φ2 | kore_in _ _ φ1 φ2
      => free_evars φ1 ∪ free_evars φ2
   | kore_app σ args
      => foldr (fun x acc => free_evars x ∪ acc) ∅ args
   | kore_exists _ φ | kore_forall _ φ
   | kore_mu _ φ | kore_nu _ φ 
   | kore_not φ | kore_ceil _ _ φ | kore_floor _ _ φ
      => free_evars φ
   | kore_bevar _ | kore_fsvar _ | kore_bsvar _
   | kore_bot _ | kore_top _ => ∅
  end.

  Fixpoint free_svars (φ : Pattern) {struct φ} : gset svar :=
  match φ with
   | kore_fsvar X => {[X]}
   | kore_imp φ1 φ2 | kore_iff φ1 φ2
   | kore_and φ1 φ2 | kore_or φ1 φ2
   | kore_equals _ _ φ1 φ2 | kore_in _ _ φ1 φ2
      => free_svars φ1 ∪ free_svars φ2
   | kore_app σ args
      => foldr (fun x acc => free_svars x ∪ acc) ∅ args
   | kore_exists _ φ | kore_forall _ φ
   | kore_mu _ φ | kore_nu _ φ 
   | kore_not φ | kore_ceil _ _ φ | kore_floor _ _ φ
      => free_svars φ
   | kore_bevar _ | kore_fevar _ | kore_bsvar _
   | kore_bot _ | kore_top _ => ∅
  end.

  Fixpoint dep_filter {A} (f : A -> bool) (l : list A) {struct l} :
    list {a : A & f a} :=
  match l with
    | [] => []
    | x::xs =>
      (if f x as b0 return f x = b0 -> list {a : A & f a}
      then fun P => existT x P :: dep_filter f xs
      else fun P => dep_filter f xs
      ) eq_refl
  end.


  Definition fresh_evar (s : sort) (φ : Pattern) : 
    { x : evar & decide (evar_sort x = s) }.
  Proof.
    pose (elements (free_evars φ)) as fs.
    pose (dep_filter (fun x => decide (evar_sort x = s)) fs) as filtered.
    simpl in filtered.
    exact (fresh filtered).
  Defined.
  Definition fresh_svar (s : sort) (φ : Pattern) :
    { x : svar & decide (svar_sort x = s) }.
  Proof.
    pose (elements (free_svars φ)) as fs.
    pose (dep_filter (fun x => decide (svar_sort x = s)) fs) as filtered.
    simpl in filtered.
    exact (fresh filtered).
  Defined.


End Freshness.