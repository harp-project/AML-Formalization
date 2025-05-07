From Kore Require Export Syntax.

Section Freshness.

  Context {Σ : Signature}.

  Fixpoint free_evars {ex mu s}
                      (φ : Pattern ex mu s)
                      (sTarget : sort) {struct φ} : gset (evar sTarget) :=
  match φ with
   | @kore_fevar _ _ _ var_sort x =>
       (* var_sort = s in this case *)
       match decide (sTarget = var_sort) with
       | left H => {[eq_rect_r evar x H]}
       | right _ => ∅
       end
   | kore_imp φ1 φ2 | kore_iff φ1 φ2
   | kore_and φ1 φ2 | kore_or φ1 φ2
   | kore_equals _ φ1 φ2 | kore_in _ φ1 φ2
      => free_evars φ1 sTarget ∪ free_evars φ2 sTarget
   | kore_app σ args
      => hlist_rect ∅ (fun _ _ x xs rest => free_evars x sTarget ∪ rest) args
   | kore_exists _ φ | kore_forall _ φ
   | kore_mu φ | kore_nu φ 
   | kore_not φ | kore_ceil _ φ | kore_floor _ φ
      => free_evars φ sTarget
   | kore_bevar _ | kore_fsvar _ | kore_bsvar _
   | kore_bot _ | kore_top _ => ∅
  end.

  Fixpoint free_svars {ex mu s}
                      (φ : Pattern ex mu s)
                      (sTarget : sort) {struct φ} : gset (svar sTarget) :=
  match φ with
   | @kore_fsvar _ _ _ var_sort X =>
       (* var_sort = s in this case *)
       match decide (sTarget = var_sort) with
       | left H => {[eq_rect_r svar X H]}
       | right _ => ∅
       end
   | kore_imp φ1 φ2 | kore_iff φ1 φ2
   | kore_and φ1 φ2 | kore_or φ1 φ2
   | kore_equals _ φ1 φ2 | kore_in _ φ1 φ2
      => free_svars φ1 sTarget ∪ free_svars φ2 sTarget
   | kore_app σ args
      => hlist_rect ∅ (fun _ _ x xs rest => free_svars x sTarget ∪ rest) args
   | kore_exists _ φ | kore_forall _ φ
   | kore_mu φ | kore_nu φ 
   | kore_not φ | kore_ceil _ φ | kore_floor _ φ
      => free_svars φ sTarget
   | kore_bevar _ | kore_fevar _ | kore_bsvar _
   | kore_bot _ | kore_top _ => ∅
  end.

  Definition fresh_evar {s} {ex mu}
      (sTarget : sort) (φ : Pattern s ex mu) :
      evar sTarget :=
    fresh (elements (free_evars φ sTarget)).
  Definition fresh_svar {s} {ex mu}
      (sTarget : sort) (φ : Pattern s ex mu) :
      svar sTarget :=
    fresh (elements (free_svars φ sTarget)).

End Freshness.
