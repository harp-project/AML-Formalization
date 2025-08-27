From Kore Require Export Syntax.

Section Freshness.

  Context {Σ : Signature}.

  Fixpoint free_evars {ex mu s}
                      (sTarget : sort)
                      (φ : Pattern ex mu s)
                      {struct φ} : gset (evar sTarget) :=
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
      => free_evars sTarget φ1 ∪ free_evars sTarget φ2
   | kore_app σ args
      => hlist_rect ∅ (fun _ _ x xs rest => free_evars sTarget x ∪ rest) args
   | kore_exists _ φ | kore_forall _ φ
   | kore_mu φ | kore_nu φ 
   | kore_not φ | kore_ceil _ φ | kore_floor _ φ
   | kore_inj _ _ φ
      => free_evars sTarget φ
   | kore_bevar _ | kore_fsvar _ | kore_bsvar _
   | kore_bot _ | kore_top _
   | kore_dv _ _
       => ∅
  end.

  Fixpoint free_svars {ex mu s}
                      (sTarget : sort)
                      (φ : Pattern ex mu s)
                      {struct φ} : gset (svar sTarget) :=
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
      => free_svars sTarget φ1 ∪ free_svars sTarget φ2
   | kore_app σ args
      => hlist_rect ∅ (fun _ _ x xs rest => free_svars sTarget x ∪ rest) args
   | kore_exists _ φ | kore_forall _ φ
   | kore_mu φ | kore_nu φ 
   | kore_not φ | kore_ceil _ φ | kore_floor _ φ
   | kore_inj _ _ φ
      => free_svars sTarget φ
   | kore_bevar _ | kore_fevar _ | kore_bsvar _
   | kore_bot _ | kore_top _
   | kore_dv _ _
       => ∅
  end.

  Definition fresh_evar {s} {ex mu}
      (sTarget : sort) (φ : Pattern s ex mu) :
      evar sTarget :=
    fresh (elements (free_evars sTarget φ)).
  Definition fresh_svar {s} {ex mu}
      (sTarget : sort) (φ : Pattern s ex mu) :
      svar sTarget :=
    fresh (elements (free_svars sTarget φ)).

  Lemma fresh_evar_is_fresh {s} {ex mu} (sTarget : sort) (φ : Pattern s ex mu) :
    fresh_evar sTarget φ ∉ free_evars sTarget φ.
  Proof.
    unfold fresh_evar.
    pose proof (is_fresh (free_evars sTarget φ)).
    set_solver.
  Defined.

  Lemma fresh_svar_is_fresh {s} {ex mu} (sTarget : sort) (φ : Pattern s ex mu) :
    fresh_svar sTarget φ ∉ free_svars sTarget φ.
  Proof.
    unfold fresh_evar.
    pose proof (is_fresh (free_svars sTarget φ)).
    set_solver.
  Defined.

End Freshness.
