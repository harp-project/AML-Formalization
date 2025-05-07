From Kore Require Export Syntax Freshness.

Import Kore.Syntax.Notations.

Tactic Notation "hlist_map" uconstr(f) "in" ident(h) :=
  let y := fresh in let H := fresh in
  induction h as [ | ? ? y _ H];
  [left | right];
  [eapply f; eauto using y | exact H].

Tactic Notation "hlist_foldr" uconstr(f) "with" uconstr(def) "in" ident(h) :=
let y := fresh in let H := fresh in
  induction h as [ | ?x ?xs y _ H ];
  [exact def | eapply f];
  [exact y | exact H].

Section Substitution.
  Context {Σ : Signature}.

  Fixpoint inc_var {ex ex' ex'' mu mu' mu''} {s}
    (base : Pattern (ex ++ ex'') (mu ++ mu'') s)
    : Pattern (ex ++ ex' ++ ex'') (mu ++ mu' ++ mu'') s.
  Proof.
    revert s ex ex' ex'' mu mu' mu'' base.
    fix IH 8.
    intros.
    dependent destruction base.
    - apply kore_bevar, InTy_app, idx.
    - apply kore_bsvar, InTy_app, idx.
    - apply kore_fevar, x.
    - apply kore_fsvar, X.
    - apply kore_app.
      (* hlist_map inc_evar in h. *)
      (* epose proof (@hlist_rect _ _
        (fun l => hlist _ l) hnil). *)
      (* refine (hlist_rect []%hlist
            (fun _ _ x xs rest => _) args). *)
      hlist_map inc_var in args.
    (* bot *)
    - exact (kore_bot s).
    (* top *)
    - exact (kore_top s).
    (* not *)
    - apply kore_not; apply inc_var.
      exact base.
    (* and *)
    - apply kore_and; apply inc_var.
      exact base1. exact base2.
    (* or *)
    - apply kore_or; apply inc_var.
      exact base1. exact base2.
    (* imp *)
    - apply kore_imp; apply inc_var.
      exact base1. exact base2.
    (* iff *)
    - apply kore_iff; apply inc_var.
      exact base1. exact base2.
    (* exists *)
    - eapply kore_exists. instantiate (1 := s_var).
      rewrite app_comm_cons_defined.
      apply inc_var.
      rewrite <- app_comm_cons_defined.
      exact base.
    (* forall *)
    - eapply kore_forall. instantiate (1 := s_var).
      rewrite app_comm_cons_defined.
      apply inc_var.
      rewrite <- app_comm_cons_defined.
      exact base.
    (* mu *)
    - eapply kore_mu.
      rewrite app_comm_cons_defined.
      apply inc_var.
      rewrite <- app_comm_cons_defined.
      exact base.
    (* nu *)
    - eapply kore_nu.
      rewrite app_comm_cons_defined.
      apply inc_var.
      rewrite <- app_comm_cons_defined.
      exact base.
    (* ceil *)
    - eapply kore_ceil; apply inc_var.
      exact base.
    (* floor *)
    - eapply kore_floor; apply inc_var.
      exact base.
    (* equals *)
    - eapply kore_equals; apply inc_var.
      exact base1. exact base2.
    (* in *)
    - eapply kore_in; apply inc_var.
      exact base1. exact base2.
    (* inj *)
    - eapply kore_inj. exact pf. apply inc_var. exact base.
  Defined.

  Arguments inc_var {_} {_} {_} {_} {_} {_} {_} !_.

  (*
  The following two function substitute the `(length ex)`th index in the dB index
  `idx` by `ψ`. The result is likely a `kore_bevar idx` (`kore_bsvar dbi` resp.),
  except when `idx` is the `(length ex)`th index, in which case it is ψ, with its
  context extended with `ex`.
  *)
  Fixpoint sub_evar {s s'} {ex ex' mu}
    (idx : InTy s (ex ++ s' :: ex'))
    (ψ : Pattern ex' mu s') {struct idx}
      : Pattern (ex ++ ex') mu s.
  Proof.
    refine (match idx in (InTy o l) return (o = s -> l = ex ++ s' :: ex' -> Pattern (ex ++ ex') mu s) with
            | In_nil => _
            | In_cons idx => _
            end eq_refl eq_refl); intros; subst.
    - destruct ex; simpl in *; apply cons_eq_inv in H0 as [-> ->].
      + exact ψ.
      + apply kore_bevar, In_nil.
    - destruct ex; simpl in *; apply cons_eq_inv in H0 as [-> ->].
      + apply kore_bevar, idx.
      + specialize (sub_evar _ _ _ _ _ idx ψ).
        apply (@inc_var [] [s1] (ex ++ ex') [] [] mu _).
        simpl. exact sub_evar.
  Defined.

  Arguments sub_evar {_} {_} {_} {_} {_} !_ _.

  Fixpoint sub_svar {s s'} {ex mu mu'}
    (dbi : InTy s (mu ++ s' :: mu'))
    (ψ : Pattern ex mu' s') {struct dbi}
    : Pattern ex (mu ++ mu') s.
  Proof.
    refine (match dbi in (InTy o l) return (o = s -> l = mu ++ s' :: mu' -> Pattern ex (mu ++ mu') s) with
            | In_nil => _
            | In_cons idx => _
            end eq_refl eq_refl); intros; subst.
    - destruct mu; simpl in *; apply cons_eq_inv in H0 as [-> ->].
      + exact ψ.
      + apply kore_bsvar, In_nil.
    - destruct mu; simpl in *; apply cons_eq_inv in H0 as [-> ->].
      + apply kore_bsvar, idx.
      + specialize (sub_svar _ _ _ _ _ idx ψ).
        apply (@inc_var [] [] ex [] [s1] (mu ++ mu')).
        simpl. exact sub_svar.
  Defined.

  Arguments sub_svar {_} {_} {_} {_} {_} !_ _.

  Fixpoint bevar_subst ex {ex' mu : list sort} {s s'}
    (ψ : Pattern ex' mu s')
    (φ : Pattern (ex ++ s' :: ex') mu s) {struct φ}
    : Pattern (ex ++ ex') mu s.
  Proof.
    intros.
    dependent destruction φ.
    (* bevar *)
    - eapply sub_evar; eauto.
    (* bsvar *)
    - apply kore_bsvar. exact idx.
    (* fevar *)
    - apply kore_fevar, x.
    (* fsvar *)
    - apply kore_fsvar, X.
    (* app *)
    - apply kore_app.
      hlist_map bevar_subst in args.
    (* bot *)
    - exact (kore_bot s).
    (* top *)
    - exact (kore_top s).
    (* not *)
    - exact (kore_not (bevar_subst _ _ _ _ _ ψ φ)).
    (* and *)
    - exact (kore_and (bevar_subst _ _ _ _ _ ψ φ1)
                      (bevar_subst _ _ _ _ _ ψ φ2)).
    (* or *)
    - exact (kore_or (bevar_subst _ _ _ _ _ ψ φ1)
                     (bevar_subst _ _ _ _ _ ψ φ2)).
    (* imp *)
    - exact (kore_imp (bevar_subst _ _ _ _ _ ψ φ1)
                      (bevar_subst _ _ _ _ _ ψ φ2)).
    (* iff *)
    - exact (kore_iff (bevar_subst _ _ _ _ _ ψ φ1)
                      (bevar_subst _ _ _ _ _ ψ φ2)).
    (* exists *)
    - eapply kore_exists.
      rewrite app_comm_cons_defined.
      eapply bevar_subst. exact ψ.
      rewrite <- app_comm_cons_defined. exact φ.
    (* forall *)
    - eapply kore_forall.
      rewrite app_comm_cons_defined.
      eapply bevar_subst. exact ψ.
      rewrite <- app_comm_cons_defined. exact φ.
    (* mu *)
    - eapply kore_mu.
      eapply bevar_subst. 2: exact φ.
      apply (@inc_var [] [] ex' [] [s] mu s').
      assumption.
    (* nu *)
    - eapply kore_nu.
      eapply bevar_subst. 2: exact φ.
      apply (@inc_var [] [] ex' [] [s] mu s').
      assumption.
    (* ceil *)
    - eapply kore_ceil.
      eapply bevar_subst.
      exact ψ. exact φ.
    (* floor *)
    - eapply kore_ceil.
      eapply bevar_subst.
      exact ψ. exact φ.
    (* equals *)
    - exact (kore_equals _ (bevar_subst _ _ _ _ _ ψ φ1)
                      (bevar_subst _ _ _ _ _ ψ φ2)).
    (* in *)
    - exact (kore_in _ (bevar_subst _ _ _ _ _ ψ φ1)
                      (bevar_subst _ _ _ _ _ ψ φ2)).
    (* inj *)
    - exact (kore_inj _ pf (bevar_subst _ _ _ _ _ ψ φ)).
  Defined.

  Arguments bevar_subst _ {_} {_} {_} {_} !_ _.


  Fixpoint bsvar_subst {ex} mu {mu' : list sort} {s s'}
    (ψ : Pattern ex mu' s')
    (φ : Pattern ex (mu ++ s'::mu') s) {struct φ}
    : Pattern ex (mu ++ mu') s.
  Proof.
    intros.
    dependent destruction φ.
    (* bevar *)
    - eapply kore_bevar. exact idx.
    (* bsvar *)
    - eapply sub_svar; eauto.
    (* fevar *)
    - apply kore_fevar, x.
    (* fsvar *)
    - apply kore_fsvar, X.
    (* app *)
    - apply kore_app.
      hlist_map bsvar_subst in args.
    (* bot *)
    - exact (kore_bot s).
    (* top *)
    - exact (kore_top s).
    (* not *)
    - exact (kore_not (bsvar_subst _ _ _ _ _ ψ φ)).
    (* and *)
    - exact (kore_and (bsvar_subst _ _ _ _ _ ψ φ1)
                      (bsvar_subst _ _ _ _ _ ψ φ2)).
    (* or *)
    - exact (kore_or (bsvar_subst _ _ _ _ _ ψ φ1)
                     (bsvar_subst _ _ _ _ _ ψ φ2)).
    (* imp *)
    - exact (kore_imp (bsvar_subst _ _ _ _ _ ψ φ1)
                      (bsvar_subst _ _ _ _ _ ψ φ2)).
    (* iff *)
    - exact (kore_iff (bsvar_subst _ _ _ _ _ ψ φ1)
                      (bsvar_subst _ _ _ _ _ ψ φ2)).
    (* exists *)
    - eapply kore_exists.
      eapply bsvar_subst. 2: exact φ.
      apply (@inc_var [] [s_var] ex [] [] mu' s').
      assumption.
    (* forall *)
    - eapply kore_forall.
      eapply bsvar_subst. 2: exact φ.
      apply (@inc_var [] [s_var] ex [] [] mu' s').
      assumption.
    (* mu *)
    - eapply kore_mu.
      rewrite app_comm_cons_defined.
      eapply bsvar_subst. exact ψ.
      rewrite <- app_comm_cons_defined. exact φ.
    (* nu *)
    - eapply kore_nu.
      rewrite app_comm_cons_defined.
      eapply bsvar_subst. exact ψ.
      rewrite <- app_comm_cons_defined. exact φ.
    (* ceil *)
    - eapply kore_ceil.
      eapply bsvar_subst.
      exact ψ. exact φ.
    (* floor *)
    - eapply kore_ceil.
      eapply bsvar_subst.
      exact ψ. exact φ.
    (* equals *)
    - exact (kore_equals _ (bsvar_subst _ _ _ _ _ ψ φ1)
                      (bsvar_subst _ _ _ _ _ ψ φ2)).
    (* in *)
    - exact (kore_in _ (bsvar_subst _ _ _ _ _ ψ φ1)
                      (bsvar_subst _ _ _ _ _ ψ φ2)).
    (* inj *)
    - exact (kore_inj _ pf (bsvar_subst _ _ _ _ _ ψ φ)).
  Defined.

  Arguments bevar_subst {_} _ {_} {_} {_} !_ _.

End Substitution.

Module Notations.

  Notation "p '^[' 'evar:' s ↦ t ']'" :=
    (bevar_subst s t p) : kore_scope.
  Notation "p '^[' 'svar:' s ↦ t ']'" :=
    (bsvar_subst s t p) : kore_scope.

End Notations.

Section Substitution.
  Import Notations.

  Context {Σ : Signature}.

  Lemma inc_var_size : forall s ex ex' ex'' mu mu' mu'' (φ : Pattern (ex ++ ex'') (mu ++ mu'') s),
    pat_size (@inc_var Σ ex ex' ex'' mu mu' mu'' s φ) =
    pat_size φ.
  Proof.
    fix IH 8. intros.
    dependent destruction φ; try reflexivity.
    all: simpl; try by auto.
    - simpl. induction args.
      * by auto.
      * simpl. rewrite IH. by auto.
    - cbn.
      specialize (IH s (s_var :: ex) ex' ex'' mu mu' mu'' φ).
      f_equal. assumption.
    - cbn.
      specialize (IH s (s_var :: ex) ex' ex'' mu mu' mu'' φ).
      f_equal. assumption.
    - cbn.
      specialize (IH s ex ex' ex'' (s :: mu) mu' mu'' φ).
      f_equal. assumption.
    - cbn.
      specialize (IH s ex ex' ex'' (s :: mu) mu' mu'' φ).
      f_equal. assumption.
  Defined.

  Lemma sub_evar_size s s' ex ex' mu o idx:
    pat_size (@sub_evar Σ s s' ex ex' mu idx (kore_fevar o)) = 1.
  Proof.
    dependent induction ex; simpl in *.
    * dependent destruction idx; cbn; reflexivity.
    * dependent destruction idx; cbn. reflexivity.
      epose proof inc_var_size _ [] [a] (ex ++ ex') [] [] mu (sub_evar idx (kore_fevar o)).
      rewrite IHex in H.
      exact H.
  Defined.

  Lemma bevar_subst_size : forall ex ex' mu s s'
    (φ : Pattern (ex ++ s' :: ex') mu s)
    o,
      pat_size (bevar_subst ex (kore_fevar o) φ) =
      pat_size φ.
  Proof.
    fix IH 6.
    intros.
    dependent destruction φ; simpl; try reflexivity.
    all: try by auto.
    - autounfold with kore.
      simpl. clear IH.
      apply sub_evar_size.
    - induction args; simpl.
      + reflexivity.
      + simpl. by auto.
    - specialize (IH (s_var :: ex) ex' mu s s').
      cbn. by f_equal.
    - specialize (IH (s_var :: ex) ex' mu s s').
      cbn. by f_equal.
    - specialize (IH ex ex' (s :: mu) s s').
      cbn. by f_equal.
    - specialize (IH ex ex' (s :: mu) s s').
      cbn. by f_equal.
  Defined.

  Lemma sub_svar_size s s' ex mu mu' o idx:
    pat_size (@sub_svar Σ s s' ex mu mu' idx (kore_fsvar o)) = 1.
  Proof.
    dependent induction mu; simpl in *.
    * dependent destruction idx; cbn; reflexivity.
    * dependent destruction idx; cbn. reflexivity.
      epose proof inc_var_size _ [] [] ex [] [a] (mu ++ mu') (sub_svar idx (kore_fsvar o)).
      rewrite IHmu in H.
      exact H.
  Defined.

  Lemma bsvar_subst_size : forall ex mu mu' s s'
    (φ : Pattern ex (mu ++ s' :: mu') s)
    o,
      pat_size (bsvar_subst mu (kore_fsvar o) φ) =
      pat_size φ.
  Proof.
    fix IH 6.
    intros.
    dependent destruction φ; simpl; try reflexivity.
    all: try by auto.
    - autounfold with kore.
      simpl. clear IH.
      apply sub_svar_size.
    - induction args; simpl.
      + reflexivity.
      + simpl. by auto.
    - specialize (IH (s_var :: ex) mu mu' s s').
      cbn. by f_equal.
    - specialize (IH (s_var :: ex) mu mu' s s').
      cbn. by f_equal.
    - specialize (IH ex (s :: mu) mu' s s').
      cbn. by f_equal.
    - specialize (IH ex (s :: mu) mu' s s').
      cbn. by f_equal.
  Defined.

End Substitution.