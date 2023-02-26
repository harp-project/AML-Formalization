From Coq Require Import ssreflect ssrfun ssrbool.

From Coq Require Import Strings.String.
From Coq Require Import Logic.PropExtensionality Logic.Eqdep_dec.

From stdpp Require Export base gmap fin_sets sets list countable.
From MatchingLogic Require Import
  Syntax
  DerivedOperators_Syntax
  ProofSystem
  ProofInfo
  Utils.stdpp_ext
.
From MatchingLogicProver Require Import Named NamedProofSystem.

From stdpp Require Import base finite gmap mapset listset_nodup numbers propset list pretty strings.

Section ProofConversionAbstractStateless.

  Class Ln2NamedProperties
    {Σ : Signature}
    (l2n : Pattern -> NamedPattern)
    := mkLn2NamedProperties {
        l2n_imp: forall ϕ₁ ϕ₂, l2n (patt_imp ϕ₁ ϕ₂) = npatt_imp (l2n ϕ₁) (l2n ϕ₂) ;
        l2n_app: forall ϕ₁ ϕ₂, l2n (patt_app ϕ₁ ϕ₂) = npatt_app (l2n ϕ₁) (l2n ϕ₂) ;
        l2n_bott : l2n patt_bott = npatt_bott ;
        l2n_nwf : forall ϕ, named_well_formed (l2n ϕ) = true;
        ebody : Pattern -> NamedPattern ;
        fe : Pattern -> evar -> evar ;
        ename : Pattern -> evar ;
        l2n_evar_open : forall ϕ y, l2n (evar_open y 0 ϕ) = rename_free_evar (ebody ϕ) (fe ϕ y) (ename ϕ) ;
        l2n_ex : forall ϕ', l2n (patt_exists ϕ') = npatt_exists (ename ϕ') (ebody ϕ') ;
        l2n_eqevar : evar -> Pattern -> evar ;
        l2n_exists_quantify : forall x ϕ, l2n (exists_quantify x ϕ) = npatt_exists (l2n_eqevar x ϕ) (l2n ϕ) ;
        l2n_eqevar_fresh : forall phi1 phi2 x, x ∉ free_evars phi2 -> l2n_eqevar x phi1 ∉ named_free_evars (l2n phi2) ;
        l2n_ebody_app : forall phi1 phi2, ebody (patt_app phi1 phi2) = npatt_app (ebody phi1) (ebody phi2) ;
        l2n_ebody : forall phi, ebody phi = l2n phi ;
        l2n_ename_app_1 : forall phi1 phi2, ename (patt_app phi1 phi2) = ename phi1 ;
        l2n_ename_app_2 : forall phi1 phi2, ename (patt_app phi1 phi2) = ename phi2 ;
        l2n_ename_fresh : forall phi psi, ename phi ∉ named_free_evars (l2n psi) ;
        l2n_svar_subst : forall phi psi X, l2n (free_svar_subst psi X phi) = named_svar_subst (l2n phi) (l2n psi) X ;
        sname : Pattern -> svar ;
        sbody : Pattern -> NamedPattern ;
        l2n_mu : forall ϕ', l2n (patt_mu ϕ') = npatt_mu (sname ϕ') (sbody ϕ') ;
        l2n_bsvar_subst : forall phi1 phi2, l2n (bsvar_subst phi2 0 phi1) = named_svar_subst (sbody phi1) (l2n phi2) (sname phi1) ;
        ebody_bound : forall n, ebody (patt_bound_evar n) = npatt_evar (ename (patt_bound_evar n)) ;
        l2nctx : Application_context -> Named_Application_context ;
        l2n_subst_ctx : forall C phi, l2n (subst_ctx C phi) = named_subst_ctx (l2nctx C) (l2n phi) ;
        l2nfe : evar -> evar ;
        l2n_free_evar : forall x, l2n (patt_free_evar x) = npatt_evar (l2nfe x) ;
  }.

  Context
    {Σ : Signature}
    {State : Type}
    (l2n : Pattern -> (NamedPattern)%type)
    {_ln2named_prop : Ln2NamedProperties l2n}
  .

  Definition pf_ln2named
    (Γ : Theory)
    (ϕ : Pattern)
    (wfϕ : well_formed ϕ)
    (pf : ML_proof_system Γ ϕ)
    : NP_ML_proof_system ((fun p => (l2n p)) <$> Γ) (l2n ϕ).
  Proof.
    induction pf.
    {
      apply N_hypothesis.
      { apply l2n_nwf. }
      {
        rewrite elem_of_fmap.
        exists axiom.
        split;[reflexivity|assumption].
      }
    }
    {
      rewrite !l2n_imp.
      apply N_P1; apply l2n_nwf.
    }
    {
      rewrite !l2n_imp.
      apply N_P2; apply l2n_nwf.
    }
    {
      rewrite !l2n_imp. rewrite l2n_bott.
      apply N_P3; apply l2n_nwf.
    }
    {
      rewrite !l2n_imp in IHpf2.
      eapply N_Modus_ponens.
      4: {
        apply IHpf2.
        wf_auto2.
      }
      3: {
        apply IHpf1.
        wf_auto2.
      }
      { apply l2n_nwf. }
      { replace (npatt_imp (l2n phi1) (l2n phi2))
        with (l2n (patt_imp phi1 phi2)).
        2: { rewrite l2n_imp. simpl. reflexivity. }
        apply l2n_nwf.
      }
    }
    {
      unfold instantiate.
      fold (evar_open y 0 phi).
      rewrite l2n_imp.
      rewrite l2n_evar_open.
      rewrite l2n_ex.
      apply N_Ex_quan.
    }
    {
      specialize (IHpf ltac:(wf_auto2)).
      rewrite l2n_imp.
      rewrite l2n_imp in IHpf.
      rewrite l2n_exists_quantify.
      apply N_Ex_gen.
      { apply l2n_nwf. }
      { apply l2n_nwf. }
      { apply IHpf. }
      { 
        apply l2n_eqevar_fresh.
        assumption.
      }
    }
    {
        (* Prop_bott_left *)
        rewrite l2n_imp.
        rewrite l2n_app.
        rewrite l2n_bott.
        apply N_Prop_bott_left.
        { apply l2n_nwf. }
    }
    {
        (* Prop_bott_right *)
        rewrite l2n_imp.
        rewrite l2n_app.
        rewrite l2n_bott.
        apply N_Prop_bott_right.
        { apply l2n_nwf. }
    }
    {
        (* Prop_disj_left *)
        rewrite l2n_imp.
        rewrite l2n_app.
        unfold patt_or, patt_not.
        rewrite 4!l2n_imp.
        rewrite l2n_bott.
        rewrite 2!l2n_app.
        apply N_Prop_disj_left; apply l2n_nwf.
    }
    {
        (* Prop_disj_right *)
        rewrite l2n_imp.
        rewrite l2n_app.
        unfold patt_or, patt_not.
        rewrite 4!l2n_imp.
        rewrite l2n_bott.
        rewrite 2!l2n_app.
        apply N_Prop_disj_right; apply l2n_nwf.
    }
    {
        (* Prop_ex_left *)
        rewrite l2n_imp.
        rewrite l2n_app.
        rewrite 2!l2n_ex.
        rewrite l2n_ebody_app.
        rewrite 2!l2n_ebody.
        rewrite l2n_ename_app_1.
        apply N_Prop_ex_left.
        { cbn. apply l2n_nwf. }
        { apply l2n_nwf. }
        { apply l2n_ename_fresh. }
    }
    {
        (* Prop_ex_right *)
        rewrite l2n_imp.
        rewrite l2n_app.
        rewrite 2!l2n_ex.
        rewrite l2n_ebody_app.
        rewrite 2!l2n_ebody.
        rewrite l2n_ename_app_2.
        apply N_Prop_ex_right.
        { cbn. apply l2n_nwf. }
        { apply l2n_nwf. }
        { apply l2n_ename_fresh. }
    }
    {
        (* Framing_left *)
        specialize (IHpf ltac:(wf_auto2)).
        rewrite l2n_imp.
        rewrite 2!l2n_app.
        apply N_Framing_left.
        rewrite l2n_imp in IHpf.
        apply IHpf.
    }
    {
        (* Framing_right *)
        specialize (IHpf ltac:(wf_auto2)).
        rewrite l2n_imp.
        rewrite 2!l2n_app.
        apply N_Framing_right.
        rewrite l2n_imp in IHpf.
        apply IHpf.
    }
    {
        (* Svar_subst *)
        specialize (IHpf ltac:(wf_auto2)).
        rewrite l2n_svar_subst.
        apply N_Svar_subst.
        { apply l2n_nwf. }
        { apply l2n_nwf. }
        apply IHpf.
    }
    {
        (* Pre_fixp *)
        rewrite l2n_imp.
        unfold instantiate.
        rewrite l2n_mu.
        rewrite l2n_bsvar_subst.
        rewrite l2n_mu.
        apply N_Pre_fixp.
    }
    {
        (* Knaster_tarski *)
        specialize (IHpf ltac:(wf_auto2)).
        rewrite l2n_imp in IHpf.
        unfold instantiate in IHpf.
        rewrite l2n_bsvar_subst in IHpf.
        rewrite l2n_imp.
        rewrite l2n_mu.
        apply N_Knaster_tarski.
        apply IHpf.
    }
    {
        (* Existence *)
        rewrite l2n_ex.
        rewrite ebody_bound.
        apply N_Existence.
    }
    {
        unfold patt_and,patt_or,patt_not.
        rewrite !l2n_imp.
        rewrite !l2n_subst_ctx.
        rewrite !l2n_imp.
        rewrite l2n_bott.
        pose proof (Htmp := N_Singleton_ctx (l2n <$> Γ) (l2nctx C1) (l2nctx C2)).
        unfold npatt_and,npatt_or,npatt_not in Htmp.
        rewrite l2n_free_evar.
        apply Htmp.
    }
  Defined.
End ProofConversionAbstractStateless.