From Coq Require Import ssreflect ssrfun ssrbool.

From Coq Require Import Strings.String.
From Coq Require Import Logic.PropExtensionality Logic.Eqdep_dec.
From Equations Require Import Equations.

From stdpp Require Export base gmap fin_sets sets list countable.
From MatchingLogic Require Import Syntax Semantics StringSignature ProofSystem ProofMode Utils.stdpp_ext.
From MatchingLogicProver Require Import Named NamedProofSystem NMatchers.

From stdpp Require Import base finite gmap mapset listset_nodup numbers propset list pretty strings.

From MatchingLogicProver Require Import StringManip.
Import ProofSystem.Notations.

(* TODO: move this near to the definition of Pattern *)
Derive NoConfusion for Pattern.
Derive Subterm for Pattern.

Section ProofConversionAbstractStateless.

  Class Ln2NamedProperties
    {Σ : Signature}
    {State : Type}
    (l2n : State -> Pattern -> (State * NamedPattern)%type)
    := mkLn2NamedProperties {
        l2n_initial : State ;
        l2n_imp: forall s ϕ₁ ϕ₂, l2n s (patt_imp ϕ₁ ϕ₂) = (s, npatt_imp (l2n s ϕ₁).2 (l2n s ϕ₂).2) ;
        l2n_bott : forall s, l2n s patt_bott = (s, npatt_bott) ;
        l2n_nwf : forall s ϕ, named_well_formed (l2n s ϕ).2 = true;
        (*

    ebody : Pattern -> NamedPattern ;
    fe : Pattern -> evar -> evar ;
    ename : Pattern -> evar ;
    l2n_evar_open : forall ϕ y, l2n (evar_open y 0 ϕ) = rename_free_evar (ebody ϕ) (fe ϕ y) (ename ϕ) ;

    l2n_ex : forall ϕ', l2n (patt_exists ϕ') = npatt_exists (ename ϕ') (ebody ϕ') ;

    l2n_exists_quantify : forall x ϕ, l2n (exists_quantify x ϕ) = l2n 
    *)
  }.

  Context
    {Σ : Signature}
    {State : Type}
    (l2n : State -> Pattern -> (State * NamedPattern)%type)
    {_ln2named_prop : Ln2NamedProperties l2n}
  .

  Definition pf_ln2named
    (Γ : Theory)
    (ϕ : Pattern)
    (wfϕ : well_formed ϕ)
    (pf : ML_proof_system Γ ϕ)
    : NP_ML_proof_system ((fun p => (l2n l2n_initial p).2) <$> Γ) (l2n l2n_initial ϕ).2.
  Proof.
    induction pf.
    {
      apply N_hypothesis.
      { unfold is_true. apply l2n_nwf. admit. (* WF *)}
      {
        rewrite elem_of_fmap.
        exists axiom.
        split;[reflexivity|assumption].
      }
    }
    {
      rewrite !l2n_imp.
      apply N_P1.
      { admit. (* WF *)}
      { admit. (* WF *)}
    }
    {
      rewrite !l2n_imp.
      apply N_P2.
      { admit. (* WF *)}
      { admit. (* WF *)}
      { admit. (* WF *)}
    }
    {
      rewrite !l2n_imp. rewrite l2n_bott.
      apply N_P3.
      { admit. (* WF *)}
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
      { admit. (* WF *)}
      { admit. (* WF *)}
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
    }
  Defined.


End ProofConversionAbstract.
