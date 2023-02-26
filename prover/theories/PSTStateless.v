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
    (l2n : Pattern -> NamedPattern)
    := mkLn2NamedProperties {
        l2n_imp: forall ϕ₁ ϕ₂, l2n (patt_imp ϕ₁ ϕ₂) = npatt_imp (l2n ϕ₁) (l2n ϕ₂) ;
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
        
    }
  Defined.
