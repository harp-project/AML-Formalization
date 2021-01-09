From Coq Require Import ssreflect ssrfun ssrbool.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From MatchingLogic Require Import Syntax Semantics Helpers.monotonic Utils.Lattice.

Section with_signature.
  Context {Σ : Signature}.
  Existing Instance variables.


  Lemma pattern_interpretation_mu_lfp M ρₑ ρₛ ϕ :
    well_formed_positive (patt_mu ϕ) ->
    let X := fresh_svar ϕ in
    let F := Fassoc ρₑ ρₛ (svar_open 0 X ϕ) X in
    let Sfix := @pattern_interpretation Σ M ρₑ ρₛ (patt_mu ϕ) in
    F Sfix = Sfix.
  Proof.
    simpl.
    remember (fresh_svar ϕ) as X.
    remember (Fassoc ρₑ ρₛ (svar_open 0 X ϕ) X) as F.
    remember (@pattern_interpretation Σ M ρₑ ρₛ (patt_mu ϕ)) as Sfix.
    pose (OS := EnsembleOrderedSet (Domain M)).
    pose (L := PowersetLattice (Domain M)).
    intros Hwfp.

    assert (Ffix : Lattice.isFixpoint F (Lattice.LeastFixpointOf F)).
    { apply Lattice.LeastFixpoint_fixpoint.
      rewrite HeqF. rewrite /Fassoc.
      apply is_monotonic. apply Hwfp. rewrite HeqX. apply set_svar_fresh_is_fresh.
    }
    
    rewrite pattern_interpretation_mu_simpl in HeqSfix.
    unfold isFixpoint in Ffix.
  Abort.

End with_signature.
