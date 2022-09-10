From Coq Require Import ssreflect ssrfun ssrbool.

From Ltac2 Require Import Ltac2.

From Coq Require Import Ensembles Bool.
From Coq.Logic Require Import FunctionalExtensionality Eqdep_dec.
From Equations Require Import Equations.

Require Import Coq.Program.Tactics.

From MatchingLogic Require Import
    Syntax
    DerivedOperators_Syntax
    ProofSystem
    IndexManipulation
    wftactics
    ProofMode_base
    ProofMode_propositional
.

From stdpp Require Import list tactics fin_sets coGset gmap sets.

From MatchingLogic.Utils Require Import stdpp_ext.

Import extralibrary.

Import
  MatchingLogic.Syntax.Notations
  MatchingLogic.DerivedOperators_Syntax.Notations
  MatchingLogic.ProofSystem.Notations
.

Set Default Proof Mode "Classic".

Section with_signature.
  Context {Σ : Signature}.
  Open Scope ml_scope.

  Structure TaggedPattern := TagPattern { untagPattern :> Pattern; }.

  Definition reshape_nil p := TagPattern p.
  Canonical Structure reshape_cons (p : Pattern) : TaggedPattern := reshape_nil p.

  Structure ImpReshapeS (g : Pattern) (l : list Pattern) :=
  ImpReshape
    { irs_flattened :> TaggedPattern ;
      irs_pf : (untagPattern irs_flattened) = foldr patt_imp g l ;
    }.

  Lemma ImpReshape_nil_pf0:
    ∀ (g : Pattern),
      g = foldr patt_imp g [].
  Proof. intros. reflexivity. Qed.

  Canonical Structure ImpReshape_nil (g : Pattern) : ImpReshapeS g [] :=
    ImpReshape g [] (reshape_nil g) (ImpReshape_nil_pf0 g).


  Program Canonical Structure ImpReshape_cons
     (g x : Pattern) (xs : list Pattern) (r : ImpReshapeS g xs)
  : ImpReshapeS g (x::xs) :=
    ImpReshape g (x::xs) (reshape_cons (x ---> untagPattern (reshape_cons r))) _.
  Next Obligation.
    intros g x xs r. simpl.
    rewrite irs_pf.
    reflexivity.
  Qed.


  Lemma reshape (Γ : Theory) (g : Pattern) (xs: list Pattern) (i : ProofInfo) :
    forall (r : ImpReshapeS g xs),
       Γ ⊢i foldr (patt_imp) g xs using i ->
       Γ ⊢i (untagPattern (irs_flattened _ _ r)) using i.
  Proof.
    intros r [pf Hpf].
    unshelve (eexists).
    {
      eapply cast_proof.
      { rewrite irs_pf; reflexivity. }
      exact pf.
    }
    {
      simpl.
      destruct Hpf as [Hpf2 Hpf3 Hpf4].
      constructor.
      {
        rewrite elem_of_subseteq in Hpf2.
        rewrite elem_of_subseteq.
        intros x Hx.
        specialize (Hpf2 x).
        apply Hpf2. clear Hpf2.
        rewrite elem_of_gset_to_coGset in Hx.
        rewrite uses_of_ex_gen_correct in Hx.
        rewrite elem_of_gset_to_coGset.
        rewrite uses_of_ex_gen_correct.
        rewrite indifferent_to_cast_uses_ex_gen in Hx.
        exact Hx.
      }
      {
        rewrite elem_of_subseteq in Hpf3.
        rewrite elem_of_subseteq.
        intros x Hx.
        specialize (Hpf3 x).
        apply Hpf3. clear Hpf3.
        rewrite elem_of_gset_to_coGset in Hx.
        rewrite uses_of_svar_subst_correct in Hx.
        rewrite elem_of_gset_to_coGset.
        rewrite uses_of_svar_subst_correct.
        rewrite indifferent_to_cast_uses_svar_subst in Hx.
        exact Hx.
      }
      {
        rewrite indifferent_to_cast_uses_kt.
        apply Hpf4.
      }
      {
        rewrite framing_patterns_cast_proof.
        destruct i;assumption.
      }
    }
  Defined.


  Local Example ex_reshape Γ a b c d:
    well_formed a ->
    well_formed b ->
    well_formed c ->
    well_formed d ->
    Γ ⊢i a ---> (b ---> (c ---> d)) using BasicReasoning.
  Proof.
    intros wfa wfb wfc wfd.
    apply reshape.
    (* Now the goal has the right shape *)
  Abort.


  (*
    Γ ⊢ (φ₁ and ... and φₖ) ---> ψ
    -------------------------------
    Γ ⊢ φ₁ ---> ... ---> φₖ ---> ψ
  *)
  Lemma lhs_and_to_imp_r Γ (g x : Pattern) (xs : list Pattern) i :
    well_formed g ->
    well_formed x ->
    Pattern.wf xs ->
    forall (r : ImpReshapeS g (x::xs)),
       Γ ⊢i ((foldr (patt_and) x xs) ---> g) using i ->
       Γ ⊢i untagPattern (irs_flattened _ _ r) using i .
  Proof.
    intros wfg wfx wfxs r H.
    eapply cast_proof'.
    { rewrite irs_pf; reflexivity. }
    clear r.
    apply lhs_and_to_imp_meta; assumption.
  Defined.


  Local Example ex_match Γ a b c d:
    well_formed a ->
    well_formed b ->
    well_formed c ->
    well_formed d ->
    Γ ⊢i a ---> (b ---> (c ---> d)) using BasicReasoning.
  Proof.
    intros wfa wfb wfc wfd.
    apply lhs_and_to_imp_r.
  Abort.


  Structure AndReshapeS (g : Pattern) (l : list Pattern) :=
  AndReshape
    { ars_flattened :> TaggedPattern ;
      ars_pf : (untagPattern ars_flattened) = foldr patt_and g l ;
    }.

  Lemma AndReshape_nil_pf0:
    ∀ (g : Pattern),
      g = foldr patt_and g [].
  Proof. intros. reflexivity. Qed.

  Canonical Structure AndReshape_nil (g : Pattern) : AndReshapeS g [] :=
    AndReshape g [] (reshape_nil g) (AndReshape_nil_pf0 g).


  Program Canonical Structure AndReshape_cons
     (g x : Pattern) (xs : list Pattern) (r : AndReshapeS g xs)
  : AndReshapeS g (x::xs) :=
    AndReshape g (x::xs) (reshape_cons (x and untagPattern (reshape_cons r))) _.
  Next Obligation.
    intros g x xs r. simpl.
    rewrite ars_pf.
    reflexivity.
  Qed.


  Lemma reshape_and (Γ : Theory) (g : Pattern) (xs: list Pattern) (i : ProofInfo) :
    forall (r : AndReshapeS g xs),
       Γ ⊢i foldr (patt_and) g xs using i ->
       Γ ⊢i (untagPattern (ars_flattened _ _ r)) using i.
  Proof.
    intros r [pf Hpf].
    unshelve (eexists).
    {
      eapply cast_proof.
      { rewrite ars_pf; reflexivity. }
      exact pf.
    }
    {
      simpl.
      destruct Hpf as [Hpf2 Hpf3 Hpf4].
      constructor.
      {
        rewrite elem_of_subseteq in Hpf2.
        rewrite elem_of_subseteq.
        intros x Hx.
        specialize (Hpf2 x).
        apply Hpf2. clear Hpf2.
        rewrite elem_of_gset_to_coGset in Hx.
        rewrite uses_of_ex_gen_correct in Hx.
        rewrite elem_of_gset_to_coGset.
        rewrite uses_of_ex_gen_correct.
        rewrite indifferent_to_cast_uses_ex_gen in Hx.
        exact Hx.
      }
      {
        rewrite elem_of_subseteq in Hpf3.
        rewrite elem_of_subseteq.
        intros x Hx.
        specialize (Hpf3 x).
        apply Hpf3. clear Hpf3.
        rewrite elem_of_gset_to_coGset in Hx.
        rewrite uses_of_svar_subst_correct in Hx.
        rewrite elem_of_gset_to_coGset.
        rewrite uses_of_svar_subst_correct.
        rewrite indifferent_to_cast_uses_svar_subst in Hx.
        exact Hx.
      }
      {
        rewrite indifferent_to_cast_uses_kt.
        apply Hpf4.
      }
      {
        rewrite framing_patterns_cast_proof.
        destruct i;assumption.
      }
    }
  Defined.

  Local Example ex_reshape_and Γ a b c d:
  well_formed a ->
  well_formed b ->
  well_formed c ->
  well_formed d ->
  Γ ⊢i a and b and c and d using BasicReasoning.
  Proof.
    intros wfa wfb wfc wfd.
    apply reshape_and.
  (* Now the goal has the right shape *)
  Abort.

    (*
      Γ ⊢ φ₁ ---> ... ---> φₖ ---> ψ
      ------------------------------
      Γ ⊢ (φ₁ and ... and φₖ) ---> ψ
    *)
  Lemma lhs_imp_to_and_r Γ (g x : Pattern) (xs : list Pattern) i :
    well_formed g ->
    well_formed x ->
    Pattern.wf xs ->
    forall (r : AndReshapeS x xs),
       Γ ⊢i ((foldr (patt_imp) g (x::xs))) using i ->
       Γ ⊢i (untagPattern (ars_flattened _ _ r)) ---> g using i .
  Proof.
    intros wfg wfx wfxs r H.
    eapply cast_proof'.
    { rewrite ars_pf; reflexivity. }
    clear r.
    apply lhs_imp_to_and_meta; assumption.
  Defined.

  Local Example ex_match_and Γ a b c d:
   well_formed a ->
   well_formed b ->
   well_formed c ->
   well_formed d ->
   Γ ⊢i (a and b and c) ---> d using BasicReasoning.
  Proof.
   intros wfa wfb wfc wfd.
   apply lhs_imp_to_and_r; simpl.
  Abort.

End with_signature.
