From Coq Require Import ssreflect ssrfun ssrbool.

(* From Ltac2 Require Import Ltac2. *)

Require Import Equations.Prop.Equations.

From Coq Require Import String Setoid.
Require Import Coq.Program.Equality.
Require Import Coq.Logic.Classical_Prop.
From Coq.Logic Require Import FunctionalExtensionality Eqdep_dec.
From Coq.Classes Require Import Morphisms_Prop.
From Coq.Unicode Require Import Utf8.
From Coq.micromega Require Import Lia.

From MatchingLogic Require Import Logic ProofMode.MLPM Substitution.
From MatchingLogic.Theories Require Import Definedness_Syntax Definedness_ProofSystem FOEquality_ProofSystem DeductionTheorem.
From MatchingLogic.Utils Require Import stdpp_ext.

Require Import MatchingLogic.wftactics.

From stdpp Require Import base fin_sets sets propset proof_irrel option list.

Import extralibrary.

Import MatchingLogic.Logic.Notations.
Import MatchingLogic.Theories.Definedness_Syntax.Notations.

Set Default Proof Mode "Classic".

Close Scope equations_scope. (* Because of [!] *)

Open Scope ml_scope.
Open Scope string_scope.
Open Scope list_scope.

Section EqCon.
  Context {Σ : Signature} {syntax : Syntax}.

  (* Mu-freeness is a stricter property. *)
  Lemma mf_imp_ktwf φ : mu_free φ -> pattern_kt_well_formed φ.
  Proof.
    intros.
    induction φ; auto.
    all: inversion H; apply andb_true_iff in H1 as [?%IHφ1 ?%IHφ2]; now apply andb_true_iff.
  Defined.

  (* Allows splitting `wf` without unfolding in-place. *)
  Lemma wf_cons x l : wf (x :: l) <-> well_formed x /\ wf l.
  Proof.
    unfold wf. simpl. apply andb_true_iff.
  Defined.

  (* Same proof as `bevar_subst_evar_quantify_free_evar`, *)
  (* but more general statement. *)
  Lemma bevar_subst_evar_quantify x p dbi ϕ:
    well_formed_closed_ex_aux ϕ dbi ->
    (ϕ^{{evar: x ↦ dbi}})^[evar: dbi ↦ p] = ϕ^[[evar: x ↦ p]].
  Proof.
    revert dbi.
    induction ϕ; intros dbi Hwf; simpl in *; auto.
    - case_match; simpl; [|reflexivity].
      case_match; simpl; try lia. reflexivity.
    - do 2 case_match; try lia; auto. congruence. congruence.
    - apply andb_true_iff in Hwf.
      destruct_and!.
      rewrite IHϕ1;[assumption|].
      rewrite IHϕ2;[assumption|].
      reflexivity.
    - apply andb_true_iff in Hwf.
      destruct_and!.
      rewrite IHϕ1;[assumption|].
      rewrite IHϕ2;[assumption|].
      reflexivity.
    - rewrite IHϕ;[assumption|reflexivity].
    - rewrite IHϕ;[assumption|reflexivity].
  Qed.

  (* Very similar to `mf_fold_left`, but this wasn't needed before. *)
  Corollary mf_foldr {A : Type} (f : A -> Pattern -> Pattern) (t : A -> Pattern) x xs :
    mu_free x ->
    foldr (fun c a => mu_free c && a) true (map t xs) ->
    (forall a b, mu_free a -> mu_free (t b) -> mu_free (f b a)) ->
    mu_free (foldr f x xs).
  Proof.
    intros.
    apply foldr_ind with (Q := mu_free ∘ t);
    only 2: apply Forall_fold_right;
    only 2: rewrite -> foldr_map, foldr_andb_equiv_foldr_conj in H0;
    auto.
  Qed.

  (* The remainder works for any theory containing definedness. *)
  Context (Γ : Theory).
  Hypothesis (HΓ : theory ⊆ Γ).

  (* Equality elimination for substitution using a functional *)
  (* pattern. *)
  Lemma equality_elimination_functional_subst p q p1 p2 x :
    well_formed p ->
    well_formed q ->
    well_formed p1 ->
    well_formed p2 ->
    mu_free p ->
    mu_free q ->
    pattern_kt_well_formed p1 ->
    pattern_kt_well_formed p2 ->
    Γ ⊢ p =ml q ->
    Γ ⊢ p1 =ml p2 ->
    Γ ⊢ is_functional p1 ->
    Γ ⊢ p^[[evar: x ↦ p1]] =ml q^[[evar: x ↦ p2]].
  Proof.
    intros Hwfp Hwfq Hwfp1 Hwfp2 Hmfp Hmfq Hktwfp1 Hktwfp2 Hpeqq Hp1eqp2 Hfuncp1.
    pose proof mf_imp_ktwf _ Hmfp as Hktwfp.
    pose proof mf_imp_ktwf _ Hmfq as Hktwfq.
    apply universal_generalization with (x := x) in Hpeqq;
    [| try_solve_pile | wf_auto2].
    eapply forall_functional_subst_meta with (φ' := p1) in Hpeqq;
    auto; [|rewrite <- mu_free_evar_quantify | ..];
    [| wf_auto2 ..].
    rewrite bevar_subst_evar_quantify in Hpeqq; [wf_auto2 |].
    mlSimpl in Hpeqq.
    mlFreshEvar as y.
    unshelve epose proof MP Hp1eqp2 (equality_elimination Γ p1 p2 {|pcPattern := p^[[evar: x ↦ p1]] =ml q^[[evar: x ↦ patt_free_evar y]]; pcEvar := y|} HΓ _ _ _ _); try solve [wf_auto2].
    simpl. rewrite ! pattern_kt_well_formed_free_evar_subst; auto.
    unfold emplace in H. mlSimpl in H. cbn in H.
    rewrite -> 2 free_evar_subst_chain in H; [| fm_solve ..].
    rewrite -> 2 (free_evar_subst_no_occurrence y) in H; [| fm_solve ..].
    exact (MP Hpeqq H).
  Defined.
 
  (* The patterns that will be equal, *)
  (* and the evars that they will replace. *)
  Context (σ : list (evar * Pattern * Pattern)).
  (* They are well-formed... *)
  Hypothesis (Hσ1 : wf (map (snd ∘ fst) σ)) (Hσ2 : wf (map snd σ)).
  (* ... mu-free ... *)
  Hypothesis (Hmfσ1 : foldr (fun c a => mu_free c && a) true (map (snd ∘ fst) σ)).
  Hypothesis (Hmfσ2 : foldr (fun c a => mu_free c && a) true (map snd σ)).
  (* ... and one of them is functional. *)
  Hypothesis (Hfpσ : foldr (fun c a => ((Γ ⊢ is_functional c.1.2) * a)%type) unit σ).

  (* Separate equalities as a hypothesis. *)
  Definition hypos : Type := foldr (fun x t => ((Γ ⊢ x.1.2 =ml x.2) * t)%type) unit σ.

  (* Same as `emplace`ing into a context with multiple holes. *)
  Definition goal (φ : Pattern) : Pattern := (foldr (fun x p => p^[[evar: x.1.1 ↦ x.1.2]]) φ σ) =ml (foldr (fun x p => p^[[evar: x.1.1 ↦ x.2]]) φ σ).

  (* For any pattern (which would serve as the core of the context), *)
  (* given the eqalities as hypothesis, substituting into the *)
  (* multihole context yields equality. *)
  Goal forall φ,
    well_formed φ ->
    mu_free φ ->
    hypos ->
    Γ ⊢ goal φ.
  Proof.
    intros ? Hwfφ Hmfφ.
    unfold hypos, goal.
    induction σ; simpl; intros.
    now aapply patt_equal_refl.
    simpl in Hσ1, Hσ2. apply wf_cons in Hσ1 as [], Hσ2 as [].
    simpl in Hmfσ1, Hmfσ2. apply andb_true_iff in Hmfσ1 as [], Hmfσ2 as [].
    simpl in Hfpσ.
    destruct X as [? ?%(IHl H0 H2)]. clear IHl.
    apply equality_elimination_functional_subst; auto.
    - eapply wf_foldr. auto. exact H0.
      intros ? [[] ?] **. wf_auto2.
    - eapply wf_foldr. auto. exact H2.
      intros ? [[] ?] **. wf_auto2.
    - eapply mf_foldr. auto. exact H4.
      intros ? [[] ?] **. simpl in H8 |- *. now apply mu_free_free_evar_subst.
    - eapply mf_foldr. auto. exact H6.
      intros ? [[] ?] **. simpl in H8 |- *. now apply mu_free_free_evar_subst.
    - now apply mf_imp_ktwf.
    - now apply mf_imp_ktwf.
    - exact (Hfpσ.1).
    - auto.
    - auto.
    - exact (Hfpσ.2).
  Defined.
End EqCon.
