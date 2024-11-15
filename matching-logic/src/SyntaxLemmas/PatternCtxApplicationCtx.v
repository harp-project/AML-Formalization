From Coq Require Import ProofIrrelevance.
From MatchingLogic Require Export SyntaxLemmas.ApplicationCtxSubstitution
                                  PatternContext
                                  Freshness.

Section with_signature.
    Context {Σ : Signature}.



    Program Definition ApplicationContext2PatternCtx'
    (boxvar : evar)
    (AC : Application_context)
    (pf : boxvar ∉ free_evars_ctx AC)
: PatternCtx :=
{|
pcEvar := boxvar;
pcPattern := ApplicationContext2Pattern boxvar AC;
|}.

Lemma AC2PC'_wf boxvar AC pf: PC_wf (@ApplicationContext2PatternCtx' boxvar AC pf).
Proof.
  unfold PC_wf. apply wf_sctx. reflexivity.
Qed.

Definition ApplicationContext2PatternCtx (AC : Application_context) : PatternCtx :=
  let boxvar := (evar_fresh (elements (free_evars_ctx AC))) in
    ApplicationContext2PatternCtx' boxvar AC (@set_evar_fresh_is_fresh' Σ _).

Lemma AC2PC_wf AC: PC_wf (ApplicationContext2PatternCtx AC).
Proof.
  apply AC2PC'_wf.
Defined.

Definition is_application (p : Pattern) : bool :=
match p with
| patt_app _ _ => true
| _ => false
end.

Definition is_free_evar (p : Pattern) : bool :=
match p with
| patt_free_evar _ => true
| _ => false
end.

Definition is_application_or_free_evar (p : Pattern) : bool :=
is_application p || is_free_evar p.

Lemma ApplicationContext2PatternCtx_is_application (AC : Application_context) :
let p := pcPattern (ApplicationContext2PatternCtx AC) in
is_application_or_free_evar p = true.
Proof.
destruct AC; reflexivity.
Qed.

Definition is_application_or_free_evar_x (x : evar) (p : Pattern)  : bool :=
is_application p ||
          (match p with
           | patt_free_evar x' => if decide (x' = x) is left _ then true else false
           | _ => false
           end).

Fixpoint PatternCtx2ApplicationContext'
  (box_evar : evar)
  (p : Pattern)
  (wf : well_formed p)
: Application_context :=
(match p as q return well_formed q -> Application_context with
| patt_app p1 p2 =>
fun wf =>
if decide (box_evar ∉ free_evars p1) is left _ then
@ctx_app_r Σ p1 (@PatternCtx2ApplicationContext' box_evar p2 (well_formed_app_2 _ _ wf)) (well_formed_app_1 _ _ wf)
else if decide  (box_evar ∉ free_evars p2) is left _ then
    @ctx_app_l Σ (@PatternCtx2ApplicationContext' box_evar p1 (well_formed_app_1 _ _ wf)) p2 (well_formed_app_2 _ _ wf)
  else
    box
| _ => fun _ => box
end
) wf
.


Definition PatternCtx2ApplicationContext (C : PatternCtx) (pf: PC_wf C) : 
  Application_context :=
  @PatternCtx2ApplicationContext' (pcEvar C) (pcPattern C) pf.

Lemma count_evar_occurrences_subst_ctx AC x:
  x ∉ free_evars_ctx AC ->
  count_evar_occurrences x (subst_ctx AC (patt_free_evar x)) = 1.
Proof.
  intros H.
  induction AC; simpl.
  - rewrite decide_eq_same. reflexivity.
  - simpl in H. apply not_elem_of_union in H.
  rewrite IHAC;[exact (proj1 H)|].
  rewrite (proj1 (count_evar_occurrences_0 x p)); [exact (proj2 H)|].
  reflexivity.
  - simpl in H. apply not_elem_of_union in H.
  rewrite IHAC;[exact (proj2 H)|].
  rewrite (proj1 (count_evar_occurrences_0 x p)); [exact (proj1 H)|].
  reflexivity.
Qed.

Lemma ApplicationContext2PatternCtx2ApplicationContext'
  (boxvar : evar)
  (AC : Application_context)
  (Hnotin: boxvar ∉ free_evars_ctx AC) :
  let C : PatternCtx := ApplicationContext2PatternCtx' boxvar AC Hnotin in
  let pf := AC2PC'_wf _ _ Hnotin in
  PatternCtx2ApplicationContext' boxvar _ pf = AC.
Proof.
  simpl.
  move: (AC2PC'_wf _ _ Hnotin).
  move: boxvar Hnotin.

  induction AC; intros boxvar Hnotin pf.
  - reflexivity.
  - simpl.
  simpl in Hnotin.
  pose proof (Hnotin' := Hnotin).
  apply not_elem_of_union in Hnotin'.
  destruct Hnotin' as [HnotinAC Hnotinp].
  assert (Hcount1: count_evar_occurrences boxvar (subst_ctx AC (patt_free_evar boxvar)) = 1).
  { rewrite count_evar_occurrences_subst_ctx; [exact HnotinAC|lia]. }
  assert (Hcount1': count_evar_occurrences boxvar (subst_ctx AC (patt_free_evar boxvar)) > 0) by lia.
  apply count_evar_occurrences_not_0 in Hcount1'.
  destruct decide. set_solver.
  clear n Hcount1'.

  assert (HoneOcc : count_evar_occurrences boxvar (ApplicationContext2Pattern boxvar (ctx_app_l AC p Prf)) = 1).
  { apply ApplicationContext2Pattern_one_occ. simpl. exact Hnotin. }
  simpl in HoneOcc.
  rewrite Hcount1 in HoneOcc.
  assert (Hcount0: count_evar_occurrences boxvar p = 0).
  { lia. }
  destruct decide. 2: contradiction.
  f_equal.
  2: { apply proof_irrelevance. }
  rewrite IHAC;[assumption|reflexivity].
  - simpl.
  simpl in Hnotin.
  pose proof (Hnotin' := Hnotin).
  apply not_elem_of_union in Hnotin'.
  destruct Hnotin' as [Hnotinp HnotinAC].

  assert (HoneOcc : count_evar_occurrences boxvar (ApplicationContext2Pattern boxvar (ctx_app_r p AC Prf)) = 1).
  { apply ApplicationContext2Pattern_one_occ. simpl. exact Hnotin. }

  assert (Hcount1: count_evar_occurrences boxvar (subst_ctx AC (patt_free_evar boxvar)) = 1).
  { rewrite count_evar_occurrences_subst_ctx; [exact HnotinAC|reflexivity]. }

  simpl in HoneOcc.
  rewrite Hcount1 in HoneOcc.
  assert (Hcount0: count_evar_occurrences boxvar p = 0).
  { lia. }

  destruct decide. 2: contradiction. 

  f_equal.
  2: { apply proof_irrelevance. }
  rewrite IHAC;[assumption|reflexivity].
Qed.

Lemma ApplicationContext2PatternCtx2ApplicationContext (AC : Application_context) :
  PatternCtx2ApplicationContext _ (AC2PC_wf AC) = AC.
Proof.
  unfold PatternCtx2ApplicationContext, ApplicationContext2PatternCtx.
  unfold AC2PC_wf.
  apply ApplicationContext2PatternCtx2ApplicationContext'.
Qed.

(* TODO: This needs to use count_evar_occurrences, because the prover depends on it *)
Fixpoint is_implicative_context' (box_evar : evar) (phi : Pattern) : bool :=
match phi with
| patt_bott => true
| patt_free_evar _ => true
| patt_imp phi1 phi2 =>
(if decide(count_evar_occurrences box_evar phi1 <> 0) is left _
then is_implicative_context' box_evar phi1 else true) &&
(if decide(count_evar_occurrences box_evar phi2 <> 0) is left _
then is_implicative_context' box_evar phi2 else true)
| _ => false
end.

Definition is_implicative_context (C : PatternCtx) :=
  is_implicative_context' (pcEvar C) (pcPattern C).

Lemma emplace_subst_ctx AC ϕ:
  emplace (ApplicationContext2PatternCtx AC) ϕ = subst_ctx AC ϕ.
Proof.
  induction AC.
  - unfold ApplicationContext2PatternCtx,ApplicationContext2PatternCtx'.
    unfold emplace. simpl. unfold free_evar_subst. simpl.
    rewrite decide_eq_same. reflexivity.
  - simpl.
    rewrite -IHAC.
    unfold ApplicationContext2PatternCtx,ApplicationContext2PatternCtx'.
    simpl.
    unfold emplace. unfold free_evar_subst. simpl.
    unfold ApplicationContext2Pattern.
    f_equal.
    2: { fold free_evar_subst.
      rewrite free_evar_subst_no_occurrence.
      2: { reflexivity. }
      eapply evar_is_fresh_in_richer'.
      2: { apply set_evar_fresh_is_fresh'. }
      clear. set_solver.
    }
    remember (evar_fresh (elements (free_evars_ctx AC ∪ free_evars p))) as Xfr1.
    remember (evar_fresh (elements (free_evars_ctx AC))) as Xfr2.
    apply free_evar_subst_subst_ctx_independent.
    { subst.
      eapply not_elem_of_larger_impl_not_elem_of.
      2: { apply set_evar_fresh_is_fresh'. }
      clear. set_solver.
    }
    { subst.
      eapply not_elem_of_larger_impl_not_elem_of.
      2: { apply set_evar_fresh_is_fresh'. }
      clear. set_solver.
    }
  - simpl.
    rewrite -IHAC.
    unfold ApplicationContext2PatternCtx,ApplicationContext2PatternCtx'.
    simpl.
    unfold emplace. unfold free_evar_subst. simpl.
    unfold ApplicationContext2Pattern.
    f_equal.
    { fold free_evar_subst.
      rewrite free_evar_subst_no_occurrence.
      2: { reflexivity. }
      eapply evar_is_fresh_in_richer'.
      2: { apply set_evar_fresh_is_fresh'. }
      clear. set_solver.
    }
    remember (evar_fresh (elements (free_evars_ctx AC ∪ free_evars p))) as Xfr1.
    remember (evar_fresh (elements (free_evars_ctx AC))) as Xfr2.
    apply free_evar_subst_subst_ctx_independent.
    { subst.
      eapply not_elem_of_larger_impl_not_elem_of.
      2: { apply set_evar_fresh_is_fresh'. }
      clear. set_solver.
    }
    { subst.
      eapply not_elem_of_larger_impl_not_elem_of.
      2: { apply set_evar_fresh_is_fresh'. }
      clear. set_solver.
    }
Qed.

End with_signature.