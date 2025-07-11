(* Order of Exports is important for mutable tacs *)
From MatchingLogic Require Export BasicProofSystemLemmas.
From MatchingLogic.ProofMode Require Export Basics.

Import MatchingLogic.Logic.Notations.

Set Default Proof Mode "Classic".

Lemma MLGoal_exactn {Σ : Signature}
  (Γ : Theory)
  (l₁ l₂ : hypotheses)
  (name : string)
  (g : Pattern)
  (info : ProofInfo) :
  mkMLGoal Σ Γ (l₁ ++ (mkNH _ name g) :: l₂) g info.
Proof.
  mlExtractWF wfl₁gl₂ wfg.
  fromMLGoal.
  useBasicReasoning.
  unfold patterns_of in *.
  rewrite map_app.
  apply nested_const_middle.
  { exact wfg. }
  { abstract (
      pose proof (wfl₁ := wf_take (length (patterns_of l₁)) _ wfl₁gl₂);
      rewrite map_app in wfl₁;
      rewrite take_app in wfl₁;
      unfold patterns_of in wfl₁;
      rewrite firstn_all in wfl₁;
      rewrite Nat.sub_diag take_0 app_nil_r in wfl₁;
      exact wfl₁
    ).
  }
  {
    abstract (
      pose proof (wfgl₂ := wf_drop (length (patterns_of l₁)) _ wfl₁gl₂);
      rewrite map_app in wfgl₂;
      rewrite drop_app in wfgl₂;
      unfold Pattern.wf in wfgl₂;
      simpl in wfgl₂; unfold patterns_of in wfgl₂;
      rewrite drop_all in wfgl₂;
      rewrite Nat.sub_diag drop_0 in wfgl₂;
      apply andb_prop in wfgl₂;
      destruct wfgl₂ as [_ wfl₂];
      exact wfl₂
    ).
  }
Defined.

Ltac2 do_mlExactn (n : constr) :=
  do_ensureProofMode ();
  do_mlReshapeHypsByIdx n;
  Control.plus (fun () => apply MLGoal_exactn)
  (fun _ => _mlReshapeHypsBack;
            throw_pm_exn_with_goal "do_mlExactn: Hypothesis is not identical to the goal!")
.

Ltac2 Notation "mlExactn" n(constr) :=
  do_mlExactn n
.

Tactic Notation "mlExactn" constr(n) :=
  let f := ltac2:(n |- do_mlExactn (Option.get (Ltac1.to_constr n))) in
  f n
.


Lemma MLGoal_exact {Σ : Signature} Γ l name g idx info:
  find_hyp name l = Some (idx, (mkNH _ name g)) ->
  mkMLGoal Σ Γ l g info.
Proof.
  intros Hfound.
  setoid_rewrite -> list.list_find_Some in Hfound.
  destruct Hfound as [Hfound1 [Hfound2 Hfound3] ].
  rewrite -[l](take_drop_middle l idx (mkNH _ name g)).
  { exact Hfound1. }
  apply MLGoal_exactn.
Defined.

Ltac2 do_mlExact (name' : constr) :=
  do_ensureProofMode ();
  Control.plus (fun () =>
    eapply MLGoal_exact with (name := $name');
    simpl; apply f_equal; reflexivity)
    (fun _ => _mlReshapeHypsBack;
              throw_pm_exn_with_goal ("do_mlExact: Given hypothesis is not identical to the goal, or there is no pattern associated with the given name!"))
.

Ltac2 Notation "mlExact" name(constr) :=
  do_mlExact name
.

Tactic Notation "mlExact" constr(name) :=
  let f := ltac2:(name |- do_mlExact (Option.get (Ltac1.to_constr name))) in
  f name
.
  
Local Example ex_mlExact {Σ : Signature} Γ a b c:
  well_formed a = true ->
  well_formed b = true ->
  well_formed c = true ->
  Γ ⊢i a ---> b ---> c ---> b using BasicReasoning.
Proof.
  (* The following are not necessary *)
  (*
    intros wfa wfb wfc.
    toMLGoal.
    { wf_auto2. }
  *)
  mlIntro "H1". mlIntro "H2". mlIntro "H3". (* TODO: mlIntros "H1" "H2" "H3".*)
  Fail mlExact "H4".
  Fail mlExact "H1".
  mlExact "H2".
Defined.



Lemma MLGoal_weakenConclusion' {Σ : Signature} Γ l g g' (i : ProofInfo):
  Γ ⊢i g ---> g' using i ->
  mkMLGoal Σ Γ l g i ->
  mkMLGoal Σ Γ l g' i.
Proof.
  intros Hgg' Hlg.
  (*mlExtractWF wfl wfgp.*)
  unfold of_MLGoal in *. simpl in *.
  intros wfg' wfl.
  pose proof (wfimp := ProofSystem.proved_impl_wf _ _ (proj1_sig Hgg')).
  apply well_formed_imp_proj1 in wfimp.
  eapply prf_weaken_conclusion_iter_meta_meta.
  5: apply Hlg.
  4: apply Hgg'.
  all: assumption.
Defined.

Lemma prf_contraction {Σ : Signature} Γ a b:
  well_formed a ->
  well_formed b ->
  Γ ⊢i ((a ---> a ---> b) ---> (a ---> b)) using BasicReasoning.
Proof.
  intros wfa wfb.
  assert (H1 : Γ ⊢i (a ---> ((a ---> b) ---> b)) using BasicReasoning).
  {
    apply modus_ponens; assumption.
  }
  assert (H2 : Γ ⊢i ((a ---> ((a ---> b) ---> b)) ---> ((a ---> (a ---> b)) ---> (a ---> b))) using BasicReasoning).
  {
    apply P2; wf_auto2.
  }
  eapply MP. 2: apply H2. apply H1.
Defined.

Lemma prf_weaken_conclusion_under_implication {Σ : Signature} Γ a b c:
  well_formed a ->
  well_formed b ->
  well_formed c ->
  Γ ⊢i ((a ---> b) ---> ((a ---> (b ---> c)) ---> (a ---> c))) using BasicReasoning.
Proof.
  intros wfa wfb wfc.
  assert (H1 : Γ ⊢i ((a ---> (b ---> c)) ---> (b ---> (a ---> c))) using BasicReasoning).
  {
    apply reorder; wf_auto2.
  }
  assert (H2 : Γ ⊢i (((b ---> (a ---> c)) ---> (a ---> c)) ---> ((a ---> (b ---> c)) ---> (a ---> c))) using BasicReasoning).
  {
    apply prf_strenghten_premise_meta;[wf_auto2|wf_auto2|wf_auto2|].
    apply H1.
  }
  eapply prf_weaken_conclusion_meta_meta.
  4: apply H2. 1-3: wf_auto2. clear H1 H2.

  assert (H3 : Γ ⊢i ((a ---> b) ---> ((b ---> (a ---> c)) ---> (a ---> (a ---> c)))) using BasicReasoning).
  {
    apply syllogism; wf_auto2.
  }
  assert (H4 : Γ ⊢i ((a ---> (a ---> c)) ---> (a ---> c)) using BasicReasoning).
  {
    apply prf_contraction; wf_auto2.
  }
  assert (Hiter: ((a ---> b) ---> (b ---> a ---> c) ---> a ---> c)
                 = foldr patt_imp (a ---> c) [(a ---> b); (b ---> a ---> c)]) by reflexivity.

  rewrite Hiter.

  eapply prf_weaken_conclusion_iter_meta_meta.
  5: apply H3. 4: apply H4. all: wf_auto2.
Defined.

Lemma prf_weaken_conclusion_under_implication_meta {Σ : Signature} Γ a b c (i : ProofInfo):
  well_formed a ->
  well_formed b ->
  well_formed c ->
  Γ ⊢i (a ---> b) using i ->
  Γ ⊢i ((a ---> (b ---> c)) ---> (a ---> c)) using i.
Proof.
  intros wfa wfb wfc H.
  eapply MP.
  2: { useBasicReasoning. apply prf_weaken_conclusion_under_implication; wf_auto2. }
  exact H.
Defined.

Lemma prf_weaken_conclusion_under_implication_meta_meta {Σ : Signature} Γ a b c i:
  well_formed a ->
  well_formed b ->
  well_formed c ->
  Γ ⊢i a ---> b using i ->
  Γ ⊢i a ---> b ---> c using i ->
  Γ ⊢i a ---> c using i.
Proof.
  intros wfa wfb wfc H1 H2.
  eapply MP.
  { apply H2. }
  { apply prf_weaken_conclusion_under_implication_meta.
    4: { apply H1. }
    all: wf_auto2.
  }
Defined.

Lemma prf_weaken_conclusion_iter_under_implication {Σ : Signature} Γ l g g':
  Pattern.wf l ->
  well_formed g ->
  well_formed g' ->
  Γ ⊢i (((g ---> g') ---> (foldr patt_imp g l)) ---> ((g ---> g') ---> (foldr patt_imp g' l)))
  using BasicReasoning.
Proof.
  intros wfl wfg wfg'.
  pose proof (H1 := prf_weaken_conclusion_iter Γ l g g' wfl wfg wfg').
  remember ((g ---> g')) as a.
  remember (foldr patt_imp g l) as b.
  remember (foldr patt_imp g' l) as c.
  assert (well_formed a) by (subst; wf_auto2).
  assert (well_formed b) by (subst; wf_auto2).
  assert (well_formed c) by (subst; wf_auto2).
  pose proof (H2' := prf_weaken_conclusion_under_implication Γ a b c ltac:(assumption) ltac:(assumption) ltac:(assumption)).
  apply reorder_meta in H2'. 2,3,4: subst;wf_auto2.
  eapply MP. 2: apply H2'. apply H1.
Defined.

Lemma prf_weaken_conclusion_iter_under_implication_meta {Σ : Signature} Γ l g g' (i : ProofInfo):
  Pattern.wf l ->
  well_formed g ->
  well_formed g' ->
  Γ ⊢i ((g ---> g') ---> (foldr patt_imp g l)) using i->
  Γ ⊢i ((g ---> g') ---> (foldr patt_imp g' l)) using i.
Proof.
  intros wfl wfg wfg' H.
  eapply MP.
  2: { useBasicReasoning. apply prf_weaken_conclusion_iter_under_implication; wf_auto2. }
  { exact H. }
Defined.

Lemma MLGoal_weakenConclusion_under_first_implication {Σ : Signature} Γ l name g g' i:
  mkMLGoal Σ Γ (mkNH _ name (g ---> g') :: l) g i ->
  mkMLGoal Σ Γ (mkNH _ name (g ---> g') :: l) g' i .
Proof.
  intros H. unfold of_MLGoal in *. simpl in *.
  intros wfg' wfgg'l.
  pose proof (Htmp := wfgg'l).
  unfold Pattern.wf in Htmp. simpl in Htmp. apply andb_prop in Htmp. destruct Htmp as [wfgg' wfl].
  apply well_formed_imp_proj1 in wfgg'. specialize (H wfgg' wfgg'l).
  apply prf_weaken_conclusion_iter_under_implication_meta; assumption.
Defined.

Lemma prf_weaken_conclusion_iter_under_implication_iter {Σ : Signature} Γ l₁ l₂ g g':
  Pattern.wf l₁ ->
  Pattern.wf l₂ ->
  well_formed g ->
  well_formed g' ->
  Γ ⊢i ((foldr patt_imp g (l₁ ++ (g ---> g') :: l₂)) --->
       (foldr patt_imp g' (l₁ ++ (g ---> g') :: l₂)))
  using BasicReasoning.
Proof.
  intros wfl₁ wfl₂ wfg wfg'.
  induction l₁; simpl.
  - apply prf_weaken_conclusion_iter_under_implication; auto.
  - pose proof (wfal₁ := wfl₁). unfold Pattern.wf in wfl₁. simpl in wfl₁. apply andb_prop in wfl₁.
    destruct wfl₁ as [wfa wfl₁]. specialize (IHl₁ wfl₁).
    eapply prf_weaken_conclusion_meta. 4: assumption. all: wf_auto2.
Defined.

Lemma prf_weaken_conclusion_iter_under_implication_iter_meta {Σ : Signature} Γ l₁ l₂ g g' i:
  Pattern.wf l₁ ->
  Pattern.wf l₂ ->
  well_formed g ->
  well_formed g' ->
  Γ ⊢i (foldr patt_imp g (l₁ ++ (g ---> g') :: l₂)) using i ->
  Γ ⊢i (foldr patt_imp g' (l₁ ++ (g ---> g') :: l₂)) using i.
Proof.
  intros wfl₁ wfl₂ wfg wfg' H.
  eapply MP.
  { apply H. }
  { useBasicReasoning. apply prf_weaken_conclusion_iter_under_implication_iter; wf_auto2. }
Defined.

Lemma MLGoal_weakenConclusion {Σ : Signature} Γ l₁ l₂ name g g' i:
  mkMLGoal Σ Γ (l₁ ++ (mkNH _ name (g ---> g')) :: l₂) g i ->
  mkMLGoal Σ Γ (l₁ ++ (mkNH _ name (g ---> g')) :: l₂) g' i.
Proof.
  unfold of_MLGoal in *. simpl in *.
  intros H wfg' wfl₁gg'l₂.

  unfold patterns_of in wfl₁gg'l₂.
  rewrite map_app in wfl₁gg'l₂.

  unfold patterns_of.
  rewrite map_app.

  apply prf_weaken_conclusion_iter_under_implication_iter_meta.
  { abstract (pose proof (wfl₁ := wf_take (length (patterns_of l₁)) _ wfl₁gg'l₂); simpl in wfl₁; rewrite take_app in wfl₁; 
       rewrite firstn_all in wfl₁;
       rewrite Nat.sub_diag take_0 app_nil_r in wfl₁;
       exact wfl₁). }
  { abstract (
      pose proof (wfgg'l₂ := wf_drop (length (patterns_of l₁)) _ wfl₁gg'l₂);
      rewrite drop_app in wfgg'l₂;
      pose proof (Htmp := wfgg'l₂);
      unfold Pattern.wf in Htmp;
      simpl in Htmp; unfold patterns_of in Htmp;
      rewrite drop_all in Htmp;
      rewrite Nat.sub_diag drop_0 in Htmp;
      apply andb_prop in Htmp;
      destruct Htmp as [wfgg' wfl₂];
      exact wfl₂
    ).
  }
  {
    abstract(
      pose proof (wfgg'l₂ := wf_drop (length (patterns_of l₁)) _ wfl₁gg'l₂);
      rewrite drop_app in wfgg'l₂;
      pose proof (Htmp := wfgg'l₂);
      unfold Pattern.wf in Htmp;
      simpl in Htmp;
      simpl in Htmp; unfold patterns_of in Htmp;
      rewrite drop_all in Htmp;
      rewrite Nat.sub_diag drop_0 in Htmp;
      apply andb_prop in Htmp;
      destruct Htmp as [wfgg' wfl₂];
      pose proof (wfg := well_formed_imp_proj1 _ _ wfgg');
      exact wfg
    ).
  }
  { exact wfg'. }

  unfold patterns_of in H.
  rewrite map_app in H.
  apply H.
  {
    abstract(
      pose proof (wfgg'l₂ := wf_drop (length (patterns_of l₁)) _ wfl₁gg'l₂);
      rewrite drop_app in wfgg'l₂;
      pose proof (Htmp := wfgg'l₂);
      unfold Pattern.wf in Htmp;
      simpl in Htmp; unfold patterns_of in Htmp;
      rewrite drop_all in Htmp;
      rewrite Nat.sub_diag drop_0 in Htmp;
      apply andb_prop in Htmp;
      destruct Htmp as [wfgg' wfl₂];
      pose proof (wfg := well_formed_imp_proj1 _ _ wfgg');
      exact wfg
    ).
  }
  exact wfl₁gg'l₂.
Defined.

Ltac2 run_in_reshaped_by_idx
  (n : constr) (f : unit -> unit) : unit :=
  do_ensureProofMode ();
  do_mlReshapeHypsByIdx n;
  f ();
  do_mlReshapeHypsBack ()
.

Ltac2 do_mlApplyn (n : constr) :=
  run_in_reshaped_by_idx n ( fun () =>
    Control.plus (fun () => apply MLGoal_weakenConclusion)
      (fun _ => throw_pm_exn_with_goal "do_mlApplyn: Failed for goal: ")
  )
.

Ltac2 Notation "mlApplyn" n(constr) :=
  do_mlApplyn n
.

Tactic Notation "mlApplyn" constr(n) :=
  let f := ltac2:(n |- do_mlApplyn (Option.get (Ltac1.to_constr n))) in
  f n
.


Ltac2 run_in_reshaped_by_name
  (name : constr) (f : unit -> unit) : unit :=
  do_ensureProofMode ();
  do_mlReshapeHypsByName name;
  f ();
  do_mlReshapeHypsBack ()
.

Ltac2 do_mlApply (name' : constr) :=
  run_in_reshaped_by_name name' (fun () =>
    Control.plus (fun () => apply MLGoal_weakenConclusion)
    (fun _ => throw_pm_exn_with_goal "do_mlApply: Goal does not match the conclusion of the hypothesis")
  )
.

Ltac2 Notation "mlApply" name(constr) :=
  do_mlApply name
.

Tactic Notation "mlApply" constr(name') :=
  let f := ltac2:(name' |- do_mlApply (Option.get (Ltac1.to_constr name'))) in
  f name'
.

Local Example ex_mlApplyn {Σ : Signature} Γ a b:
  well_formed a ->
  well_formed b ->
  Γ ⊢i a ---> (a ---> b) ---> b using BasicReasoning.
Proof.
  intros wfa wfb.
  toMLGoal.
  { wf_auto2. }
  mlIntro "H1".
  mlIntro "H2".
  Fail mlApply "H1".
  Fail mlApply "H3".
  mlApply "H2".
  fromMLGoal.
  apply P1; wf_auto2.
Defined.

Lemma Constructive_dilemma {Σ : Signature} Γ p q r s:
  well_formed p ->
  well_formed q ->
  well_formed r ->
  well_formed s ->
  Γ ⊢i ((p ---> q) ---> (r ---> s) ---> (p or r) ---> (q or s)) using BasicReasoning.
Proof.
  intros wfp wfq wfr wfs.
  unfold patt_or.

  toMLGoal.
  { wf_auto2. }

  mlIntro "H0". mlIntro "H1". mlIntro "H2". mlIntro "H3".
  mlApply "H1".
  mlApply "H2".
  mlIntro "H4".
  mlApply "H3".
  mlApply "H0".
  mlExact "H4".
Defined.

Lemma prf_impl_distr_meta {Σ : Signature} Γ a b c i:
  well_formed a ->
  well_formed b ->
  well_formed c ->
  Γ ⊢i (a ---> (b ---> c)) using i ->
  Γ ⊢i ((a ---> b) ---> (a ---> c)) using i.
Proof.
  intros wfa wfb wfc H.
  eapply MP.
  { apply H. }
  { useBasicReasoning. apply P2; wf_auto2. }
Defined.

Lemma prf_add_lemma_under_implication {Σ : Signature} Γ l g h:
  Pattern.wf l ->
  well_formed g ->
  well_formed h ->
  Γ ⊢i ((foldr patt_imp h l) --->
       ((foldr patt_imp g (l ++ [h])) --->
        (foldr patt_imp g l)))
  using BasicReasoning.
Proof.
  intros wfl wfg wfh.
  induction l; simpl.
  - apply modus_ponens; auto.
  - pose proof (wfal := wfl).
    unfold Pattern.wf in wfl. apply andb_prop in wfl. destruct wfl as [wfa wfl].
    specialize (IHl wfl).
    assert (H1: Γ ⊢i a --->
                    foldr patt_imp h l --->
                    foldr patt_imp g (l ++ [h]) --->
                    foldr patt_imp g l
            using BasicReasoning).
    { apply prf_add_assumption; try_wfauto2. assumption. }

    assert (H2 : Γ ⊢i (a ---> foldr patt_imp h l) --->
                     (a ---> foldr patt_imp g (l ++ [h]) --->
                     foldr patt_imp g l)
            using BasicReasoning).
    { apply prf_impl_distr_meta;[wf_auto2|wf_auto2|wf_auto2|]. apply H1. }

    assert (H3 : Γ ⊢i ((a ---> foldr patt_imp g (l ++ [h]) ---> foldr patt_imp g l)
                        ---> ((a ---> foldr patt_imp g (l ++ [h])) ---> (a ---> foldr patt_imp g l)))
            using BasicReasoning).
    { apply P2; wf_auto2. }

    eapply prf_weaken_conclusion_meta_meta.
    4: apply H3. 4: apply H2. all: wf_auto2.
Defined.

Lemma prf_add_lemma_under_implication_meta {Σ : Signature} Γ l g h i:
  Pattern.wf l ->
  well_formed g ->
  well_formed h ->
  Γ ⊢i (foldr patt_imp h l) using i ->
  Γ ⊢i ((foldr patt_imp g (l ++ [h])) ---> (foldr patt_imp g l)) using i.
Proof.
  intros WFl WFg WGh H.
  eapply MP.
  { apply H. }
  { useBasicReasoning. apply prf_add_lemma_under_implication. all: wf_auto2. }
Defined.

Lemma prf_add_lemma_under_implication_meta_meta {Σ : Signature} Γ l g h i:
  Pattern.wf l ->
  well_formed g ->
  well_formed h ->
  Γ ⊢i (foldr patt_imp h l) using i ->
  Γ ⊢i (foldr patt_imp g (l ++ [h])) using i ->
  Γ ⊢i (foldr patt_imp g l) using i.
Proof.
  intros WFl WFg WGh H H0.
  eapply MP.
  { apply H0. }
  { apply prf_add_lemma_under_implication_meta. 4: apply H. all: wf_auto2. }
Defined.

Lemma mlGoal_assert {Σ : Signature} Γ l name g h i:
  well_formed h ->
  mkMLGoal Σ Γ l h i ->
  mkMLGoal Σ Γ (l ++ [mkNH _ name h]) g i ->
  mkMLGoal Σ Γ l g i.
Proof.
  intros wfh H1 H2.
  unfold of_MLGoal in *. simpl in *.
  intros wfg wfl.
  eapply prf_add_lemma_under_implication_meta_meta.
  4: apply H1. 6: unfold patterns_of in H2; rewrite map_app in H2; apply H2. all: try assumption.
  { abstract (
      unfold Pattern.wf;
      rewrite map_app;
      rewrite foldr_app;
      simpl;
      rewrite wfh;
      simpl;
      exact wfl
    ).
  }
Defined.

Lemma impl_elim
  {Σ: Signature}
  (Γ : Theory)
  (A B C : Pattern)
  (l1 l2 : list Pattern)
  (i : ProofInfo)
  :
  Γ ⊢i foldr patt_imp A (l1 ++ l2) using i ->
  Γ ⊢i foldr patt_imp C (l1 ++ B :: l2) using i ->
  Γ ⊢i foldr patt_imp C (l1 ++ (A ---> B)::l2) using i
  .
Proof.
  intros H1 H2.
  assert (HwfA : well_formed A) by wf_auto2.
  assert (HwfB : well_formed B) by wf_auto2.
  assert (HwfC : well_formed C) by wf_auto2.
  apply reorder_last_to_middle_meta in H2. 2-5: wf_auto2.
  apply reorder_middle_to_last_meta. 1-4: wf_auto2.
  rewrite app_assoc foldr_snoc in H2. rewrite app_assoc foldr_snoc.
  eapply prf_add_lemma_under_implication_meta_meta.
  4: {
    apply H1.
  }
  1-3: wf_auto2.
  rewrite foldr_snoc.
  eapply prf_weaken_conclusion_iter_meta_meta. 5: exact H2. 1-3: wf_auto2.
  clear -HwfA HwfB HwfC.
  pose proof (syllogism Γ A B C HwfA HwfB HwfC).
  eapply reorder_meta in H. 2-4: wf_auto2.
  eapply prf_weaken_conclusion_meta_meta.
  4: gapply reorder. 1-3, 5-7: wf_auto2. try_solve_pile.
  by gapply H.
Defined.

Lemma mlGoal_destructImp {Σ : Signature} Γ l1 l2 name C A B i:
  mkMLGoal Σ Γ (l1 ++ l2) A i ->
  mkMLGoal Σ Γ (l1 ++ (mkNH _ name B)::l2) C i ->
  mkMLGoal Σ Γ (l1 ++ (mkNH _ name (A ---> B))::l2) C i.
Proof.
  intros H1 H2.
  unfold of_MLGoal in *. simpl in *.
  intros wfg wfl.
  unfold patterns_of in *. rewrite -> map_app in *.
  simpl in *.
  eapply impl_elim. apply H1. 3: apply H2.
  all: wf_auto2.
Defined.

Ltac2 do_mlDestructImp (name : constr) :=
  run_in_reshaped_by_name name (fun () =>
   Control.plus (fun () => apply (mlGoal_destructImp _ _ _ $name))
                 (fun _ => throw_pm_exn_with_goal "do_mlDestructImp: The given hypothesis was not an implication pattern: ")
  )
.

Ltac2 Notation "mlDestructImp" name(constr) :=
  do_mlDestructImp name
.

Tactic Notation "mlDestructImp" constr(name) :=
  let f := ltac2:(name |- do_mlDestructImp (Option.get (Ltac1.to_constr name))) in
  f name
.

Local Example Test_destructImp {Σ : Signature} Γ :
  forall A B C, well_formed A -> well_formed B -> well_formed C ->
  Γ ⊢i (A ---> B) ---> (B ---> C) ---> A ---> C using BasicReasoning.
Proof.
  intros. toMLGoal. wf_auto2.
  mlIntro "H". mlIntro "H0". mlIntro "H1".
  mlDestructImp "H".
  * mlExact "H1".
  * mlDestructImp "H0".
    - mlExact "H".
    - mlExact "H0".
Defined.

Lemma MLGoal_revert {Σ : Signature} (Γ : Theory) (l1 l2 : hypotheses) (x g : Pattern) (n : string) i :
  mkMLGoal Σ Γ (l1 ++ l2) (x ---> g) i ->
  mkMLGoal Σ Γ (l1 ++ (mkNH _ n x) :: l2) g i.
Proof.
  intros H.
  unfold of_MLGoal in H. simpl in H.
  unfold of_MLGoal. simpl. intros wfxig wfl.
  unfold patterns_of in *. rewrite -> map_app in *. simpl in *.
  ospecialize* H. 1-2: wf_auto2.
  apply reorder_middle_to_last_meta. 1-4: wf_auto2.
  by rewrite app_assoc foldr_snoc.
Defined.

Ltac2 do_mlRevert (name : constr) :=
  run_in_reshaped_by_name name (fun () =>
    Control.plus (fun () => apply (MLGoal_revert _ _ _ _ _ $name))
      (fun _ => throw_pm_exn_with_goal "do_mlRevert: failed for goal: ")
  )
.

Ltac2 Notation "mlRevert" name(constr) :=
  do_mlRevert name
.

Tactic Notation "mlRevert" constr(name) :=
  let f := ltac2:(name |- do_mlRevert (Option.get (Ltac1.to_constr name))) in
  f name
.


Local Example Test_revert {Σ : Signature} Γ :
  forall A B C, well_formed A -> well_formed B -> well_formed C ->
  Γ ⊢i A ---> B ---> C ---> A using BasicReasoning.
Proof.
  intros. toMLGoal. wf_auto2.
  mlIntro "H". mlIntro "H0". mlIntro "H1".
  mlRevert "H0". mlRevert "H1".
  Fail mlRevert "H0".
  mlIntro "H0". mlIntro "H1".
  mlExact "H".
Defined.

Lemma prf_add_lemma_under_implication_generalized {Σ : Signature} Γ l1 l2 g h:
  Pattern.wf l1 ->
  Pattern.wf l2 ->
  well_formed g ->
  well_formed h ->
  Γ ⊢i ((foldr patt_imp h l1) ---> ((foldr patt_imp g (l1 ++ [h] ++ l2)) ---> (foldr patt_imp g (l1 ++ l2))))
  using BasicReasoning.
Proof.
  intros wfl1 wfl2 wfg wfh.
  induction l1; simpl.
  - apply modus_ponens; wf_auto2.
  - pose proof (wfal1 := wfl1).
    unfold Pattern.wf in wfl1. simpl in wfl1. apply andb_prop in wfl1. destruct wfl1 as [wfa wfl1].
    specialize (IHl1 wfl1).
    assert (H1: Γ ⊢i a ---> foldr patt_imp h l1 ---> foldr patt_imp g (l1 ++ [h] ++ l2) ---> foldr patt_imp g (l1 ++ l2) using BasicReasoning).
    { apply prf_add_assumption; try_wfauto2. assumption. }
    assert (H2 : Γ ⊢i (a ---> foldr patt_imp h l1) ---> (a ---> foldr patt_imp g (l1 ++ [h] ++ l2) ---> foldr patt_imp g (l1 ++ l2)) using BasicReasoning).
    { apply prf_impl_distr_meta;[wf_auto2|wf_auto2|wf_auto2|]. exact H1. }
    assert (H3 : Γ ⊢i ((a ---> foldr patt_imp g (l1 ++ [h] ++ l2) ---> foldr patt_imp g (l1 ++ l2))
                        ---> ((a ---> foldr patt_imp g (l1 ++ [h] ++ l2)) ---> (a ---> foldr patt_imp g (l1 ++ l2)))) using BasicReasoning).
    { apply P2; wf_auto2. }

    eapply prf_weaken_conclusion_meta_meta.
    4: apply H3. 4: assumption. all: wf_auto2.
Defined.

Lemma prf_add_lemma_under_implication_generalized_meta {Σ : Signature} Γ l1 l2 g h i:
  Pattern.wf l1 ->
  Pattern.wf l2 ->
  well_formed g ->
  well_formed h ->
  Γ ⊢i (foldr patt_imp h l1) using i ->
  Γ ⊢i ((foldr patt_imp g (l1 ++ [h] ++ l2)) ---> (foldr patt_imp g (l1 ++ l2))) using i.
Proof.
  intros WFl1 WFl2 WFg WGh H.
  eapply MP.
  { apply H. }
  { useBasicReasoning.
    apply prf_add_lemma_under_implication_generalized; wf_auto2.
  }
Defined.

Lemma prf_add_lemma_under_implication_generalized_meta_meta {Σ : Signature} Γ l1 l2 g h i:
  Pattern.wf l1 ->
  Pattern.wf l2 ->
  well_formed g ->
  well_formed h ->
  Γ ⊢i (foldr patt_imp h l1) using i ->
  Γ ⊢i (foldr patt_imp g (l1 ++ [h] ++ l2)) using i ->
  Γ ⊢i (foldr patt_imp g (l1 ++ l2)) using i.
Proof.
  intros WFl1 WFl2 WFg WGh H H0.
  eapply MP.
  { apply H0. }
  { apply prf_add_lemma_under_implication_generalized_meta.
    5: apply H. all: wf_auto2.
  }
Defined.

Lemma mlGoal_assert_generalized {Σ : Signature} Γ l1 l2 name g h i:
  well_formed h ->
  mkMLGoal Σ Γ l1 h i ->
  mkMLGoal Σ Γ (l1 ++ [mkNH _ name h] ++ l2) g i ->
  mkMLGoal Σ Γ (l1 ++ l2) g i.
Proof.
  intros wfh H1 H2.
  unfold of_MLGoal in *. simpl in *.
  intros wfg wfl1l2.
  unfold patterns_of.
  rewrite map_app.
  eapply prf_add_lemma_under_implication_generalized_meta_meta.
  5: apply H1. 7: unfold patterns_of in H2; rewrite map_app in H2; apply H2. all: try assumption.
  { abstract (
        apply (wf_take (length (patterns_of l1))) in wfl1l2;
        unfold patterns_of in wfl1l2;
        rewrite map_app in wfl1l2;
        rewrite take_app in wfl1l2;
        rewrite firstn_all in wfl1l2;
        rewrite Nat.sub_diag take_0 app_nil_r in wfl1l2;
        exact wfl1l2
    ).
  }
  { abstract (
        apply (wf_drop (length (patterns_of l1))) in wfl1l2;
        unfold patterns_of in wfl1l2;
        rewrite map_app in wfl1l2;
        rewrite drop_app in wfl1l2;
        rewrite drop_all in wfl1l2;
        rewrite Nat.sub_diag drop_0 in wfl1l2;
        exact wfl1l2
    ).
  }
  { abstract (
        apply (wf_take (length (patterns_of l1))) in wfl1l2;
        unfold patterns_of in wfl1l2;
        rewrite map_app in wfl1l2;
        rewrite take_app in wfl1l2;
        rewrite firstn_all in wfl1l2;
        rewrite Nat.sub_diag take_0 app_nil_r in wfl1l2;
        exact wfl1l2
    ).
  }
  {
    abstract(
      pose proof (wfl1 := wf_take (length (patterns_of l1)) _ wfl1l2);
      unfold patterns_of in wfl1;
      rewrite map_app in wfl1;
      rewrite take_app in wfl1;
      pose proof (wfl2 := wf_drop (length (patterns_of l1)) _ wfl1l2);
      unfold patterns_of in wfl2;
      rewrite map_app in wfl2;
      rewrite drop_app in wfl2;
      unfold Pattern.wf; rewrite map_app; rewrite foldr_app;
      simpl; rewrite wfh; unfold Pattern.wf in wfl2;
      rewrite firstn_all in wfl1;
      rewrite Nat.sub_diag take_0 app_nil_r in wfl1;
      rewrite drop_all in wfl2;
      rewrite Nat.sub_diag drop_0 in wfl2;
      rewrite wfl2;
      simpl; exact wfl1
    ).
  }
Defined.

Ltac2 do_mlAssert_nocheck
  (name : constr) (t : constr) :=
  lazy_match! goal with
  | [ |- @of_MLGoal _ (@mkMLGoal ?sgm ?ctx ?l ?g ?i)] =>
    let hwf := Fresh.in_goal ident:(Hwf) in
    assert ($hwf : well_formed $t = true) >
    [()|(
      let hwf_constr := Control.hyp hwf in
      let h := Fresh.in_goal ident:(H) in
      assert ($h : @of_MLGoal $sgm (@mkMLGoal $sgm $ctx $l $t $i)) >
      [() |
        let h_constr := Control.hyp h in
        (eapply (@mlGoal_assert $sgm $ctx $l $name $g $t $i $hwf_constr $h_constr);
         ltac1:(rewrite [_ ++ _]/=); clear $h)]
    )]
  end.

Ltac2 Notation "_mlAssert_nocheck" "(" name(constr) ":" t(constr) ")" :=
  do_mlAssert_nocheck name t
.

Tactic Notation "_mlAssert_nocheck" "(" constr(name) ":" constr(t) ")" :=
  let f := ltac2:(name t |- do_mlAssert_nocheck (Option.get (Ltac1.to_constr name)) (Option.get (Ltac1.to_constr t))) in
  f name t
.

Ltac2 do_mlAssert (name : constr) (t : constr) :=
  do_ensureProofMode ();
  do_failIfUsed name;
  do_mlAssert_nocheck name t
.

Ltac2 Notation "mlAssert" "(" name(constr) ":" t(constr) ")" :=
  do_mlAssert name t
.

(* TODO: make this bind tigther. *)
Tactic Notation "mlAssert" "(" constr(name) ":" constr(t) ")" :=
  let f := ltac2:(name t |- do_mlAssert (Option.get (Ltac1.to_constr name)) (Option.get (Ltac1.to_constr t))) in
  f name t
.

Ltac2 do_mlAssert_autonamed (t : constr) :=
  do_ensureProofMode ();
  let hyps := do_getHypNames () in
  let name := eval lazy in (fresh $hyps) in
  do_mlAssert name t
.

Ltac2 Notation "mlAssert" "(" t(constr) ")" :=
  do_mlAssert_autonamed t
.

Tactic Notation "mlAssert" "(" constr(t) ")" :=
  let f := ltac2:(t |- do_mlAssert_autonamed (Option.get (Ltac1.to_constr t))) in
  f t
.

Local Example ex_mlAssert {Σ : Signature} Γ a:
  well_formed a ->
  Γ ⊢i (a ---> a ---> a) using BasicReasoning.
Proof.
  intros wfa.
  toMLGoal.
  { wf_auto2. }
  mlIntro "H0". mlIntro "H1".
  Fail mlAssert ("H0" : a).
  mlAssert ("H2" : a).
  { wf_auto2. }
  { mlExact "H1". }
  mlAssert (a).
  { wf_auto2. }
  { mlExact "H1". }
  mlExact "H2".
Qed.

Ltac2 _getGoalProofInfo () : constr :=
  lazy_match! goal with
  | [|- @of_MLGoal _ (@mkMLGoal _ _ _ _ ?i)]
    => i
  end.


Ltac2 _getGoalTheory () : constr :=
  lazy_match! goal with
  | [|- @of_MLGoal _ (@mkMLGoal _ ?ctx _ _ _)]
    => ctx
  end.

Ltac2 mlAssert_using_first
  (name : constr) (t : constr) (n : constr) :=
  do_ensureProofMode ();
  do_failIfUsed name;
  lazy_match! goal with
  | [|- @of_MLGoal ?sgm (@mkMLGoal ?sgm ?ctx ?l ?g ?i)] =>
    let l1 := Fresh.in_goal ident:(l1) in
    let l2 := Fresh.in_goal ident:(l2) in
    let heql1 := Fresh.in_goal ident:(Heql1) in
    let heql2 := Fresh.in_goal ident:(Heql2) in
    remember (take $n $l) as l1 eqn:$heql1 in |-;
    remember (drop $n $l) as l2 eqn:$heql2 in |-;
    simpl in Heql1; simpl in Heql2;
    eapply cast_proof_ml_hyps >
    [(
      ltac1:(l n |- rewrite -[l](take_drop n)) (Ltac1.of_constr l) (Ltac1.of_constr n);
      reflexivity
    )|()];
    let hwf := Fresh.in_goal ident:(Hwf) in
    assert ($hwf : well_formed $t = true) >
    [()|
      let h := Fresh.in_goal ident:(H) in
      let l1_constr := Control.hyp l1 in
(*       let l2_constr := Control.hyp l2 in *)
      let heql1_constr := Control.hyp heql1 in
      let hwf_constr := Control.hyp hwf in
      assert ($h : @of_MLGoal $sgm (@mkMLGoal $sgm $ctx $l1_constr $t $i)) >
      [
        (eapply cast_proof_ml_hyps>
         [(rewrite -> $heql1_constr; reflexivity)|()]);
         clear $l1 $l2 $heql1 $heql2
      | 
        let h_constr := Control.hyp h in
        apply (cast_proof_ml_hyps _ _ _ (f_equal patterns_of $heql1_constr)) in $h;
        eapply (@mlGoal_assert_generalized $sgm $ctx (take $n $l) (drop $n $l) $name $g $t $i $hwf_constr $h_constr);
        ltac1:(rewrite [_ ++ _]/=);
        clear $l1 $l2 $heql1 $heql2 $h
      ]
    ]
  end.

Ltac2 Notation "mlAssert" "(" name(constr) ":" t(constr) ")" "using" "first" n(constr) :=
  mlAssert_using_first name t n
.

Tactic Notation "mlAssert" "(" constr(name) ":" constr(t) ")" "using" "first" constr(n) :=
  let f := ltac2:(name t n |- mlAssert_using_first (Option.get (Ltac1.to_constr name)) (Option.get (Ltac1.to_constr t)) (Option.get (Ltac1.to_constr n))) in
  f name t n
.


Ltac2 mlAssert_autonamed_using_first
  (t : constr) (n : constr) :=
  do_ensureProofMode ();
  let hyps := do_getHypNames () in
  let name := eval cbv in (fresh $hyps) in
  mlAssert_using_first name t n
.

Ltac2 Notation "mlAssert" "(" t(constr) ")" "using" "first" n(constr)  :=
  mlAssert_autonamed_using_first t n
.

Tactic Notation "mlAssert" "(" constr(t) ")" "using" "first" constr(n)  :=
  let f := ltac2:(t n |- mlAssert_autonamed_using_first (Option.get (Ltac1.to_constr t)) (Option.get (Ltac1.to_constr n))) in
  f t n
.

Local Example ex_assert_using {Σ : Signature} Γ p q a b:
  well_formed a = true ->
  well_formed b = true ->
  well_formed p = true ->
  well_formed q = true ->
  Γ ⊢i a ---> p and q ---> b ---> ! ! q using BasicReasoning.
Proof.
  intros wfa wfb wfp wfq.
  toMLGoal.
  { wf_auto2. }
  mlIntro "H0".
  mlIntro "H1".
  mlIntro "H2".

  mlAssert ("H4" : p) using first 2.
  { wf_auto2. }
  { admit. }

  mlAssert (p) using first 2.
  { wf_auto2. }
  { admit. }

  remember "H5" as name.
  (* ltac2:(do_failIfUsed ident:(name)).*)
  mlAssert (name : p) using first 2.
  { wf_auto2. }
  { admit. }
Abort.

Lemma P4i' {Σ : Signature} (Γ : Theory) (A : Pattern) :
  well_formed A →
  Γ ⊢i ((!A ---> A) ---> A) using BasicReasoning.
Proof.
  intros wfA.
  assert (H1: Γ ⊢i ((! A ---> ! ! A) ---> ! ! A) using BasicReasoning).
  { apply P4i. wf_auto2. }
  assert (H2: Γ ⊢i ((! A ---> A) ---> (! A ---> ! ! A)) using BasicReasoning).
  { eapply prf_weaken_conclusion_meta. 
    4: apply not_not_intro.
    all: wf_auto2.
  }

  eapply prf_strenghten_premise_meta_meta. 4: apply H2.
  4: eapply prf_weaken_conclusion_meta_meta. 7: apply not_not_elim.
  8: { apply H1. }
  all: wf_auto2.
Defined.

Lemma tofold {Σ : Signature} p:
  p = fold_right patt_imp p [].
Proof.
  reflexivity.
Defined.

Lemma consume {Σ : Signature} p q l:
  fold_right patt_imp (p ---> q) l = fold_right patt_imp q (l ++ [p]).
Proof.
  rewrite foldr_app. reflexivity.
Defined.

Lemma prf_disj_elim {Σ : Signature} Γ p q r:
  well_formed p ->
  well_formed q ->
  well_formed r ->
  Γ ⊢i ((p ---> r) ---> (q ---> r) ---> (p or q) ---> r)
  using BasicReasoning.
Proof.
  intros wfp wfq wfr.
  pose proof (H1 := Constructive_dilemma Γ p r q r wfp wfr wfq wfr).
  assert (Γ ⊢i ((r or r) ---> r) using BasicReasoning).
  { unfold patt_or. apply P4i'. wf_auto2. }
  replace ((p ---> r) ---> (q ---> r) ---> p or q ---> r or r)
  with (foldr patt_imp ((p ---> r) ---> (q ---> r) ---> p or q ---> r or r) [])
  in H1 by reflexivity.
  do 3 rewrite -> consume in H1.
  eapply prf_weaken_conclusion_iter_meta_meta in H1. 5: apply H.
  { apply H1. }
  all: wf_auto2.
Defined.

Lemma prf_disj_elim_meta {Σ : Signature} Γ p q r i:
  well_formed p ->
  well_formed q ->
  well_formed r ->
  Γ ⊢i (p ---> r) using i ->
  Γ ⊢i ((q ---> r) ---> (p or q) ---> r) using i.
Proof.
  intros WFp WHq WFr H.
  eapply MP. apply H. useBasicReasoning. apply prf_disj_elim.
  all: wf_auto2.
Defined.

Lemma prf_disj_elim_meta_meta {Σ : Signature} Γ p q r i:
  well_formed p ->
  well_formed q ->
  well_formed r ->
  Γ ⊢i (p ---> r) using i ->
  Γ ⊢i (q ---> r) using i ->
  Γ ⊢i ((p or q) ---> r) using i.
Proof.
  intros WFp WHq WFr H H0.
  eapply MP. apply H0. apply prf_disj_elim_meta. 4: apply H.
  all: wf_auto2.
Defined.

Lemma prf_disj_elim_meta_meta_meta {Σ : Signature} Γ p q r i:
  well_formed p ->
  well_formed q ->
  well_formed r ->
  Γ ⊢i (p ---> r) using i ->
  Γ ⊢i (q ---> r) using i ->
  Γ ⊢i (p or q) using i ->
  Γ ⊢i r using i.
Proof.
  intros WFp WHq WFr H H0 H1.
  eapply MP. apply H1.
  apply prf_disj_elim_meta_meta.
  all: assumption.
Defined.

Lemma prf_add_proved_to_assumptions {Σ : Signature} Γ l a g i:
  Pattern.wf l ->
  well_formed a ->
  well_formed g ->
  Γ ⊢i a using i->
  Γ ⊢i ((foldr patt_imp g (a::l)) ---> (foldr patt_imp g l)) using i.
Proof.
  intros wfl wfa wfg Ha.
  induction l.
  - simpl.
    pose proof (modus_ponens Γ _ _ wfa wfg).
    eapply MP. apply Ha. useBasicReasoning. apply H.
  - pose proof (wfa0l := wfl).
    unfold Pattern.wf in wfl. simpl in wfl. apply andb_prop in wfl. destruct wfl as [wfa0 wfl].
    specialize (IHl wfl).
    simpl in IHl. simpl.
    (* < change a0 and a in the LHS > *)
    assert (H : Γ ⊢i (a ---> a0 ---> foldr patt_imp g l) ---> (a0 ---> a ---> foldr patt_imp g l) using BasicReasoning).
    { apply reorder; wf_auto2. }

    rewrite (tofold ((a ---> a0 ---> foldr patt_imp g l) ---> a0 ---> foldr patt_imp g l)).
    rewrite consume.
    pose proof (H0 := prf_strenghten_premise_iter_meta_meta Γ [] []).
    simpl in H0. simpl.
    specialize (H0 (a0 ---> a ---> foldr patt_imp g l) (a ---> a0 ---> foldr patt_imp g l)).
    specialize (H0 (a0 ---> foldr patt_imp g l)). simpl in H0. simpl.
    simpl. apply H0. all: try_wfauto2.
    { useBasicReasoning. apply H. }
    clear H0 H.
    (* </change a0 and a > *)
    assert (Γ ⊢i ((a ---> a0 ---> foldr patt_imp g l) ---> (a0 ---> foldr patt_imp g l)) using i).
    { eapply MP. 2: { useBasicReasoning. apply modus_ponens; wf_auto2. } apply Ha. }

    eapply prf_strenghten_premise_meta_meta. 5: apply H. all: try_wfauto2.
    useBasicReasoning.
    apply reorder; wf_auto2.
Defined.

Lemma prf_add_proved_to_assumptions_meta {Σ : Signature} Γ l a g i:
  Pattern.wf l ->
  well_formed a ->
  well_formed g ->
  Γ ⊢i a using i ->
  Γ ⊢i (foldr patt_imp g (a::l)) using i ->
  Γ ⊢i (foldr patt_imp g l) using i.
Proof.
  intros WFl WFa WFg H H0.
  eapply MP.
  apply H0.
  eapply prf_add_proved_to_assumptions.
  4: apply H.
  all: wf_auto2.
Defined.


Lemma MLGoal_add {Σ : Signature} Γ l name g h i:
  Γ ⊢i h using i ->
  mkMLGoal Σ Γ (mkNH _ name h::l) g i ->
  mkMLGoal Σ Γ l g i.
Proof.
  intros H H0.
  unfold of_MLGoal in *. simpl in *.
  intros wfg wfl.
  apply prf_add_proved_to_assumptions_meta with (a := h).
  5: apply H0.
  all: try assumption.
  { abstract (pose (tmp := proj1_sig H); apply proved_impl_wf in tmp; exact tmp). }
  { abstract (
        unfold Pattern.wf;
        simpl;
        pose (tmp := proj1_sig H);
        apply proved_impl_wf in tmp;
        rewrite tmp;
        simpl;
        exact wfl
    ).
  }
Defined.


Ltac2 do_mlAdd_as (n : constr) (name' : constr) :=
  do_ensureProofMode ();
  do_failIfUsed name';
  lazy_match! goal with
  | [|- @of_MLGoal ?sgm (@mkMLGoal ?sgm ?ctx ?l ?g ?i)] =>
  Control.plus(fun () =>
    apply (@MLGoal_add $sgm $ctx $l $name' $g _ $i $n)
  )
  (fun _ => throw_pm_exn (Message.concat (Message.of_string "do_mlAdd_as: given Coq hypothesis is not a pattern: ") (Message.of_constr n)))
  end.

Ltac2 Notation "mlAdd" n(constr) "as" name(constr) :=
  do_mlAdd_as n name
.

Tactic Notation "mlAdd" constr(n) "as" constr(name') :=
  let f := ltac2:(n name |- do_mlAdd_as (Option.get (Ltac1.to_constr n)) (Option.get (Ltac1.to_constr name))) in
  f n name'
.

Ltac2 get_fresh_name () : constr :=
  do_ensureProofMode ();
  let hyps := do_getHypNames () in
  let name := eval cbv in (fresh $hyps) in
  name
.

Ltac2 do_mlAdd (n : constr) :=
  do_mlAdd_as n (get_fresh_name ())
.

Ltac2 Notation "mlAdd" n(constr) :=
  do_mlAdd n
.

Tactic Notation "mlAdd" constr(n) :=
  let f := ltac2:(n |- do_mlAdd (Option.get (Ltac1.to_constr n))) in
  f n
.

Local Example ex_mlAdd {Σ : Signature} Γ l g h i:
  Pattern.wf l ->
  well_formed g ->
  well_formed h ->
  Γ ⊢i (h ---> g) using i ->
  Γ ⊢i h using i ->
  Γ ⊢i g using i.
Proof.
  intros WFl WFg WFh H H0.
  mlAdd H0 as "H0".
  mlAdd H.
  Fail mlAdd WFl as "0".
  Fail mlAdd WFl as "1".
  mlApply "0".
  mlExact "H0".
Defined.


Lemma prf_clear_hyp {Σ : Signature} Γ l1 l2 g h:
  Pattern.wf l1 ->
  Pattern.wf l2 ->
  well_formed g ->
  well_formed h ->
  Γ ⊢i (foldr patt_imp g (l1 ++ l2)) ---> (foldr patt_imp g (l1 ++ [h] ++ l2))
  using BasicReasoning.
Proof.
  intros wfl1 wfl2 wfg wfh.
  induction l1; simpl.
  - apply P1; wf_auto2.
  - unfold Pattern.wf in wfl1. simpl in wfl1. apply andb_prop in wfl1. destruct wfl1 as [wfa wfl1].
    specialize (IHl1 wfl1).

    assert (H1: Γ ⊢i a ---> foldr patt_imp g (l1 ++ l2) ---> foldr patt_imp g (l1 ++ [h] ++ l2) using BasicReasoning).
    {
      toMLGoal.
      { wf_auto2. }
      mlAdd IHl1 as "H0".
      mlIntro "H1". mlExact "H0".
    }
    apply prf_impl_distr_meta; try_wfauto2. apply H1.
Defined.

Lemma prf_clear_hyp_meta {Σ : Signature} Γ l1 l2 g h i:
  Pattern.wf l1 ->
  Pattern.wf l2 ->
  well_formed g ->
  well_formed h ->
  Γ ⊢i (foldr patt_imp g (l1 ++ l2)) using i ->
  Γ ⊢i (foldr patt_imp g (l1 ++ [h] ++ l2)) using i.
Proof.
  intros. eapply MP.
  apply H3.
  useBasicReasoning.
  apply prf_clear_hyp; wf_auto2.
Defined.



Lemma mlGoal_clear_hyp {Σ : Signature} Γ l1 l2 g h i:
  mkMLGoal Σ Γ (l1 ++ l2) g i ->
  mkMLGoal Σ Γ (l1 ++ h::l2) g i.
Proof.
  intros H1.
  unfold of_MLGoal in *. simpl in *. intros wfg wfl1hl2.
  unfold patterns_of in *. rewrite map_app.
  rewrite map_app in wfl1hl2; simpl in wfl1hl2.
  apply prf_clear_hyp_meta.
  5: rewrite map_app in H1; apply H1. all: try assumption.
  { apply wfl₁hl₂_proj_l₁ in wfl1hl2. exact wfl1hl2. }
  { apply wfl₁hl₂_proj_l₂ in wfl1hl2. exact wfl1hl2. }
  { apply wfl₁hl₂_proj_h in wfl1hl2. exact wfl1hl2. }
  { apply wfl₁hl₂_proj_l₁l₂ in wfl1hl2. exact wfl1hl2. }
Defined.


Ltac2 do_mlClear (name : constr) :=
  run_in_reshaped_by_name name (fun () =>
    apply mlGoal_clear_hyp
  )
.

Ltac2 Notation "mlClear" name(constr) :=
  do_mlClear name
.

Tactic Notation "mlClear" constr(name) :=
  let f := ltac2:(name |- do_mlClear (Option.get (Ltac1.to_constr name))) in
  f name
.

Local Example ex_mlClear {Σ : Signature} Γ a b c:
  well_formed a ->
  well_formed b ->
  well_formed c ->
  Γ ⊢i a ---> (b ---> (c ---> b)) using BasicReasoning.
Proof.
  intros wfa wfb wfc.
  toMLGoal.
  { wf_auto2. }
  mlIntro "H0". mlIntro "H1". mlIntro "H2".
  mlClear "H2".
  mlClear "H0".
  Fail mlClear "H0".
  mlExact "H1".
Defined.


Lemma not_concl {Σ : Signature} Γ p q:
  well_formed p ->
  well_formed q ->
  Γ ⊢i (p ---> (q ---> ((p ---> ! q) ---> ⊥))) using BasicReasoning.
Proof.
  intros wfp wfq.
  rewrite [(p ---> q ---> (p ---> ! q) ---> ⊥)]tofold.
  do 3 rewrite consume.
  rewrite [(((nil ++ [p]) ++ [q]) ++ [p ---> ! q])]/=.
  replace ([p; q; p--->!q]) with ([p] ++ [q; p ---> !q] ++ []) by reflexivity.
  apply prf_reorder_iter_meta; try_wfauto2.
  simpl.
  fold (! q).
  apply modus_ponens; wf_auto2.
Defined.

Lemma reorder_last_to_head {Σ : Signature} Γ g x l:
  Pattern.wf l ->
  well_formed g ->
  well_formed x ->
  Γ ⊢i ((foldr patt_imp g (x::l)) ---> (foldr patt_imp g (l ++ [x]))) using BasicReasoning.
Proof.
  intros wfl wfg wfx.
  induction l.
  - simpl. apply A_impl_A. wf_auto2.
  - pose proof (wfal := wfl).
    unfold Pattern.wf in wfl. simpl in wfl. apply andb_prop in wfl. destruct wfl as [wfa wfl].
    specialize (IHl wfl).
    simpl. simpl in IHl.
    eapply cast_proof'.
    { rewrite -> tofold at 1. repeat rewrite -> consume. reflexivity. }
    eapply prf_weaken_conclusion_iter_meta_meta.
    4: { apply IHl. }
    all: try_wfauto2.
    eapply cast_proof'.
    {
      rewrite consume.
      replace ((([] ++ [x ---> a ---> foldr patt_imp g l]) ++ [a]) ++ [x])
        with ([x ---> a ---> foldr patt_imp g l] ++ [a;x] ++ []) by reflexivity.
      reflexivity.
    }
    apply prf_reorder_iter_meta; wf_auto2.
    simpl. apply A_impl_A. wf_auto2.
Defined.

Lemma reorder_last_to_head_meta {Σ : Signature} Γ g x l i:
  Pattern.wf l ->
  well_formed g ->
  well_formed x ->
  Γ ⊢i (foldr patt_imp g (x::l)) using i ->
  Γ ⊢i (foldr patt_imp g (l ++ [x])) using i.
Proof.
  intros WFl WFG WFx H.
  eapply MP.
  apply H.
  useBasicReasoning.
  apply reorder_last_to_head; wf_auto2.
Defined.

(* Iterated modus ponens.
 For l = [x₁, ..., xₙ], it says that
 Γ ⊢i ((x₁ -> ... -> xₙ -> (x₁ -> ... -> xₙ -> r)) -> r)
*)
Lemma modus_ponens_iter {Σ : Signature} Γ l r:
  Pattern.wf l ->
  well_formed r ->
  Γ ⊢i (foldr patt_imp r (l ++ [foldr patt_imp r l])) using BasicReasoning.
Proof.
  intros wfl wfr.
  induction l.
  - simpl. apply A_impl_A. exact wfr.
  - pose proof (wfal := wfl).
    unfold Pattern.wf in wfl. simpl in wfl. apply andb_prop in wfl. destruct wfl as [wfa wfl].
    specialize (IHl wfl).
    simpl.
    eapply cast_proof'.
    { rewrite foldr_app. simpl. rewrite consume. simpl. reflexivity. }
    eapply cast_proof' in IHl.
    2: { rewrite foldr_app. reflexivity. }
    simpl in IHl.
    eapply prf_weaken_conclusion_meta_meta.
    4: { apply reorder_last_to_head; wf_auto2. }
    all: try_wfauto2.
    simpl. apply modus_ponens; wf_auto2.
Defined.

Lemma and_impl {Σ : Signature} Γ p q r:
  well_formed p ->
  well_formed q ->
  well_formed r ->
  Γ ⊢i ((p and q ---> r) ---> (p ---> (q ---> r))) using BasicReasoning.
Proof.
  intros wfp wfq wfr.
  toMLGoal.
  { wf_auto2. }
  mlIntro "H0". mlIntro "H2". mlIntro "H3".
  unfold patt_and. mlApply "H0".
  mlIntro "H4". unfold patt_or at 2.
  mlAssert ("H5" : (! ! p)).
  { wf_auto2. }
  {
    mlAdd (not_not_intro Γ p wfp) as "H6".
    mlApply "H6".
    mlExact "H2".
  }
  mlAssert ("H6" : (! q)).
  { wf_auto2. }
  {
    mlApply "H4". mlExact "H5".
  }
  mlApply "H6". mlExact "H3".
Defined.

Lemma and_impl' {Σ : Signature} Γ p q r:
  well_formed p ->
  well_formed q ->
  well_formed r ->
  Γ ⊢i ((p ---> (q ---> r)) ---> ((p and q) ---> r)) using BasicReasoning.
Proof.
  intros wfp wfq wfr.
  toMLGoal.
  { wf_auto2. }
  mlIntro "H0". mlIntro "H1".
  mlAssert ("H2" : p).
  { wf_auto2. }
  {
    mlAdd (pf_conj_elim_l Γ p q wfp wfq) as "H2".
    mlApply "H2".
    mlExact "H1".
  }
  mlAssert ("H3" : q).
  { wf_auto2. }
  {
    mlAdd (pf_conj_elim_r Γ p q wfp wfq) as "H4".
    mlApply "H4".
    mlExact "H1".
  }
  (* This pattern is basically an "apply ... in" *)
  mlAssert ("H4" : (q ---> r)).
  { wf_auto2. }
  { mlApply "H0". mlExact "H2". }
  mlApply "H4". mlExact "H3".
Defined.

Lemma prf_disj_elim_iter {Σ : Signature} Γ l p q r:
  Pattern.wf l ->
  well_formed p ->
  well_formed q ->
  well_formed r ->
  Γ ⊢i ((fold_right patt_imp r (l ++ [p]))
         --->
         ((fold_right patt_imp r (l ++ [q]))
            --->
            (fold_right patt_imp r (l ++ [p or q]))))
  using BasicReasoning.
Proof.
  intros wfl wfp wfq wfr.
  induction l.
  - simpl. apply prf_disj_elim; wf_auto2.
  - pose proof (wfal := wfl).
    unfold Pattern.wf in wfl. simpl in wfl. apply andb_prop in wfl. destruct wfl as [wfa wfl].
    specialize (IHl wfl).
    simpl in *.
    toMLGoal.
    { wf_auto2. }
    mlIntro "H0". mlIntro "H1". mlIntro "H2". 
    mlAdd IHl as "H3".
    mlAssert ("H4" : (foldr patt_imp r (l ++ [p]))).
    { wf_auto2. }
    { mlApply "H0". mlExact "H2". }
    mlAssert ("H5" : (foldr patt_imp r (l ++ [q]))).
    { wf_auto2. }
    { mlApply "H1". mlExact "H2". }
    mlAssert ("H6" : (foldr patt_imp r (l ++ [q]) ---> foldr patt_imp r (l ++ [p or q]))).
    { wf_auto2. }
    { mlApply "H3". mlExact "H4". }
    mlApply "H6".
    mlExact "H5".
Defined.

Lemma prf_disj_elim_iter_2 {Σ : Signature} Γ l₁ l₂ p q r:
  Pattern.wf l₁ ->
  Pattern.wf l₂ ->
  well_formed p ->
  well_formed q ->
  well_formed r ->
  Γ ⊢i ((fold_right patt_imp r (l₁ ++ [p] ++ l₂))
         --->
         ((fold_right patt_imp r (l₁ ++ [q] ++ l₂))
            --->
            (fold_right patt_imp r (l₁ ++ [p or q] ++ l₂))))
  using BasicReasoning.
Proof.
  intros wfl₁ wfl₂ wfp wfq wfr.
  move: l₁ wfl₁.
  induction l₂; intros l₁ wfl₁.
  - simpl. apply prf_disj_elim_iter; wf_auto2.
  - pose proof (wfal₂ := wfl₂).
    unfold Pattern.wf in wfl₂. simpl in wfl₂. apply andb_prop in wfl₂. destruct wfl₂ as [wfa wfl₂].

    simpl. (* We need to move 'a' to the beginning of l₁; then we can apply IHl₂. *)
    (* Or we can swap p and a (move a to the end of l_1) *)
    remember (foldr patt_imp r (l₁ ++ p :: a :: l₂)) as A in |-.
    remember (foldr patt_imp r (l₁ ++ q :: a :: l₂)) as B in |-.
    remember (foldr patt_imp r (l₁ ++ (p or q) :: a :: l₂)) as C in |-.
    eapply cast_proof'.
    { rewrite -HeqA. rewrite -HeqB. rewrite -HeqC. reflexivity. }
    eapply cast_proof'.
    {
      rewrite -> tofold at 1. rewrite consume. rewrite consume. rewrite [_ ++ [B] ]/=.
      rewrite -> HeqA at 1. rewrite -> HeqB at 1. rewrite -> HeqC at 1.
      reflexivity.
    }
    eapply prf_weaken_conclusion_iter_meta_meta.
    4: {
      eapply cast_proof'.
      {
        replace (l₁ ++ (p or q) :: a :: l₂) with (l₁ ++ [p or q; a] ++ l₂) by reflexivity.
        reflexivity.
      }
      apply prf_reorder_iter; wf_auto2.
    }
    all: try_wfauto2.
    simpl.

    eapply cast_proof'.
    { 
      rewrite -> tofold at 1. repeat rewrite consume. rewrite [_ ++ [_] ]/=.

    replace
      ([foldr patt_imp r (l₁ ++ p :: a :: l₂); foldr patt_imp r (l₁ ++ q :: a :: l₂)])
      with
        ([foldr patt_imp r (l₁ ++ p :: a :: l₂)] ++ (foldr patt_imp r (l₁ ++ q :: a :: l₂))::[])
      by reflexivity.
      reflexivity.
    }

    eapply prf_strenghten_premise_iter_meta_meta with (h := foldr patt_imp r (l₁ ++ a :: q :: l₂)).
    6: { apply prf_reorder_iter; wf_auto2. }
    all: try_wfauto2.

    eapply cast_proof'.
    {
      replace
        ([foldr patt_imp r (l₁ ++ p :: a :: l₂)] ++ [foldr patt_imp r (l₁ ++ a :: q :: l₂)])
        with
        ([] ++ ((foldr patt_imp r (l₁ ++ p :: a :: l₂))::[foldr patt_imp r (l₁ ++ a :: q :: l₂)]))
        by reflexivity.
      reflexivity.
   }

    eapply prf_strenghten_premise_iter_meta_meta with (h := (foldr patt_imp r (l₁ ++ a :: p :: l₂))).
    6: {  apply prf_reorder_iter; wf_auto2. }
    all: try_wfauto2.

    simpl.
    eapply cast_proof'.
    {
      replace (l₁ ++ a :: p :: l₂) with ((l₁ ++ [a]) ++ [p] ++ l₂) by (rewrite <- app_assoc; reflexivity).
      replace (l₁ ++ a :: q :: l₂) with ((l₁ ++ [a]) ++ [q] ++ l₂) by (rewrite <- app_assoc; reflexivity).
      replace (l₁ ++ a :: (p or q) :: l₂) with ((l₁ ++ [a]) ++ [p or q] ++ l₂) by (rewrite <- app_assoc; reflexivity).
      reflexivity.
    }
    apply IHl₂; wf_auto2.
Defined.

Lemma prf_disj_elim_iter_2_meta {Σ : Signature} Γ l₁ l₂ p q r i:
  Pattern.wf l₁ ->
  Pattern.wf l₂ ->
  well_formed p ->
  well_formed q ->
  well_formed r ->
  Γ ⊢i (fold_right patt_imp r (l₁ ++ [p] ++ l₂)) using i ->
  Γ ⊢i ((fold_right patt_imp r (l₁ ++ [q] ++ l₂))
            --->
            (fold_right patt_imp r (l₁ ++ [p or q] ++ l₂))) using i.
Proof.
  intros WFl1 WFl2 WFp WFq WFr H.
  eapply MP.
  apply H.
  useBasicReasoning.
  apply prf_disj_elim_iter_2; wf_auto2.
Defined.

Lemma prf_disj_elim_iter_2_meta_meta {Σ : Signature} Γ l₁ l₂ p q r i:
  Pattern.wf l₁ ->
  Pattern.wf l₂ ->
  well_formed p ->
  well_formed q ->
  well_formed r ->
  Γ ⊢i (fold_right patt_imp r (l₁ ++ [p] ++ l₂)) using i ->
  Γ ⊢i (fold_right patt_imp r (l₁ ++ [q] ++ l₂)) using i ->
  Γ ⊢i (fold_right patt_imp r (l₁ ++ [p or q] ++ l₂)) using i.
Proof.
  intros WFl1 WFl2 WFp WFq WFr H H0.
  eapply MP.
  2: { apply prf_disj_elim_iter_2_meta; try_wfauto2. apply H. }
  apply H0.
Defined.

Lemma MLGoal_disj_elim {Σ : Signature} Γ l₁ l₂ pn p qn q pqn r i:
  mkMLGoal Σ Γ (l₁ ++ (mkNH _ pn p) :: l₂) r i ->
  mkMLGoal Σ Γ (l₁ ++ (mkNH _ qn q) :: l₂) r i ->
  mkMLGoal Σ Γ (l₁ ++ (mkNH _ pqn (p or q)) :: l₂) r i.
Proof.
  intros H1 H2.
  unfold of_MLGoal in *. simpl in *.
  intros wfr Hwf.
  unfold patterns_of in *.
  rewrite map_app.
  rewrite map_app in H1.
  rewrite map_app in H2.
  apply prf_disj_elim_iter_2_meta_meta.
  7: apply H2.
  6: apply H1.
  all: try assumption; unfold patterns_of in *; rewrite map_app in Hwf.
  { abstract (apply wfl₁hl₂_proj_l₁ in Hwf; exact Hwf). }
  { abstract (apply wfl₁hl₂_proj_l₂ in Hwf; exact Hwf). }
  { abstract (apply wfl₁hl₂_proj_h in Hwf; wf_auto2). }
  { abstract (apply wfl₁hl₂_proj_h in Hwf; wf_auto2). }
  {
    pose proof (wfl₁hl₂_proj_l₁ _ _ _ Hwf).
    pose proof (wfl₁hl₂_proj_h _ _ _ Hwf).
    pose proof (wfl₁hl₂_proj_l₂ _ _ _ Hwf).
    apply wf_app; [assumption|].
    unfold patt_or,patt_not in *.
    simpl.
    wf_auto2.
  }
  {
    pose proof (wfl₁hl₂_proj_l₁ _ _ _ Hwf).
    pose proof (wfl₁hl₂_proj_h _ _ _ Hwf).
    pose proof (wfl₁hl₂_proj_l₂ _ _ _ Hwf).
    apply wf_app; [assumption|].
    unfold patt_or,patt_not in *.
    simpl.
    wf_auto2.
  }
Defined.

Ltac2 do_mlDestructOr_as (name : constr) (name1 : constr) (name2 : constr) :=
  do_ensureProofMode ();
  do_failIfUsed name1;
  do_failIfUsed name2;
  lazy_match! goal with
  | [|- @of_MLGoal _ (@mkMLGoal _ _ _ _ _)] =>
    (* let htd := Fresh.in_goal ident:(Htd) in *)
    eapply cast_proof_ml_hyps;
    f_equal;
    _mlReshapeHypsByName name;
    Control.plus (fun () =>
      apply MLGoal_disj_elim with (pqn := $name) (pn := $name1) (qn := $name2);
      _mlReshapeHypsBack
    )
    (fun _ => _mlReshapeHypsBack; 
      throw_pm_exn_with_goal "do_mlDestructOr_as: failed for goal: ")
  end
.

Ltac2 Notation "mlDestructOr" name(constr) "as" name1(constr) name2(constr) :=
  do_mlDestructOr_as name name1 name2
.

Tactic Notation "mlDestructOr" constr(name) "as" constr(name1) constr(name2) :=
  let f := ltac2:(name name1 name2 |- do_mlDestructOr_as (Option.get (Ltac1.to_constr name)) (Option.get (Ltac1.to_constr name1)) (Option.get (Ltac1.to_constr name2))) in
  f name name1 name2
.

Ltac2 do_mlDestructOr (name : constr) :=
  do_ensureProofMode ();
  let hyps := do_getHypNames () in
  let name0 := eval cbv in (fresh $hyps) in
  let name1 := eval cbv in (fresh ($name0 :: $hyps)) in
  mlDestructOr $name as $name0 $name1
.

Ltac2 Notation "mlDestructOr" name(constr) :=
  do_mlDestructOr name
.

Tactic Notation "mlDestructOr" constr(name) :=
  let f := ltac2:(name |- do_mlDestructOr (Option.get (Ltac1.to_constr name))) in
  f name
.

Local Example exd {Σ : Signature} Γ a b p q c i:
  well_formed a ->
  well_formed b ->
  well_formed p ->
  well_formed q ->
  well_formed c ->
  Γ ⊢i (a ---> p ---> b ---> c) using i ->
  Γ ⊢i (a ---> q ---> b ---> c) using i->
  Γ ⊢i (a ---> (p or q) ---> b ---> c) using i.
Proof.
  intros WFa WFb WFp WFq WFc H H0.
  toMLGoal.
  { wf_auto2. } 
  mlIntro "H0".
  mlIntro "H1".
  mlIntro "H2".
  Fail mlDestructOr "H3".
  Fail mlDestructOr "H0".
  mlDestructOr "H1".
  - fromMLGoal. apply H.
  - fromMLGoal. apply H0.
Defined.

Lemma pf_iff_split {Σ : Signature} Γ A B i:
  well_formed A ->
  well_formed B ->
  Γ ⊢i A ---> B using i ->
  Γ ⊢i B ---> A using i ->
  Γ ⊢i A <---> B using i.
Proof.
  intros wfA wfB AimplB BimplA.
  unfold patt_iff.
  apply conj_intro_meta; try_wfauto2; assumption.
Defined.

Lemma pf_iff_proj1 {Σ : Signature} Γ A B i:
  well_formed A ->
  well_formed B ->
  Γ ⊢i A <---> B using i ->
  Γ ⊢i A ---> B using i.
Proof.
  intros WFA WFB H. unfold patt_iff in H.
  apply pf_conj_elim_l_meta in H; try_wfauto2; assumption.
Defined.

Lemma pf_iff_proj2 {Σ : Signature} Γ A B i:
  well_formed A ->
  well_formed B ->
  Γ ⊢i (A <---> B) using i ->
  Γ ⊢i (B ---> A) using i.
Proof.
  intros WFA WFB H. unfold patt_iff in H.
  apply pf_conj_elim_r_meta in H; try_wfauto2; assumption.
Defined.

Lemma pf_iff_iff {Σ : Signature} Γ A B i:
  well_formed A ->
  well_formed B ->
  prod ((Γ ⊢i (A <---> B) using i) -> (prod (Γ ⊢i (A ---> B) using i) (Γ ⊢i (B ---> A) using i)))
  ( (prod (Γ ⊢i (A ---> B) using i)  (Γ ⊢i (B ---> A) using i)) -> (Γ ⊢i (A <---> B) using i)).
Proof.
  intros WFA WFB.
  split; intros H.
  {
    pose proof (H1 := pf_iff_proj1 _ _ _ _ WFA WFB H).
    pose proof (H2 := pf_iff_proj2 _ _ _ _ WFA WFB H).
    split; assumption.
  }
  {
    destruct H as [H1 H2].
    apply pf_iff_split; assumption.
  }
Defined.

Lemma pf_iff_equiv_refl {Σ : Signature} Γ A :
  well_formed A ->
  Γ ⊢i (A <---> A) using BasicReasoning.
Proof.
  intros WFA.
  apply pf_iff_split; try_wfauto2; apply A_impl_A; assumption.
Defined.

Lemma pf_iff_equiv_sym {Σ : Signature} Γ A B i:
  well_formed A ->
  well_formed B ->
  Γ ⊢i (A <---> B) using i ->
  Γ ⊢i (B <---> A) using i.
Proof.
  intros wfA wfB H.
  pose proof (H2 := H).
  apply pf_iff_proj2 in H2; try_wfauto2.
  rename H into H1.
  apply pf_iff_proj1 in H1; try_wfauto2.
  apply pf_iff_split; try_wfauto2; assumption.
Defined.

Lemma pf_iff_equiv_trans {Σ : Signature} Γ A B C i:
  well_formed A ->
  well_formed B ->
  well_formed C ->
  Γ ⊢i (A <---> B) using i ->
  Γ ⊢i (B <---> C) using i ->
  Γ ⊢i (A <---> C) using i.
Proof.
  intros wfA wfB wfC AeqB BeqC.
  apply pf_iff_iff in AeqB; try_wfauto2. destruct AeqB as [AimpB BimpA].
  apply pf_iff_iff in BeqC; try_wfauto2. destruct BeqC as [BimpC CimpB].
  apply pf_iff_iff; try_wfauto2.
  split.
  {
    eapply syllogism_meta. 4,5: eassumption.
    1-3: wf_auto2.
  }
  {
    eapply syllogism_meta. 4,5: eassumption.
    1-3: wf_auto2.
  }
Defined.

Lemma prf_conclusion {Σ : Signature} Γ a b i:
  well_formed a ->
  well_formed b ->
  Γ ⊢i b using i ->
  Γ ⊢i (a ---> b) using i.
Proof.
  intros WFa WFb H. eapply MP.
  apply H.
  useBasicReasoning.
  apply P1; wf_auto2.
Defined.



Lemma and_of_negated_iff_not_impl {Σ : Signature} Γ p1 p2:
  well_formed p1 ->
  well_formed p2 ->
  Γ ⊢i (! (! p1 ---> p2) <---> ! p1 and ! p2)
  using BasicReasoning.
Proof.
  intros wfp1 wfp2.
  apply conj_intro_meta.
  { wf_auto2. }
  { wf_auto2. }
  - toMLGoal.
    { wf_auto2. }
    mlIntro "H0". mlIntro "H1".
    mlApply "H0".
    mlIntro "H2".
    unfold patt_or.
    mlAdd (not_not_elim Γ p2 ltac:(wf_auto2)) as "H3".
    mlApply "H3".
    mlApply "H1".
    mlAdd (not_not_intro Γ (! p1) ltac:(wf_auto2)) as "H4".
    mlApply "H4".
    mlExact "H2".
  - toMLGoal.
    { wf_auto2. }
    mlIntro "H0". mlIntro "H1".
    unfold patt_and.
    mlApply "H0".
    unfold patt_or.
    mlIntro "H2".
    mlAdd (@not_not_intro Σ Γ p2 ltac:(wf_auto2)) as "H3".
    mlApply "H3".
    mlApply "H1".
    mlAdd (@not_not_elim Σ Γ (! p1) ltac:(wf_auto2)) as "H4".
    mlApply "H4".
    mlExact "H2".
Defined.

Lemma and_impl_2 {Σ : Signature} Γ p1 p2:
  well_formed p1 ->
  well_formed p2 ->
  Γ ⊢i (! (p1 ---> p2) <---> p1 and ! p2)
  using BasicReasoning.
Proof.
  intros wfp1 wfp2.
  apply conj_intro_meta.
  { wf_auto2. }
  { wf_auto2. }
  - toMLGoal.
    { wf_auto2. }
    mlIntro "H0". mlIntro "H1".
    mlApply "H0".
    mlIntro "H2".
    unfold patt_or.
    mlAdd (not_not_elim Γ p2 ltac:(wf_auto2)) as "H3".
    mlApply "H3".
    mlApply "H1".
    mlAdd (not_not_intro Γ p1 ltac:(wf_auto2)) as "H4".
    mlApply "H4".
    mlExact "H2".
  - toMLGoal.
    { wf_auto2. }
    mlIntro "H0". mlIntro "H1".
    mlApply "H0".
    unfold patt_or.
    mlIntro "H2".
    mlAdd (not_not_intro Γ p2 ltac:(wf_auto2)) as "H3".
    mlApply "H3".
    mlApply "H1".
    mlAdd (not_not_elim Γ p1 ltac:(wf_auto2)) as "H4".
    mlApply "H4".
    mlExact "H2".
Defined.

Lemma conj_intro_meta_partial {Σ : Signature} (Γ : Theory) (A B : Pattern) (i : ProofInfo) :
  well_formed A → well_formed B →
  Γ ⊢i A using i →
  Γ ⊢i B ---> (A and B) using i.
Proof.
  intros WFA WFB H.
  eapply MP.
  - exact H.
  - useBasicReasoning. apply conj_intro.
    { wf_auto2. }
    { wf_auto2. }
Defined.

Lemma and_impl_patt {Σ : Signature} (A B C : Pattern) Γ (i : ProofInfo):
  well_formed A → well_formed B → well_formed C →
  Γ ⊢i A using i ->
  Γ ⊢i ((A and B) ---> C) using i ->
  Γ ⊢i (B ---> C) using i.
Proof.
  intros WFA WFB WFC H H0.
  eapply @syllogism_meta with (B := patt_and A B).
  { wf_auto2. }
  { wf_auto2. }
  { wf_auto2. }
  2: { exact H0. }
  apply conj_intro_meta_partial.
  { wf_auto2. }
  { wf_auto2. }
  exact H.
Defined.

Lemma conj_intro2 {Σ : Signature} (Γ : Theory) (A B : Pattern) :
  well_formed A -> well_formed B ->
  Γ ⊢i (A ---> (B ---> (B and A)))
  using BasicReasoning.
Proof.
  intros WFA WFB. eapply reorder_meta.
  { wf_auto2. }
  { wf_auto2. }
  { wf_auto2. }
  apply conj_intro.
  { wf_auto2. }
  { wf_auto2. }
Defined.

Lemma conj_intro_meta_partial2  {Σ : Signature} (Γ : Theory) (A B : Pattern) (i : ProofInfo):
  well_formed A → well_formed B →
  Γ ⊢i A using i →
  Γ ⊢i B ---> (B and A) using i.
Proof.
  intros WFA WFB H.
  eapply MP.
  - exact H.
  - useBasicReasoning. apply conj_intro2.
    { wf_auto2. }
    { wf_auto2. }
Defined.

Lemma and_impl_patt2 {Σ : Signature}  (A B C : Pattern) Γ (i : ProofInfo):
  well_formed A → well_formed B → well_formed C →
  Γ ⊢i A using i ->
  Γ ⊢i ((B and A) ---> C) using i ->
  Γ ⊢i (B ---> C) using i.
Proof.
  intros WFA WFB WFC H H0.
  eapply @syllogism_meta with (B := patt_and B A).
  { wf_auto2. }
  { wf_auto2. }
  { wf_auto2. }
  2: exact H0.
  apply conj_intro_meta_partial2.
  { wf_auto2. }
  { wf_auto2. }
  exact H.
Defined.


Lemma patt_and_comm_meta {Σ : Signature} (A B : Pattern) (Γ : Theory) (i : ProofInfo) :
  well_formed A → well_formed B
  ->
  Γ ⊢i A and B using i ->
  Γ ⊢i B and A using i.
Proof.
  intros WFA WFB H.
  apply pf_conj_elim_r_meta in H as P1.
  apply pf_conj_elim_l_meta in H as P2. all: try_wfauto2.
  apply conj_intro_meta; assumption.
Defined.

Lemma MLGoal_applyMeta {Σ : Signature} Γ r r' i:
  Γ ⊢i (r' ---> r) using i ->
  forall l,
  mkMLGoal Σ Γ l r' i ->
  mkMLGoal Σ Γ l r i.
Proof.
  intros Himp l H.
  unfold of_MLGoal in *. simpl in *.
  intros wfr wfl.
  eapply prf_weaken_conclusion_iter_meta_meta.
  4: apply Himp.
  4: apply H.
  all: try assumption.
  1,2: pose proof (wfrr' := proved_impl_wf _ _ (proj1_sig Himp)); wf_auto2.
Defined.

(* Error message of this one is sufficient *)
Ltac2 do_mlApplyMetaRaw (t : constr) :=
  eapply (@MLGoal_applyMeta _ _ _ _ _ $t)
.

Ltac2 Notation "_mlApplyMetaRaw" t(open_constr) :=
  do_mlApplyMetaRaw t
.

Tactic Notation "_mlApplyMetaRaw" uconstr(t) :=
  let f := ltac2:(t |- do_mlApplyMetaRaw (Option.get (Ltac1.to_constr t))) in
  f t
.

Lemma MLGoal_left {Σ : Signature} Γ l x y i:
  mkMLGoal Σ Γ l x i ->
  mkMLGoal Σ Γ l (patt_or x y) i.
Proof.
  intros H.
  unfold of_MLGoal in *. simpl in *.
  intros wfxy wfl.
  eapply prf_weaken_conclusion_iter_meta_meta.
  4: { useBasicReasoning. apply disj_left_intro. wf_auto2. wf_auto2. }
  { wf_auto2. }
  { wf_auto2. }
  { wf_auto2. }
  apply H.
  { wf_auto2. }
  { assumption. }
Defined.

Lemma MLGoal_right {Σ : Signature} Γ l x y i:
  mkMLGoal Σ Γ l y i ->
  mkMLGoal Σ Γ l (patt_or x y) i.
Proof.
  intros H.
  unfold of_MLGoal in *. simpl in *.
  intros wfxy wfl.
  eapply prf_weaken_conclusion_iter_meta_meta.
  4: { useBasicReasoning. apply disj_right_intro. wf_auto2. wf_auto2. }
  { wf_auto2. }
  { wf_auto2. }
  { wf_auto2. }
  apply H.
  { wf_auto2. }
  { assumption. }
Defined.

Ltac2 mlLeft () :=
  _ensureProofMode;
  Control.plus(fun () =>
    apply MLGoal_left
  )
  (fun _ => throw_pm_exn_with_goal "mlLeft: Current matching logic goal is not a disjunction! ")
.

Ltac2 mlRight () :=
  _ensureProofMode;
  Control.plus(fun () =>
    apply MLGoal_right
  )
  (fun _ => throw_pm_exn_with_goal "mlLeft: Current matching logic goal is not a disjunction! ")
.

Ltac mlLeft := ltac2:(mlLeft ()).
Ltac mlRight := ltac2:(mlRight ()).


Local Example ex_mlLeft {Σ : Signature} Γ a:
  well_formed a ->
  Γ ⊢i a ---> (a or a)
  using BasicReasoning.
Proof.
  intros wfa.
  toMLGoal.
  { wf_auto2. }
  Fail mlLeft.
  mlIntro "H0".
  mlLeft.
  mlExact "H0".
Defined.

Lemma MLGoal_applyMetaIn {Σ : Signature} Γ n r n' r' i:
  Γ ⊢i (r ---> r') using i ->
  forall l₁ l₂ g,
    mkMLGoal Σ Γ (l₁ ++ (mkNH _ n' r')::l₂) g i ->
    mkMLGoal Σ Γ (l₁ ++ (mkNH _ n r)::l₂ ) g i.
Proof.
  intros Himp l₁ l₂ g H.
  unfold of_MLGoal in *. simpl in *.
  intros wfg Hwf.
  specialize (H wfg).
  unfold patterns_of in *.
  rewrite map_app in H.
  rewrite map_app.
  eapply prf_strenghten_premise_iter_meta_meta.
  6: apply Himp.
  6: apply H.
  all: rewrite map_app in Hwf.
  { abstract (apply wfapp_proj_1 in Hwf; exact Hwf). }
  { abstract (apply wfl₁hl₂_proj_l₂ in Hwf; exact Hwf). }
  { abstract (pose proof (Himp' := proj1_sig Himp); apply proved_impl_wf in Himp'; wf_auto2). }
  { abstract (apply wfl₁hl₂_proj_h in Hwf; exact Hwf). }
  { exact wfg. }
  { abstract(
      pose proof (wfapp_proj_1 _ _ Hwf);
      pose proof (wfl₁hl₂_proj_l₂ _ _ _ Hwf);
      pose proof (wfl₁hl₂_proj_h _ _ _ Hwf);
      unfold Pattern.wf;
      rewrite map_app;
      rewrite foldr_app;
      simpl;
      pose proof (Himp' := proj1_sig Himp);
      apply proved_impl_wf in Himp';
      apply well_formed_imp_proj2 in Himp';
      rewrite Himp';
      simpl;
      unfold Pattern.wf in H1;
      rewrite H1;
      exact H0
    ).
 }
Defined.

Ltac2 do_mlApplyMetaRawIn (t : constr) (name : constr) :=
  eapply cast_proof_ml_hyps;
  f_equal;

  run_in_reshaped_by_name name (fun () =>
    eapply (@MLGoal_applyMetaIn _ _ _ _ $name _ _ $t)
  )
.

Ltac do_mlApplyMetaRawIn t name :=
  let f := ltac2:(t name |- do_mlApplyMetaRawIn (Option.get (Ltac1.to_constr t)) (Option.get (Ltac1.to_constr name))) in
  f t name
.

Ltac2 do_mlApplyMetaRaw0 (t : constr) (cl : constr option) :=
  match cl with
  | None => do_mlApplyMetaRaw t
  | Some n => do_mlApplyMetaRawIn t n
  end
.

Ltac2 Notation "_mlApplyMetaRaw" t(constr) cl(opt(seq("in", constr))) :=
  do_mlApplyMetaRaw0 t cl
.

Tactic Notation "mlApplyMetaRaw" constr(t) "in" constr(name) :=
  let f := ltac2:(t name |- do_mlApplyMetaRawIn (Option.get (Ltac1.to_constr t)) (Option.get (Ltac1.to_constr name))) in
  f t name
.

Local Example Private_ex_mlApplyMetaRawIn {Σ : Signature} Γ p q:
  well_formed p ->
  well_formed q ->
  Γ ⊢i p ---> (p or q)
  using BasicReasoning.
Proof.
  intros wfp wfq.
  toMLGoal.
  { wf_auto2. }
  mlIntro "H0".
  mlApplyMetaRaw (disj_left_intro Γ p q ltac:(wf_auto2) ltac:(wf_auto2)) in "H0".
  mlExact "H0".
Defined.

Ltac2 rec applyRec (f : constr) (xs : constr list) : constr option :=
  match xs with
  | [] => Some f
  | y::ys =>
    lazy_match! Constr.type f with
    | (forall _ : _, _) =>
      Control.plus (fun () => applyRec constr:($f $y) ys) (fun _ => None)
    | _ => None
    end
  end.

Ltac2 Eval (applyRec constr:(Nat.add) [constr:(1);constr:(2)]).

(*
  All thic complicated code is here only for one reason:
  I want to be able to first run the tactic with all the parameters
  inferred or question marked, which results in another goal.
  And then I want to handle the subgoals generated by the filling-in
  underscores / question marks.
  In particular, I want the proof mode goals to be generated first,
  and the other, uninteresting goals, next.
*)
Ltac2 rec fillWithUnderscoresAndCall0
  (tac : constr -> unit) (t : constr) (args : constr list) :=
  (*
  Message.print (
    Message.concat
      (Message.of_string "fillWithUnderscoresAndCall: t = ")
      (Message.of_constr t)
  );
  Message.print (
    Message.concat
      (Message.of_string "fillWithUnderscoresAndCall: args = ")
      (List.fold_right (Message.concat) (Message.of_string "") (List.map Message.of_constr args))
  );
  *)
  let cont := (fun () =>
    lazy_match! Constr.type t with
    | (?t' -> ?_t's) => (* NOTE, (COQ BUG?) If I omit ?t's from here,
                          forall withh match this branch
                          
                          NOTE2: This matching is fragile. Implication
                          hypotheses also seem to match the second branch
                          with forall _ : _ , _*)
      lazy_match! goal with
      | [|- ?g] =>
        let h := Fresh.in_goal ident:(hasserted) in
        assert($h : $t' -> $g) > [(
          let pftprime := Fresh.in_goal ident:(pftprime) in
          intro $pftprime;
          let new_t := open_constr:($t ltac2:(Notations.exact0 false (fun () => Control.hyp (pftprime)))) in
          fillWithUnderscoresAndCall0 tac new_t args;
          Std.clear [pftprime]
        )|(
          let h_constr := Control.hyp h in
          apply $h_constr
          )
        ]
      end
    | (forall _ : _, _) => fillWithUnderscoresAndCall0 tac open_constr:($t _) args
    | ?remainder => Control.throw (Invalid_argument (Some (Message.concat (Message.concat (Message.of_string "Remainder type: ") (Message.of_constr remainder)) (Message.concat (Message.of_string ", of term") (Message.of_constr t)))))
    end
  ) in
  match (applyRec t args) with
  | None =>
    (* Cannot apply [t] to [args] => continue *)
    cont ()
  | Some result =>
    (* Can apply [to] to [args], *)
    lazy_match! Constr.type result with
    | (forall _ : _, _) =>
      (* but result would still accept an argument => continue *)
      cont ()
    | _ =>
      (* and nothing more can be applied to the result => we are done *)
      tac result
    end
  end
.

Ltac2 rec fillWithUnderscoresAndCall
  (tac : constr -> unit) (twb : Std.constr_with_bindings) (args : constr list)
  :=
  let t := Fresh.in_goal ident:(t) in
  Notations.specialize0 (fun () => twb) (Some (Std.IntroNaming (Std.IntroIdentifier t)));
  let t_constr := Control.hyp t in
  fillWithUnderscoresAndCall0 tac t_constr args;
  clear $t
.

(*
  We have this double-primed version because we want to be able
  to feed it the proof before feeding it the ProofInfoLe.
*)
Lemma useGenericReasoning''  {Σ : Signature} (Γ : Theory) (ϕ : Pattern) i' i:
  Γ ⊢i ϕ using i' ->
  (ProofInfoLe i' i) ->
  Γ ⊢i ϕ using i.
Proof.
  intros H pile.
  eapply useGenericReasoning.
  { apply pile. }
  apply H.
Defined.

(* TODO: Create error messages for the following tactics *)
Ltac2 _callCompletedAndCast (twb : Std.constr_with_bindings) (tac : constr -> unit) :=
  let tac' := (fun (t' : constr) =>
    let tcast := open_constr:(@useGenericReasoning'' _ _ _ _ _ $t') in
    fillWithUnderscoresAndCall0 tac tcast []
  ) in
  let t := Fresh.in_goal ident:(t) in
  Notations.specialize0 (fun () => twb) (Some (Std.IntroNaming (Std.IntroIdentifier t)));
  let t_constr := Control.hyp t in
  fillWithUnderscoresAndCall0 tac' t_constr [];
  clear $t
.

Ltac2 try_solve_pile_basic () :=
  Control.enter (fun () =>
    lazy_match! goal with
    | [ |- (@ProofInfoLe _ _ _)] =>
        try (solve
          [ apply pile_any
          | apply pile_refl
          | apply pile_basic_generic
       ])
    | [|- _] => ()
    end
  )
.

Ltac2 try_wfa () :=
  Control.enter (fun () =>
    let wfa := (fun p =>
      if (Constr.has_evar p) then
        ()
      else
        ltac1:(try_wfauto2)
    ) in
    lazy_match! goal with
    | [|- well_formed ?p = true] => wfa p
    | [|- is_true (well_formed ?p) ] => wfa p
    | [|- Pattern.wf ?l = true] => wfa l
    | [|- is_true (Pattern.wf ?l) ] => wfa l
    | [|- _] => ()
    end
  )
.

Ltac2 mutable do_mlApplyMeta := fun (twb : Std.constr_with_bindings) =>
  Control.enter (fun () =>
    _ensureProofMode;
    _callCompletedAndCast twb do_mlApplyMetaRaw ;
    try_solve_pile_basic ();
    try_wfa ()
  )
.

Ltac2 mutable do_mlApplyMetaIn := fun (twb : Std.constr_with_bindings) (name : constr) =>
  Control.enter (fun () =>
    _ensureProofMode;
    _callCompletedAndCast twb (fun t =>
      do_mlApplyMetaRawIn t name
    );
    try_solve_pile_basic ();
    try_wfa ()
  )
.

Ltac2 do_mlApplyMeta0 (twb : Std.constr_with_bindings) (cl : constr option) :=
  match cl with
  | None => do_mlApplyMeta twb
  | Some n => do_mlApplyMetaIn twb n
  end
.

Ltac2 Notation "mlApplyMeta" t(seq(constr,with_bindings)) cl(opt(seq("in", constr))) :=
  do_mlApplyMeta0 t cl
.

Ltac _mlApplyMeta t :=
  let ff := ltac2:(t' |- do_mlApplyMeta ((Option.get (Ltac1.to_constr(t'))), Std.NoBindings)) in
  ff t.

Ltac _mlApplyMetaIn t name :=
  let ff := ltac2:(t' name' |- do_mlApplyMetaIn ((Option.get (Ltac1.to_constr(t')), Std.NoBindings)) (Option.get (Ltac1.to_constr(name')))) in
  ff t name
.

Tactic Notation "mlApplyMeta" constr(t) :=
  _mlApplyMeta t.

Tactic Notation "mlApplyMeta" constr(t) "in" constr(name) :=
  _mlApplyMetaIn t name
.

Lemma MLGoal_destructAnd {Σ : Signature} Γ g l₁ l₂ nx x ny y nxy i:
    mkMLGoal Σ Γ (l₁ ++ (mkNH _ nx x)::(mkNH _ ny y)::l₂ ) g i ->
    mkMLGoal Σ Γ (l₁ ++ (mkNH _ nxy (x and y))::l₂) g i.
Proof.
  intros H.
  unfold of_MLGoal. intros wfg Hwf. pose proof (wfg' := wfg). pose proof (Hwf' := Hwf).
  revert wfg' Hwf'.
  cut (of_MLGoal (mkMLGoal Σ Γ (l₁ ++ (mkNH _ nxy (x and y))::l₂ ) g i)).
  { auto. }
  simpl in wfg, Hwf.

  mlAssert (ny : y) using first (length (l₁ ++ [mkNH _ nxy (x and y)])).

  all: unfold patterns_of in Hwf; rewrite map_app in Hwf.

  { abstract (
      apply wfapp_proj_2 in Hwf;
      unfold Pattern.wf in Hwf;
      simpl in Hwf;
      apply andb_prop in Hwf;
      destruct Hwf as [wfxy _];
      wf_auto2
    ).
  }
  {
    eapply cast_proof_ml_hyps.
    { replace (l₁ ++ (mkNH _ nxy (x and y)) :: l₂) with ((l₁ ++ [mkNH _ nxy (x and y)]) ++ l₂).
      2: { rewrite -app_assoc. reflexivity. }
      rewrite take_app.
      reflexivity.
    }
    assert (well_formed x).
    {
      abstract (
        apply wfapp_proj_2 in Hwf;
        unfold Pattern.wf in Hwf;
        simpl in Hwf;
        apply andb_prop in Hwf as [wfxy _];
        wf_auto2
      ).
    }

    mlApplyMeta pf_conj_elim_r.
    repeat rewrite length_app; simpl.
    rewrite take_app_add. simpl.
    rewrite Nat.sub_diag take_0 app_nil_r.
    apply MLGoal_exactn.
    wf_auto2.
  }

  eapply cast_proof_ml_hyps.
  {
    replace (l₁ ++ (mkNH _ nxy (x and y)) :: l₂) with ((l₁ ++ [mkNH _ nxy (x and y)]) ++ l₂).
    2: { rewrite -app_assoc. reflexivity. }
    rewrite take_app. rewrite drop_app. reflexivity.
  }

  mlAssert (nx : x) using first (length (l₁ ++ [mkNH _ nxy (x and y)])).
  { abstract (
      apply wfapp_proj_2 in Hwf;
      unfold Pattern.wf in Hwf;
      simpl in Hwf;
      apply andb_prop in Hwf;
      destruct Hwf as [wfxy _];
      wf_auto2
    ).
  }
  {
    eapply cast_proof_ml_hyps.
    {
      replace (l₁ ++ (mkNH _ nxy (x and y)) :: l₂) with ((l₁++ [mkNH _ nxy (x and y)]) ++ l₂).
      2: { rewrite -app_assoc. reflexivity. }
      rewrite take_app.
      reflexivity.
    }
    assert (well_formed x).
    {
      abstract (
        apply wfapp_proj_2 in Hwf;
        unfold Pattern.wf in Hwf;
        simpl in Hwf;
        apply andb_prop in Hwf as [wfxy _];
        wf_auto2
      ).
    }
    mlApplyMeta pf_conj_elim_l.
    repeat rewrite firstn_all.
    repeat rewrite drop_all.
    repeat rewrite Nat.sub_diag.
    repeat rewrite drop_0 take_0.
    repeat rewrite length_app; simpl in *.
    rewrite Nat.add_0_r Nat.sub_diag take_0 app_nil_r app_nil_r.
    rewrite take_app_add.
    apply MLGoal_exactn.
    wf_auto2.
  }

  eapply cast_proof_ml_hyps.
  {
    replace (l₁ ++ (mkNH _ nxy (x and y)) :: l₂) with ((l₁++ [mkNH _ nxy (x and y)]) ++ l₂).
    2: { rewrite -app_assoc. reflexivity. }
    rewrite take_app. rewrite drop_app. reflexivity.
  }

  eapply cast_proof_ml_hyps.
  {
    rewrite -app_assoc. reflexivity.
  }
  simpl.
  repeat (
  repeat rewrite length_app; simpl;
  repeat rewrite Nat.sub_diag; simpl;
  repeat rewrite take_0; simpl;
  repeat rewrite drop_0; simpl;
  repeat rewrite app_nil_r;
  repeat rewrite Nat.add_0_r;
  repeat rewrite take_app_add; simpl).
  rewrite drop_app drop_app_add. simpl.
  rewrite length_app. simpl. rewrite Nat.sub_diag. rewrite drop_0.
  rewrite drop_ge. lia. simpl.
  replace (length l₁ + 1 - length l₁) with 1 by lia. simpl.
  rewrite -app_assoc.
  apply mlGoal_clear_hyp.
  exact H.
Defined.

Ltac2 mlDestructAnd_as (name : constr) (name1 : constr) (name2 : constr) :=
  Control.enter(fun () =>
    _ensureProofMode;
    _failIfUsed $name1;
    _failIfUsed $name2;
    run_in_reshaped_by_name name (fun () =>
      Control.plus(fun () =>
        apply MLGoal_destructAnd with (nxy := $name) (nx := $name1) (ny := $name2)
      )
      (fun _ => 
        _mlReshapeHypsBack;
        throw_pm_exn_with_goal "mlDestructAnd_as: Given matching logic hypothesis is not a conjunction! ")
    )
  )
.

Ltac2 Notation "mlDestructAnd" name(constr) "as" name1(constr) name2(constr) :=
  mlDestructAnd_as name name1 name2
.

Tactic Notation "mlDestructAnd" constr(name) "as" constr(name1) constr(name2) :=
  let f := ltac2:(name name1 name2 |- mlDestructAnd_as (Option.get (Ltac1.to_constr name)) (Option.get (Ltac1.to_constr name1)) (Option.get (Ltac1.to_constr name2))) in
  f name name1 name2
.

Ltac2 do_mlDestructAnd (name : constr) :=
  Control.enter(fun () =>
    _ensureProofMode;
    let hyps := do_getHypNames () in
    let name0 := eval cbv in (fresh $hyps) in
    let name1 := eval cbv in (fresh ($name0 :: $hyps)) in
    mlDestructAnd $name as $name0 $name1
  )
.

Ltac2 Notation "mlDestructAnd" name(constr) :=
  do_mlDestructAnd name
.

Tactic Notation "mlDestructAnd" constr(name) :=
  let f := ltac2:(name |- do_mlDestructAnd (Option.get (Ltac1.to_constr name))) in
  f name
.

Local Example ex_mlDestructAnd {Σ : Signature} Γ a b p q:
  well_formed a ->
  well_formed b ->
  well_formed p ->
  well_formed q ->
  Γ ⊢i p and q ---> a and b ---> q ---> a
  using BasicReasoning.
Proof.
  intros. toMLGoal.
  { wf_auto2. }
  mlIntro "H0". mlIntro "H1". mlIntro "H2".
  mlDestructAnd "H1" as "H3" "H4".
  Fail mlDestructAnd "H1" as "H3" "H4".
  Fail mlDestructAnd "H1" as "H3'" "H4".
  Fail mlDestructAnd "H1" as "H3'" "H4'".
  Fail mlDestructAnd "H3" as "H3'" "H4'".
  mlDestructAnd "H0".
  mlExact "H3".
Defined.

 
Lemma and_of_equiv_is_equiv {Σ : Signature} Γ p q p' q' i:
  well_formed p ->
  well_formed q ->
  well_formed p' ->
  well_formed q' ->
  Γ ⊢i (p <---> p') using i ->
  Γ ⊢i (q <---> q') using i ->
  Γ ⊢i ((p and q) <---> (p' and q')) using i.
Proof.
  intros wfp wfq wfp' wfq' pep' qeq'.
  pose proof (pip' := pep'). apply pf_conj_elim_l_meta in pip'; auto.
  pose proof (p'ip := pep'). apply pf_conj_elim_r_meta in p'ip; auto.
  pose proof (qiq' := qeq'). apply pf_conj_elim_l_meta in qiq'; auto.
  pose proof (q'iq := qeq'). apply pf_conj_elim_r_meta in q'iq; auto.

  apply conj_intro_meta; auto.
  - toMLGoal.
    { wf_auto2. }
    mlIntro "H0". unfold patt_and.
    mlIntro "H1". mlApply "H0".
    mlDestructOr "H1" as "H2" "H3".
    + apply modus_tollens in pip'; auto 10.
      mlAdd pip' as "H1".
      mlLeft.
      mlApply "H1".
      mlExact "H2".
    + apply modus_tollens in qiq'; auto 10.
      mlAdd qiq' as "H1".
      mlRight.
      mlApply "H1".
      mlExact "H3".
  - toMLGoal.
    { wf_auto2. }
    mlIntro "H0". unfold patt_and.
    mlIntro "H1". mlApply "H0".
    mlDestructOr "H1" as "H2" "H3".
    + mlLeft.
      apply modus_tollens in p'ip; auto.
      mlAdd p'ip as "H1".
      mlApply "H1".
      mlExact "H2".
    + mlRight.
      apply modus_tollens in q'iq; auto.
      mlAdd q'iq as "H1".
      mlApply "H1".
      mlExact "H3".
Defined. 

Lemma or_of_equiv_is_equiv {Σ : Signature} Γ p q p' q' i:
  well_formed p ->
  well_formed q ->
  well_formed p' ->
  well_formed q' ->
  Γ ⊢i (p <---> p') using i ->
  Γ ⊢i (q <---> q') using i ->
  Γ ⊢i ((p or q) <---> (p' or q')) using i.
Proof with try_wfauto2.
  intros wfp wfq wfp' wfq' pep' qeq'.
  pose proof (pip' := pep'). apply pf_conj_elim_l_meta in pip'...
  pose proof (p'ip := pep'). apply pf_conj_elim_r_meta in p'ip...
  pose proof (qiq' := qeq'). apply pf_conj_elim_l_meta in qiq'...
  pose proof (q'iq := qeq'). apply pf_conj_elim_r_meta in q'iq...

  apply conj_intro_meta; auto.
  - toMLGoal.
    { wf_auto2. }
    mlIntro "H0".
    mlDestructOr "H0" as "H1" "H2".
    + mlLeft. fromMLGoal. assumption.
    + mlRight. fromMLGoal. assumption.
  - toMLGoal.
    { wf_auto2. }
    mlIntro "H0".
    mlDestructOr "H0" as "H1" "H2".
    + mlLeft. fromMLGoal. assumption.
    + mlRight. fromMLGoal. assumption.
Defined.


Lemma impl_iff_notp_or_q {Σ : Signature} Γ p q:
  well_formed p ->
  well_formed q ->
  Γ ⊢i ((p ---> q) <---> (! p or q))
  using BasicReasoning.
Proof.
  intros wfp wfq.
  apply conj_intro_meta; auto.
  - toMLGoal.
    { wf_auto2. }
    mlIntro "H0".
    mlAdd (A_or_notA Γ p wfp) as "H1".
    mlDestructOr "H1" as "H2" "H3".
    + mlRight.
      mlApply "H0".
      mlExact "H2".
    + mlLeft.
      mlExact "H3".
  - toMLGoal.
    { wf_auto2. }
    mlIntro "H0". mlIntro "H2". unfold patt_or.
    mlApply "H0".
    mlApplyMeta not_not_intro.
    mlExact "H2".
Defined.

Lemma p_and_notp_is_bot {Σ : Signature} Γ p:
  well_formed p ->
  Γ ⊢i (⊥ <---> p and ! p)
  using BasicReasoning.
Proof.
  intros wfp.
  apply conj_intro_meta; auto.
  - apply bot_elim; auto.
  - unfold patt_and.
    toMLGoal.
    { wf_auto2. }
    mlIntro "H0".
    mlApply "H0".
    mlAdd (A_or_notA Γ (! p) ltac:(wf_auto2)) as "H1".
    mlExact "H1".
Defined.

Ltac2 do_mlExFalso ():=
  _ensureProofMode;
  mlApplyMeta bot_elim
.

Ltac2 Notation "mlExFalso"
  := do_mlExFalso ()
.

Ltac mlExFalso :=
  ltac2:(do_mlExFalso ())
.

Ltac2 do_mlDestructBot (name' : constr) :=
  Control.enter(fun () =>
    run_in_reshaped_by_name name' (fun () =>
      mlExFalso;
      do_mlExact name'
    )
  )
.

Ltac2 Notation "mlDestructBot" name(constr) :=
  do_mlDestructBot name
.

Tactic Notation "mlDestructBot" constr(name') :=
  let f := ltac2:(name |- do_mlDestructBot (Option.get (Ltac1.to_constr name))) in
  f name'
.

Lemma weird_lemma  {Σ : Signature} Γ A B L R:
  well_formed A ->
  well_formed B ->
  well_formed L ->
  well_formed R ->
  Γ ⊢i (((L and A) ---> (B or R)) ---> (L ---> ((A ---> B) or R)))
  using BasicReasoning.
Proof.
  intros wfA wfB wfL wfR.
  toMLGoal.
  { wf_auto2. }
  mlIntro "H0". mlIntro "H1".
  mlAdd (A_or_notA Γ A wfA) as "H2".
  mlDestructOr "H2" as "H3" "H4".
  - mlAssert ("H2" : (B or R)).
    { wf_auto2. }
    { mlApply "H0".
      unfold patt_and at 2.
      mlIntro "H2".
      mlDestructOr "H2" as "H4" "H5".
      + mlApply "H4". mlExact "H1".
      + mlApply "H5". mlExact "H3".
    }
    mlDestructOr "H2" as "H4" "H5".
    + mlLeft. mlIntro "H2". mlExact "H4".
    + mlRight. mlExact "H5".
  - mlLeft.
    mlIntro "H2".
    mlAssert ("0" : ⊥). wf_auto2.
    mlApply "H4". mlExact "H2".
    Fail mlDestructBot "H1".
    mlDestructBot "0".
Defined.

Lemma weird_lemma_meta {Σ : Signature} Γ A B L R i:
  well_formed A ->
  well_formed B ->
  well_formed L ->
  well_formed R ->
  Γ ⊢i ((L and A) ---> (B or R)) using i ->
  Γ ⊢i (L ---> ((A ---> B) or R)) using i.
Proof.
  intros WFA WFB WFL WFR H.
  eapply MP.
  2: { useBasicReasoning. apply weird_lemma; assumption. }
  exact H.
Defined.

Lemma imp_trans_mixed_meta {Σ : Signature} Γ A B C D i :
  well_formed A -> well_formed B -> well_formed C -> well_formed D ->
  Γ ⊢i (C ---> A) using i ->
  Γ ⊢i (B ---> D) using i ->
  Γ ⊢i ((A ---> B) ---> C ---> D) using i.
Proof.
  intros WFA WFB WFC WFD H H0.
  epose proof (H1 := prf_weaken_conclusion Γ A B D WFA WFB WFD).
  eapply useBasicReasoning in H1.
  eapply MP in H1.
  2: { exact H0. }
  epose proof (H2 := prf_strenghten_premise Γ A C D WFA WFC WFD).
  eapply useBasicReasoning in H2.
  eapply MP in H2.
  2: { exact H. }
  epose proof (H3 := syllogism_meta _ _ _ H1 H2).
  exact H3.
  Unshelve. all: wf_auto2.
Defined.

Lemma and_weaken {Σ : Signature} A B C Γ i:
  well_formed A -> well_formed B -> well_formed C ->
  Γ ⊢i (B ---> C) using i ->
  Γ ⊢i ((A and B) ---> (A and C)) using i.
Proof.
  intros WFA WFB WFC H.
  epose proof (H0 := and_impl' Γ A B (A and C) _ _ _).
  eapply MP. 2: { useBasicReasoning. exact H0. }
  apply reorder_meta.
  1-3: wf_auto2.
  epose proof (H1 := prf_strenghten_premise Γ C B (A ---> A and C) _ _ _).
  eapply MP.
  2: eapply MP.
  3: { useBasicReasoning. exact H1. }
  2: { exact H. }
  useBasicReasoning.
  apply conj_intro2; assumption.
  Unshelve.
  all: wf_auto2.
Defined.

Lemma impl_and {Σ : Signature} Γ A B C D i: 
  well_formed A -> well_formed B -> well_formed C -> well_formed D ->
  Γ ⊢i (A ---> B) using i ->
  Γ ⊢i (C ---> D) using i ->
  Γ ⊢i (A and C) ---> (B and D) using i.
Proof.
  intros WFA WFB WFC WFD H H0.
  toMLGoal.
  { wf_auto2. }
  {
    mlAdd H as "H0".
    mlAdd H0 as "H1".
    mlIntro "H2".
    mlDestructAnd "H2" as "H3" "H4".
    mlIntro "H5".
    mlDestructOr "H5" as "H6" "H7".
    {
      mlApply "H6".
      mlApply "H0".
      mlExact "H3".
    }
    {
      mlApply "H7".
      mlApply "H1".
      mlExact "H4".
    }
  }
Defined.

Lemma and_drop {Σ : Signature} A B C Γ i:
  well_formed A -> well_formed B -> well_formed C ->
  Γ ⊢i ((A and B) ---> C) using i ->
  Γ ⊢i ((A and B) ---> (A and C)) using i.
Proof.
  intros WFA WFB WFC H.
  toMLGoal.
  { wf_auto2. }
  mlAdd H as "H0".
  mlIntro "H1".
  mlIntro "H2".
  mlDestructOr "H2" as "H3" "H4".
  {
    mlDestructAnd "H1" as "H5" "H6".
    mlApply "H3".
    mlExact "H5".
  }
  {
    mlApply "H4".
    mlApply "H0".
    mlExact "H1".
  }
Defined.


Lemma prf_equiv_of_impl_of_equiv {Σ : Signature} Γ a b a' b' i:
  well_formed a = true ->
  well_formed b = true ->
  well_formed a' = true ->
  well_formed b' = true ->
  Γ ⊢i (a <---> a') using i ->
  Γ ⊢i (b <---> b') using i ->
  Γ ⊢i (a ---> b) <---> (a' ---> b') using i.
Proof.
  intros wfa wfb wfa' wfb' Haa' Hbb'.
  unshelve(epose proof (Haa'1 := pf_conj_elim_l_meta _ _ _ _ _ _ Haa')).
  { wf_auto2. }
  { wf_auto2. }
  unshelve(epose proof (Haa'2 := pf_conj_elim_r_meta _ _ _ _ _ _ Haa')).
  { wf_auto2. }
  { wf_auto2. }
  unshelve(epose proof (Hbb'1 := pf_conj_elim_l_meta _ _ _ _ _ _ Hbb')).
  { wf_auto2. }
  { wf_auto2. }
  unshelve(epose proof (Hbb'2 := pf_conj_elim_r_meta _ _ _ _ _ _ Hbb')).
  { wf_auto2. }
  { wf_auto2. }

  apply pf_iff_equiv_trans with (B := (a ---> b')).
  1-3: wf_auto2.
    + apply conj_intro_meta.
      1-2: wf_auto2.
      * toMLGoal.
        { wf_auto2. }
        mlIntro "H0". mlIntro "H1".
        mlAdd Hbb'1 as "H2".
        mlApply "H2".
        mlApply "H0".
        mlExact "H1".
      * toMLGoal.
        { wf_auto2. }
        mlIntro "H0". mlIntro "H1".
        mlAdd Hbb'2 as "H2".
        mlApply "H2".
        mlApply "H0".
        mlExact "H1".
    + apply conj_intro_meta.
      1-2: wf_auto2.
      * toMLGoal.
        { wf_auto2. }
        mlIntro "H0". mlIntro "H1".
        mlAdd Haa'2 as "H2".
        mlApply "H0".
        mlApply "H2".
        mlExact "H1".
      * toMLGoal.
        { wf_auto2. }
        mlIntro "H0". mlIntro "H1".
        mlAdd Haa'1 as "H2".
        mlApply "H0".
        mlApply "H2".
        mlExact "H1".
Defined.



Lemma lhs_to_and {Σ : Signature} Γ a b c i:
  well_formed a ->
  well_formed b ->
  well_formed c ->
  Γ ⊢i (a and b) ---> c using i ->
  Γ ⊢i a ---> b ---> c using i.
Proof.
  intros wfa wfb wfc H.
  toMLGoal.
  { wf_auto2. }
  mlIntro "H0". mlIntro "H1".
  mlApplyMeta H.
  fromMLGoal.
  useBasicReasoning.
  apply conj_intro.
  { wf_auto2. }
  { wf_auto2. }
Defined.

Lemma lhs_from_and {Σ : Signature} Γ a b c i:
  well_formed a ->
  well_formed b ->
  well_formed c ->
  Γ ⊢i a ---> b ---> c using i ->
  Γ ⊢i (a and b) ---> c using i.
Proof.
  intros wfa wfb wfc H.
  toMLGoal.
  { wf_auto2. }
  mlIntro "H0".
  mlAssert ("H1" : b).
  { wf_auto2. }
  { fromMLGoal. useBasicReasoning. apply pf_conj_elim_r.
    wf_auto2. wf_auto2.
  }
  mlAssert ("H2" : a) using first 1.
  { wf_auto2. }
  { fromMLGoal. useBasicReasoning. apply pf_conj_elim_l; wf_auto2. }
  mlAdd H as "H3".
  mlAssert ("H4" : (b ---> c)).
  { wf_auto2. }
  { mlApply "H3". mlExact "H2". }
  mlApply "H4".
  mlExact "H1".
Defined.

Lemma prf_conj_split {Σ : Signature} Γ a b l:
  well_formed a ->
  well_formed b ->
  Pattern.wf l ->
  Γ ⊢i (foldr patt_imp a l) ---> (foldr patt_imp b l) ---> (foldr patt_imp (a and b) l)
  using BasicReasoning.
Proof.
  intros wfa wfb wfl.
  induction l.
  - simpl. apply conj_intro; assumption.
  - simpl. pose proof (wfl' := wfl). unfold Pattern.wf in wfl'. simpl in wfl'. apply andb_prop in wfl' as [wfa0 wfl'].
    specialize (IHl wfl').
    toMLGoal.
    { wf_auto2. }
    mlIntro "H0". mlIntro "H1". mlIntro "H2".
    mlAssert ("H3" : (foldr patt_imp a l)).
    { wf_auto2. }
    { mlApply "H0". mlExact "H2". }
    mlAssert ("H4" : (foldr patt_imp b l)).
    { wf_auto2. }
    { mlApply "H1". mlExact "H2". }
    mlClear "H2". mlClear "H1". mlClear "H0".
    fromMLGoal. apply IHl.
Defined.

Lemma prf_conj_split_meta {Σ : Signature} Γ a b l (i : ProofInfo):
  well_formed a ->
  well_formed b ->
  Pattern.wf l ->
  Γ ⊢i (foldr patt_imp a l) using i -> 
  Γ ⊢i (foldr patt_imp b l) ---> (foldr patt_imp (a and b) l) using i.
Proof.
  intros. eapply MP. 2: { useBasicReasoning. apply prf_conj_split; assumption. }
  exact H2.
Defined.

Lemma prf_conj_split_meta_meta {Σ : Signature} Γ a b l (i : ProofInfo):
  well_formed a ->
  well_formed b ->
  Pattern.wf l ->
  Γ ⊢i (foldr patt_imp a l) using i -> 
  Γ ⊢i (foldr patt_imp b l) using i ->
  Γ ⊢i (foldr patt_imp (a and b) l) using i.
Proof.
  intros. eapply MP.
  2: {
    apply prf_conj_split_meta; assumption.
  }
  exact H3.
Defined.

Lemma MLGoal_splitAnd {Σ : Signature} Γ a b l i:
  mkMLGoal Σ Γ l a i ->
  mkMLGoal Σ Γ l b i ->
  mkMLGoal Σ Γ l (a and b) i.
Proof.
  intros Ha Hb.
  unfold of_MLGoal in *. simpl in *.
  intros wfab wfl.
  ospecialize* Ha.
  { abstract(wf_auto2). }
  { exact wfl. }
  ospecialize* Hb.
  { abstract(wf_auto2). }
  { exact wfl. }
  apply prf_conj_split_meta_meta; auto.
  { abstract (wf_auto2). }
  { abstract (wf_auto2). }
Defined.

Ltac2 do_mlSplitAnd () :=
  Control.enter(fun () =>
    _ensureProofMode;
    Control.plus(fun () =>
      apply MLGoal_splitAnd
    )
    (fun _ => throw_pm_exn_with_goal "do_mlSplitAnd: matching logic goal is not a conjunction! ")
  )
.

Ltac2 Notation "mlSplitAnd" :=
  do_mlSplitAnd ()
.

Ltac mlSplitAnd :=
  ltac2:(do_mlSplitAnd ())
.

Local Lemma ex_mlSplitAnd {Σ : Signature} Γ a b c:
  well_formed a ->
  well_formed b ->
  well_formed c ->
  Γ ⊢i a ---> b ---> c ---> (a and b)
  using BasicReasoning.
Proof.
  intros wfa wfb wfc.
  toMLGoal.
  { wf_auto2. }
  mlIntro "H0". mlIntro "H1".
  Fail mlSplitAnd.
  mlIntro "H2".
  mlSplitAnd.
  - mlExact "H0".
  - mlExact "H1".
Defined.

Lemma prf_local_goals_equiv_impl_full_equiv {Σ : Signature} Γ g₁ g₂ l:
  well_formed g₁ ->
  well_formed g₂ ->
  Pattern.wf l ->
  Γ ⊢i (foldr patt_imp (g₁ <---> g₂) l) --->
      ((foldr patt_imp g₁ l) <---> (foldr patt_imp g₂ l))
  using BasicReasoning.
Proof.
  intros wfg₁ wfg₂ wfl.
  induction l; simpl.
  - apply A_impl_A; wf_auto2.
  - pose proof (wfl' := wfl). unfold Pattern.wf in wfl'. simpl in wfl'. apply andb_prop in wfl' as [wfa wfl'].
    specialize (IHl wfl').
    toMLGoal.
    { wf_auto2. }
    mlIntro "H0". mlSplitAnd.
    + mlApplyMeta P2.
      mlRevertLast.
      mlApplyMeta P2.
      mlIntro "H0". mlClear "H0". mlIntro "H0".
      mlApplyMeta IHl in "H0".
      unfold patt_iff at 1. mlDestructAnd "H0" as "H1" "H2".
      mlExact "H1".
    + mlApplyMeta P2.
      mlRevertLast.
      mlApplyMeta P2.
      mlIntro "H0". mlClear "H0". mlIntro "H0".
      mlApplyMeta IHl in "H0".
      unfold patt_iff at 1. mlDestructAnd "H0" as "H1" "H2".
      mlExact "H2".
Defined.

Lemma prf_local_goals_equiv_impl_full_equiv_meta {Σ : Signature} Γ g₁ g₂ l i:
  well_formed g₁ ->
  well_formed g₂ ->
  Pattern.wf l ->
  Γ ⊢i (foldr patt_imp (g₁ <---> g₂) l) using i ->
  Γ ⊢i ((foldr patt_imp g₁ l) <---> (foldr patt_imp g₂ l)) using i.
Proof.
  intros wfg₁ wfg₂ wfl H.
  eapply MP.
  2: { useBasicReasoning. apply prf_local_goals_equiv_impl_full_equiv; assumption. }
  exact H.
Defined.

Lemma prf_local_goals_equiv_impl_full_equiv_meta_proj1 {Σ : Signature} Γ g₁ g₂ l i:
  well_formed g₁ ->
  well_formed g₂ ->
  Pattern.wf l ->
  Γ ⊢i (foldr patt_imp (g₁ <---> g₂) l) using i ->
  Γ ⊢i (foldr patt_imp g₁ l) using i ->
  Γ ⊢i (foldr patt_imp g₂ l) using i.
Proof.
  intros wfg₁ wfg₂ wfl H1 H2.
  eapply MP.
  2: eapply pf_iff_proj1.
  4: apply prf_local_goals_equiv_impl_full_equiv_meta.
  7: apply H1.
  1: exact H2.
  all: wf_auto2.
Defined.

Lemma prf_local_goals_equiv_impl_full_equiv_meta_proj2 {Σ : Signature} Γ g₁ g₂ l i:
  well_formed g₁ ->
  well_formed g₂ ->
  Pattern.wf l ->
  Γ ⊢i (foldr patt_imp (g₁ <---> g₂) l) using i ->
  Γ ⊢i (foldr patt_imp g₂ l) using i ->
  Γ ⊢i (foldr patt_imp g₁ l) using i.
Proof.
  intros wfg₁ wfg₂ wfl H1 H2.
  eapply MP.
  2: eapply pf_iff_proj2.
  4: apply prf_local_goals_equiv_impl_full_equiv_meta.
  7: apply H1.
  1: exact H2.
  all: wf_auto2.
Defined.



Lemma top_holds {Σ : Signature} Γ:
  Γ ⊢i Top using BasicReasoning.
Proof.
  apply bot_elim.
  { wf_auto2. }
Defined.

Lemma phi_iff_phi_top {Σ : Signature} Γ ϕ :
  well_formed ϕ ->
  Γ ⊢i ϕ <---> (ϕ <---> Top)
  using BasicReasoning.
Proof.
  intros wfϕ.
  toMLGoal.
  { wf_auto2. }
  mlSplitAnd; mlIntro "H0".
  - mlSplitAnd.
    + mlIntro "H1". mlClear "H1". mlClear "H0".
      fromMLGoal.
      apply top_holds. (* TODO: we need something like [mlExactMeta top_holds] *)
    + fromMLGoal.
      apply P1; wf_auto2.
  - mlDestructAnd "H0" as "H1" "H2".
    mlApply "H2".
    mlClear "H2".
    mlClear "H1".
    fromMLGoal.
    apply top_holds.
Defined.

Lemma not_phi_iff_phi_bott {Σ : Signature} Γ ϕ :
  well_formed ϕ ->
  Γ ⊢i (! ϕ ) <---> (ϕ <---> ⊥)
  using BasicReasoning.
Proof.
  intros wfϕ.
  toMLGoal.
  { wf_auto2. }
  mlSplitAnd; mlIntro "H0".
  - mlSplitAnd.
    + mlExact "H0".
    + mlClear "H0". fromMLGoal.
      apply bot_elim.
      { wf_auto2. }
  - mlDestructAnd "H0" as "H1" "H2".
    mlExact "H1".
Defined.

Lemma not_not_iff {Σ : Signature} (Γ : Theory) (A : Pattern) :
  well_formed A ->
  Γ ⊢i A <---> ! ! A
  using BasicReasoning.
Proof.
  intros wfA.
  apply pf_iff_split.
  { wf_auto2. }
  { wf_auto2. }
  - apply not_not_intro.
    { wf_auto2. }
  - apply not_not_elim.
    { wf_auto2. }
Defined.


Lemma patt_and_comm {Σ : Signature} Γ p q:
  well_formed p ->
  well_formed q ->
  Γ ⊢i (p and q) <---> (q and p)
  using BasicReasoning.
Proof.
  intros wfp wfq.
  toMLGoal.
  { wf_auto2. }
  mlSplitAnd; mlIntro "H0"; mlDestructAnd "H0" as "H1" "H2"; mlSplitAnd.
  - mlExact "H2".
  - mlExact "H1".
  - mlExact "H2".
  - mlExact "H1".
Defined.



(* We need to come up with tactics that make this easier. *)
Local Example ex_mt {Σ : Signature} Γ ϕ₁ ϕ₂:
  well_formed ϕ₁ ->
  well_formed ϕ₂ ->
  Γ ⊢i (! ϕ₁ ---> ! ϕ₂) ---> (ϕ₂ ---> ϕ₁)
  using BasicReasoning.
Proof.
  intros wfϕ₁ wfϕ₂.
  toMLGoal.
  { wf_auto2. }
  mlIntro "H0". mlIntro "H1".
  unfold patt_not.
  mlAssert ("H2" : ((ϕ₁ ---> ⊥) ---> ⊥)).
  { wf_auto2. }
  { mlIntro "H2".
    mlAssert ("H3" : (ϕ₂ ---> ⊥)).
    { wf_auto2. }
    { mlApply "H0". mlExact "H2". }
    mlApply "H3".
    mlExact "H1".
  }
  mlApplyMeta not_not_elim.
  mlExact "H2".
Defined.

Lemma lhs_and_to_imp {Σ : Signature} Γ (g x : Pattern) (xs : list Pattern):
  well_formed g ->
  well_formed x ->
  Pattern.wf xs ->
  Γ ⊢i (foldr patt_and x xs ---> g) ---> (foldr patt_imp g (x :: xs))
  using BasicReasoning.
Proof.
  intros wfg wfx wfxs.
  induction xs; simpl.
  - apply A_impl_A.
    { wf_auto2. }
  - pose proof (wfaxs := wfxs).
    unfold Pattern.wf in wfxs.
    simpl in wfxs.
    apply andb_prop in wfxs as [wfa wfxs].
    fold (Pattern.wf xs) in wfxs.
    specialize (IHxs wfxs).
    simpl in IHxs.
    assert (Hwffa: well_formed (foldr patt_and x xs)).
    { apply well_formed_foldr_and; assumption. }
    toMLGoal.
    { wf_auto2. }
    mlIntro "H0". mlIntro "H1". mlIntro "H2".
    mlAdd IHxs as "H3".
    mlAssert ("H4" : ((foldr patt_and x xs ---> g) ---> foldr patt_imp g xs)).
    { wf_auto2. }
    { mlIntro "H5".
      mlAssert ("H6" : (x ---> foldr patt_imp g xs)).
      { wf_auto2. }
      { mlApply "H3". mlExact "H5". }
      mlClear "H0".
      mlApply "H6".
      mlExact "H1".
    }
    mlClear "H3".
    mlApply "H4".
    mlClear "H4".
    mlIntro "H3".
    mlApply "H0".
    mlSplitAnd.
    + mlExact "H2".
    + mlExact "H3".
Defined.

Lemma lhs_and_to_imp_meta {Σ : Signature} Γ (g x : Pattern) (xs : list Pattern) i:
  well_formed g ->
  well_formed x ->
  Pattern.wf xs ->
  Γ ⊢i (foldr patt_and x xs ---> g) using i ->
  Γ ⊢i (foldr patt_imp g (x :: xs)) using i.
Proof.
  intros wfg wfx wfxs H.
  eapply MP.
  2: { useBasicReasoning. apply lhs_and_to_imp; assumption. }
  exact H.
Defined.

Lemma lhs_imp_to_and {Σ : Signature} Γ (g x : Pattern) (xs : list Pattern):
  well_formed g ->
  well_formed x ->
  Pattern.wf xs ->
  Γ ⊢i (foldr patt_imp g (x :: xs)) ---> (foldr patt_and x xs ---> g)
  using BasicReasoning.
Proof.
  intros wfg wfx wfxs.
  induction xs; simpl.
  {
    apply A_impl_A.
    wf_auto2.
  }
  {
    pose proof (wfaxs := wfxs).
    unfold Pattern.wf in wfxs.
    simpl in wfxs.
    apply andb_prop in wfxs as [wfa wfxs].
    fold (Pattern.wf xs) in wfxs.
    specialize (IHxs wfxs).
    simpl in IHxs.
    assert (Hwffa: well_formed (foldr patt_and x xs)).
    { apply well_formed_foldr_and; assumption. }
    toMLGoal.
    { wf_auto2. }
    mlAdd IHxs as "H".
    mlIntro "H1".
    mlIntro "H2".
    mlDestructAnd "H2" as "H3" "H4".
    mlApplyMeta reorder in "H1".
    mlAssert ("H5": (x ---> foldr patt_imp g xs)).
    { wf_auto2. }
    {
      mlApply "H1".
      mlExact "H3".  
    }
    mlAssert ("H6" : (foldr patt_and x xs ---> g)).
    { wf_auto2. }
    {
      mlApply "H".
      mlExact "H5".
    }
    mlApply "H6".
    mlExact "H4".
  }
Defined.


Lemma lhs_imp_to_and_meta {Σ : Signature} Γ (g x : Pattern) (xs : list Pattern) i:
  well_formed g ->
  well_formed x ->
  Pattern.wf xs ->
  Γ ⊢i (foldr patt_imp g (x :: xs)) using i ->
  Γ ⊢i (foldr patt_and x xs ---> g) using i.
Proof.
  intros wfg wfx wfxs H.
  eapply MP.
  2: { useBasicReasoning. apply lhs_imp_to_and; assumption. }
  exact H.
Defined.

Lemma foldr_and_impl_last {Σ : Signature} Γ (x : Pattern) (xs : list Pattern):
  well_formed x ->
  Pattern.wf xs ->
  Γ ⊢i (foldr patt_and x xs ---> x) using BasicReasoning.
Proof.
  intros wfx wfxs.
  induction xs; simpl.
  {
    apply A_impl_A.
    exact wfx.
  }
  {
    pose proof (wfaxs := wfxs).
    unfold Pattern.wf in wfxs.
    simpl in wfxs.
    apply andb_prop in wfxs as [wfa wfxs].
    fold (Pattern.wf xs) in wfxs.
    specialize (IHxs wfxs).
    assert (Hwf2: well_formed (foldr patt_and x xs)).
    { apply well_formed_foldr_and; assumption. }
    toMLGoal.
    { wf_auto2. }
    mlAdd IHxs as "IH".
    mlIntro "H".
    mlDestructAnd "H" as "Ha" "Hf".
    mlApply "IH".
    mlExact "Hf".
  }
Defined.

Lemma foldr_and_weaken_last {Σ : Signature} Γ (x y : Pattern) (xs : list Pattern):
  well_formed x ->
  well_formed y ->
  Pattern.wf xs ->
  Γ ⊢i (x ---> y) ---> (foldr patt_and x xs ---> foldr patt_and y xs) using BasicReasoning.
Proof.
  intros wfx wfy wfxs.
  induction xs; simpl.
  {
    apply A_impl_A.
    wf_auto2.
  }
  {
    pose proof (wfaxs := wfxs).
    unfold Pattern.wf in wfxs.
    simpl in wfxs.
    apply andb_prop in wfxs as [wfa wfxs].
    fold (Pattern.wf xs) in wfxs.
    assert (Hwf1: well_formed (foldr patt_and x xs)).
    { apply well_formed_foldr_and; assumption. }
    assert (Hwf2: well_formed (foldr patt_and y xs)).
    { apply well_formed_foldr_and; assumption. }
    specialize (IHxs wfxs).
    toMLGoal.
    {
      wf_auto2.
    }
    mlAdd IHxs as "IH".
    mlIntro "H1".
    mlIntro "H2".
    mlDestructAnd "H2" as "H3" "H4".
    mlSplitAnd;[mlExact "H3"|].
    mlAssert ("IH'": (foldr patt_and x xs ---> foldr patt_and y xs)).
    {
      wf_auto2.
    }
    {
      mlApply "IH".
      mlExact "H1".
    }
    mlApply "IH'".
    mlExact "H4".
  }
Defined.

Lemma foldr_and_weaken_last_meta {Σ : Signature} Γ (x y : Pattern) (xs : list Pattern) i:
  well_formed x ->
  well_formed y ->
  Pattern.wf xs ->
  Γ ⊢i (x ---> y) using i ->
  Γ ⊢i (foldr patt_and x xs ---> foldr patt_and y xs) using i.
Proof.
  intros wfx wfy wfxs H.
  eapply MP;[exact H|].
  useBasicReasoning.
  apply foldr_and_weaken_last; assumption.
Defined.

Lemma foldr_and_last_rotate {Σ : Signature} Γ (x1 x2 : Pattern) (xs : list Pattern):
  well_formed x1 ->
  well_formed x2 ->
  Pattern.wf xs ->
  Γ ⊢i ((foldr patt_and x2 (xs ++ [x1])) <---> (x2 and (foldr patt_and x1 xs))) using BasicReasoning.
Proof.
  intros wfx1 wfx2 wfxs.
  destruct xs; simpl.
  {
    apply patt_and_comm; assumption.
  }
  {
    pose proof (wfaxs := wfxs).
    unfold Pattern.wf in wfxs.
    simpl in wfxs.
    apply andb_prop in wfxs as [wfa wfxs].
    fold (Pattern.wf xs) in wfxs.

    assert (Hwf1: well_formed (foldr patt_and (x1 and x2) xs)).
    { apply well_formed_foldr_and;[wf_auto2|assumption]. }
    assert (Hwf2: well_formed (foldr patt_and x1 xs)).
    { apply well_formed_foldr_and; assumption. }
    assert (Hwf3: well_formed (foldr patt_and x2 xs)).
    { apply well_formed_foldr_and; assumption. }

    rewrite foldr_app. simpl. 
    toMLGoal.
    { wf_auto2. }
    mlSplitAnd; mlIntro "H".
    {
      mlDestructAnd "H" as "Ha" "Hf".
      repeat mlSplitAnd.
      { mlApplyMeta foldr_and_impl_last in "Hf".
        mlDestructAnd "Hf" as "Hx1" "Hx2".
        mlExact "Hx2".
      }
      { mlExact "Ha". }
      {
        mlApplyMeta foldr_and_weaken_last_meta in "Hf".
        2: { apply pf_conj_elim_l; wf_auto2. }
        2: wf_auto2.
        mlExact "Hf".
      }
    }
    {
      mlDestructAnd "H" as "H1" "H1'".
      mlDestructAnd "H1'" as "H2" "H3".
      mlSplitAnd;[mlExact "H2"|].
      mlAssert ("Hf": (x2 and foldr patt_and x1 xs)).
      { wf_auto2. }
      { mlSplitAnd;[mlExact "H1"|mlExact "H3"]. }
      mlAdd (foldr_and_weaken_last Γ x1 (x1 and x2) xs ltac:(wf_auto2) ltac:(wf_auto2) ltac:(wf_auto2))as "Hw".
      mlAssert ("Hw'" : (foldr patt_and x1 xs ---> foldr patt_and (x1 and x2) xs)).
      { wf_auto2. }
      {
        mlApply "Hw".
        mlIntro "Hx1".
        mlSplitAnd;[mlExact "Hx1"|mlExact "H1"].
      }
      mlApply "Hw'".
      mlExact "H3".
    }
  }
Defined.

Lemma foldr_and_last_rotate_1 {Σ : Signature} Γ (x1 x2 : Pattern) (xs : list Pattern):
  well_formed x1 ->
  well_formed x2 ->
  Pattern.wf xs ->
  Γ ⊢i ((foldr patt_and x2 (xs ++ [x1])) ---> (x2 and (foldr patt_and x1 xs))) using BasicReasoning.
Proof.
  intros.
  assert (well_formed (foldr patt_and (x1 and x2) xs)).
  { apply well_formed_foldr_and; wf_auto2. }
  assert (well_formed (foldr patt_and x1 xs)).
  { apply well_formed_foldr_and; wf_auto2. }
  eapply pf_iff_proj1.
  3: { apply foldr_and_last_rotate; assumption. }
  {
    rewrite foldr_app. simpl. wf_auto2.
  }
  apply well_formed_and; wf_auto2.
Defined.

Lemma foldr_and_last_rotate_2 {Σ : Signature} Γ (x1 x2 : Pattern) (xs : list Pattern):
  well_formed x1 ->
  well_formed x2 ->
  Pattern.wf xs ->
  Γ ⊢i ((x2 and (foldr patt_and x1 xs)) ---> ((foldr patt_and x2 (xs ++ [x1])))) using BasicReasoning.
Proof.
  intros.
  assert (well_formed (foldr patt_and (x1 and x2) xs)).
  { apply well_formed_foldr_and; wf_auto2. }
  assert (well_formed (foldr patt_and x1 xs)).
  { apply well_formed_foldr_and; wf_auto2. }
  eapply pf_iff_proj2.
  3: { apply foldr_and_last_rotate; assumption. }
  {
    rewrite foldr_app. simpl. wf_auto2.
  }
  apply well_formed_and; wf_auto2.
Defined.

#[local]
Ltac2 rec tryExact (l : constr) (idx : constr) :=
  lazy_match! l with
    | nil => throw_pm_exn_with_goal "tryExact: there was no matching logic hypothesis which is exactly matched by the goal: "
    | (_ :: ?m) => Control.plus (fun () => do_mlExactn idx) (fun _ => tryExact m constr:($idx + 1))
  end.

#[global]
Ltac2 do_mlAssumption () :=
  Control.enter(fun () =>
    _ensureProofMode;
    lazy_match! goal with
      | [ |- @of_MLGoal _ (@mkMLGoal _ _ ?l _ _) ] 
        =>
          tryExact l constr:(0)
    end
  )
.

Ltac2 Notation "mlAssumption" :=
  do_mlAssumption ()
.

Tactic Notation "mlAssumption" :=
  ltac2:(do_mlAssumption ())
.

Lemma impl_eq_or {Σ : Signature} Γ a b:
  well_formed a ->
  well_formed b ->
  Γ ⊢i ( (a ---> b) <---> ((! a) or b) )
  using BasicReasoning.
Proof.
  intros wfa wfb.
  toMLGoal.
  { wf_auto2. }
  mlIntro "H0".
  mlDestructOr "H0" as "H1" "H2".
  - mlApply "H1". mlIntro "H2". mlClear "H1". mlIntro "H1".
    mlApplyMeta not_not_elim in "H1".
    mlApply "H2". mlAssumption.
  - mlApply "H2". mlIntro "H0". mlClear "H2". mlIntro "H1".
    mlDestructOr "H0" as "H2" "H3".
    + mlExFalso. Fail mlAssumption.
      mlApply "H2". mlAssumption.
    + mlAssumption.
Defined.


Lemma nimpl_eq_and {Σ : Signature} Γ a b:
  well_formed a ->
  well_formed b ->
  Γ ⊢i ( ! (a ---> b) <---> (a and !b) )
  using BasicReasoning.
Proof.
  intros wfa wfb.
  toMLGoal.
  { wf_auto2. }
  mlIntro "H0".
  mlDestructOr "H0" as "H1" "H2".
  - mlApply "H1". mlIntro "H0".
    unfold patt_and. mlIntro "H2".
    mlApply "H0". mlIntro "H3".
    mlDestructOr "H2" as "H4" "H5".
    + mlExFalso.
      mlApply "H4". mlAssumption.
    + mlApplyMeta not_not_elim in "H5".
      mlAssumption.
  - mlApply "H2". mlIntro "H0". mlIntro "H1".
    mlDestructAnd "H0" as "H3" "H4". mlApply "H4". mlApply "H1".
    mlAssumption.
Defined.

Lemma deMorgan_nand_1 {Σ : Signature} Γ a b:
    well_formed a ->
    well_formed b ->
    Γ ⊢i ( !(a and b) ---> (!a or !b) )
    using BasicReasoning.
Proof.
  intros wfa wfb.
  mlIntro "H".
  mlIntro "H0".
  mlIntro "H1".
  mlApply "H".
  mlSplitAnd. 2: mlAssumption.
  mlApplyMeta not_not_elim in "H0".
  mlAssumption.
Defined.

Lemma deMorgan_nand_2 {Σ : Signature} Γ a b:
    well_formed a ->
    well_formed b ->
    Γ ⊢i ( (!a or !b) ---> !(a and b) )
    using BasicReasoning.
Proof.
  intros wfa wfb.
  mlIntro "H".
  mlIntro "H0".
  mlDestructAnd "H0".
  mlDestructOr "H" as "H1" "H1"; mlApply "H1"; mlAssumption.
Defined.

Lemma deMorgan_nand {Σ : Signature} Γ a b:
    well_formed a ->
    well_formed b ->
    Γ ⊢i ( !(a and b) <---> (!a or !b) )
    using BasicReasoning.
Proof.
  intros wfa wfb.
  mlSplitAnd.
  * mlIntro "H". mlApplyMeta deMorgan_nand_1. mlAssumption.
  * mlIntro "H". mlApplyMeta deMorgan_nand_2. mlAssumption.
Defined.

Lemma deMorgan_nor_1 {Σ : Signature} Γ a b:
    well_formed a ->
    well_formed b ->
    Γ ⊢i ( !(a or b) ---> (!a and !b))
    using BasicReasoning.
Proof.
  intros wfa wfb.
  mlIntro "H".
  mlSplitAnd; mlIntro "H0"; mlApply "H".
  * mlLeft. mlAssumption.
  * mlRight. mlAssumption.
Defined.

Lemma deMorgan_nor_2 {Σ : Signature} Γ a b:
    well_formed a ->
    well_formed b ->
    Γ ⊢i ( (!a and !b) ---> !(a or b))
    using BasicReasoning.
Proof.
  intros wfa wfb.
  mlIntro "H".
  mlIntro "H0".
  mlDestructAnd "H" as "H1" "H2".
  mlDestructOr "H0" as "H" "H".
  * mlApply "H1". mlAssumption.
  * mlApply "H2". mlAssumption.
Defined.

Lemma deMorgan_nor {Σ : Signature} Γ a b:
    well_formed a ->
    well_formed b ->
    Γ ⊢i ( !(a or b) <---> (!a and !b))
    using BasicReasoning.
Proof.
  intros wfa wfb.
  mlSplitAnd.
  * mlIntro "H". mlApplyMeta deMorgan_nor_1. mlAssumption.
  * mlIntro "H". mlApplyMeta deMorgan_nor_2. mlAssumption.
Defined.

Lemma not_not_eq {Σ : Signature} (Γ : Theory) (a : Pattern) :
  well_formed a ->
  Γ ⊢i (!(!a) <---> a)
  using BasicReasoning.
Proof.
  intros wfa.
  toMLGoal.
  { wf_auto2. }
  mlIntro "H0".
  mlDestructOr "H0" as "H1" "H2".
  - mlApply "H1". mlIntro "H0".
    mlApplyMeta not_not_elim in "H0".
    mlAssumption.
  - unfold patt_not. mlApply "H2". mlIntro "H0". mlIntro "H1".
    mlApply "H1". mlAssumption.
Defined.


Lemma and_singleton {Σ : Signature} : forall Γ p,
  well_formed p -> Γ ⊢i (p and p) <---> p using BasicReasoning.
Proof.
  intros Γ p WFp.
  toMLGoal. wf_auto2.
  mlSplitAnd; mlIntro "H".
  * mlDestructAnd "H". mlAssumption.
  * mlSplitAnd; mlAssumption.
Defined.

Lemma bott_and {Σ : Signature} Γ ϕ :
  well_formed ϕ ->
  Γ ⊢ ⊥ and ϕ <---> ⊥.
Proof.
  intro wfϕ.
  toMLGoal.
  { wf_auto2. }
  mlSplitAnd.
  + mlIntro "H". mlDestructAnd "H" as "B" "P". mlExact "B".
  + mlIntro "H". mlExFalso. mlExact "H".
Defined.

Lemma top_and {Σ : Signature} Γ ϕ :
  well_formed ϕ ->
  Γ ⊢ Top and ϕ <---> ϕ.
Proof.
  intro wfϕ.
  toMLGoal.
  { wf_auto2. }
  mlSplitAnd.
  + mlIntro "H". mlDestructAnd "H" as "T" "P". mlExact "P".
  + mlIntro "H".
    mlSplitAnd.
    * mlClear "H". fromMLGoal. aapply top_holds.
    * mlExact "H".
Defined.

Lemma MLGoal_ExactMeta {Σ:Signature} : forall Γ l g i,
  Γ ⊢i g using i ->
  mkMLGoal Σ Γ l g i.
Proof.
  intros Γ l g i pf wfG wfl.
  unfold of_MLGoal. simpl in *.
  induction l; simpl; auto.
  simpl in wfl. apply wf_tail' in wfl as wfl'.
  cbn in wfl. apply andb_true_iff in wfl as [wfl _].
  apply prf_conclusion; try solve [wf_auto2].
  auto with nocore.
Defined.

Tactic Notation "mlExactMeta" uconstr(t) :=
  _ensureProofMode;
  apply (@MLGoal_ExactMeta _ _ _ _ _ t).

Goal forall (Σ : Signature) Γ, Γ ⊢i Top using BasicReasoning.
Proof.
  intros. toMLGoal. wf_auto2.
  mlExactMeta (top_holds Γ).
Defined.

Local Example exfalso_test {Σ : Signature} p Γ i :
  well_formed p ->
  Γ ⊢i p and ! p ---> Top using i.
Proof.
  intro WF. toMLGoal.
  { wf_auto2. }
  mlIntro "H".
  mlDestructAnd "H" as "H0" "H1".
  mlExFalso.
  mlApply "H1".
  mlExact "H0".
Defined.

Local Example destruct_bot_test {Σ : Signature} p Γ i :
  well_formed p ->
  Γ ⊢i ⊥ ---> Top using i.
Proof.
  intro WF. toMLGoal.
  { wf_auto2. }
  mlIntro "H".
  mlDestructBot "H".
Defined.


Lemma extract_common_from_equivalence
  {Σ : Signature} (Γ : Theory) (a b c : Pattern):
  well_formed a ->
  well_formed b ->
  well_formed c ->
  Γ ⊢i (((a and b) <---> (a and c)) <---> (a ---> (b <---> c))) 
  using BasicReasoning
.
Proof.
  intros wfa wfb wfc.
  toMLGoal;[wf_auto2|].
  mlSplitAnd; mlIntro "H".
  {
    mlIntro "Ha".
    mlDestructAnd "H" as "H1" "H2".
    mlSplitAnd; mlIntro "H3".
    {
      mlAssert ("Htmp": ((a and c) ---> c)).
      { wf_auto2. }
      {
        mlIntro "H'".
        mlDestructAnd "H'" as "H'1" "H'2".
        mlExact "H'2".
      }
      mlApply "Htmp".
      mlApply "H1".
      mlSplitAnd; mlAssumption.
    }
    {
      mlAssert ("Htmp": ((a and b) ---> b)).
      { wf_auto2. }
      {
        mlIntro "H'".
        mlDestructAnd "H'" as "H'1" "H'2".
        mlExact "H'2".
      }
      mlApply "Htmp".
      mlApply "H2".
      mlSplitAnd; mlAssumption.
    }
  }
  {
    mlSplitAnd; mlIntro "H'"; mlDestructAnd "H'" as "H'1" "H'2".
    {
      mlSplitAnd. mlExact "H'1".
      mlAssert ("Htmp": (b <---> c)).
      { wf_auto2. }
      {
        mlApply "H". mlExact "H'1".
      }
      mlDestructAnd "Htmp" as "Htmp1" "Htmp2".
      mlApply "Htmp1". mlExact "H'2".
    }
    {
      mlSplitAnd. mlExact "H'1".
      mlAssert ("Htmp": (b <---> c)).
      { wf_auto2. }
      {
        mlApply "H". mlExact "H'1".
      }
      mlDestructAnd "Htmp" as "Htmp1" "Htmp2".
      mlApply "Htmp2". mlExact "H'2".
    }
  }
Defined.

Lemma extract_common_from_equivalence_1
  {Σ : Signature} (Γ : Theory) (a b c : Pattern):
  well_formed a ->
  well_formed b ->
  well_formed c ->
  Γ ⊢i ((a ---> (b <---> c)) ---> ((a and b) <---> (a and c))) 
  using BasicReasoning
.
Proof.
  intros.
  eapply pf_conj_elim_r_meta.
  3: apply extract_common_from_equivalence.
  all: wf_auto2.
Defined.


Lemma extract_common_from_equivalence_2
  {Σ : Signature} (Γ : Theory) (a b c : Pattern):
  well_formed a ->
  well_formed b ->
  well_formed c ->
  Γ ⊢i (((a and b) <---> (a and c)) ---> (a ---> (b <---> c))) 
  using BasicReasoning
.
Proof.
  intros.
  eapply pf_conj_elim_l_meta.
  3: apply extract_common_from_equivalence.
  all: wf_auto2.
Defined.


Ltac2 do_mlClassic_as (p : constr) (n1 : constr) (n2 : constr) :=
  Control.enter(fun () => 
    _ensureProofMode;
    let hyps := do_getHypNames () in
    let tmpName := eval cbv in (fresh $hyps) in
    let wfName := Fresh.in_goal ident:(Hwf) in
    lazy_match! goal with
    | [|- @of_MLGoal _ (@mkMLGoal _ ?ctx ?_l ?_g ?i)]
      => assert ($wfName : well_formed $p = true)>
        [()|(
          let wf_hyp := Control.hyp wfName in
          mlAdd (useBasicReasoning $i (A_or_notA $ctx $p $wf_hyp)) as $tmpName;
          mlDestructOr $tmpName as $n1 $n2
        )]
    end
  )
.

Ltac2 Notation "mlClassic" p(constr) "as" n1(constr) n2(constr) :=
  do_mlClassic_as p n1 n2
.

Tactic Notation "mlClassic" constr(p) "as" constr(n1) constr(n2) :=
  let f := ltac2:(p n1 n2 |- do_mlClassic_as (Option.get (Ltac1.to_constr p)) (Option.get (Ltac1.to_constr n1)) (Option.get (Ltac1.to_constr n2))) in
  f p n1 n2
.

#[local]
Example exMlClassic {Σ : Signature} (Γ : Theory) (a : Pattern):
  well_formed a ->
  Γ ⊢ (a or !a).
Proof.
  intros wfa.
  toMLGoal.
  { wf_auto2. }
  mlClassic (a) as "Hc1" "Hc2".
  { wf_auto2. }
  { mlLeft. mlExact "Hc1". }
  { mlRight. mlExact "Hc2". }
Defined.

Lemma prf_clear_hyps_meta {Σ : Signature} Γ l1 l2 l3 g i:
  Pattern.wf l1 ->
  Pattern.wf l2 ->
  Pattern.wf l3 ->
  well_formed g ->
  Γ ⊢i (foldr patt_imp g (l1 ++ l3)) using i ->
  Γ ⊢i (foldr patt_imp g (l1 ++ l2 ++ l3)) using i.
Proof.
  intros. eapply MP.
  apply H3.
  useBasicReasoning.
  induction l2.
  + simpl. apply A_impl_A. wf_auto2.
  + simpl. rewrite cons_middle. 
    apply prf_clear_hyp_meta with (l1 := foldr patt_imp g (l1 ++ l3) :: l1).
    1-4: wf_auto2.
    apply IHl2. wf_auto2.
Defined.

Lemma MLGoal_ApplyIn {Σ : Signature} Γ l1 l2 l3 name1 name2 h h' g i:
  mkMLGoal Σ Γ (l1 ++ (mkNH _ name1 h') :: l2 ++ (mkNH _ name2 (h ---> h')) :: l3) g i ->
  mkMLGoal Σ Γ (l1 ++ (mkNH _ name1 h) :: l2 ++ (mkNH _ name2 (h ---> h')) :: l3) g i.
Proof.
    intro H.
    mlExtractWF wfl wfg.
    (* mlAdd H. does not terminate *)
    fromMLGoal.
    assert ( well_formed (h ---> h') /\ well_formed h') as [wfhh' wfh'].
    {
       unfold patterns_of in wfl.
       rewrite map_app in wfl. simpl in wfl. rewrite map_app in wfl. simpl in wfl.
       assert (Pattern.wf (map nh_patt l2)). wf_auto2.
       pose proof (wfapp_proj_1 _ _ wfl).
       rewrite app_comm_cons in wfl.
       pose proof (wfapp_proj_1 _ _ (wfapp_proj_2 _ _ wfl)).
       rewrite app_assoc in wfl.
       pose proof (wfl₁hl₂_proj_h _ _ _ wfl).
       pose proof (wfapp_proj_2 _ _ wfl).
       wf_auto2.
    }
    remember wfl as wfl_save.
    clear Heqwfl_save.
    unfold patterns_of in wfl.
       rewrite map_app in wfl. simpl in wfl. rewrite map_app in wfl. simpl in wfl.
       
    assert (Pattern.wf (map nh_patt l1)). wf_auto2. 
    assert (Pattern.wf (map nh_patt l2)). wf_auto2.
    assert (Pattern.wf (map nh_patt l3)). wf_auto2.
    assert (well_formed h) as wfh. wf_auto2.
    ospecialize* H.
    simpl. wf_auto2.
    simpl. unfold patterns_of. repeat (rewrite map_app; simpl).
         wf_auto2.
    simpl in *.

    unfold patterns_of. repeat (rewrite map_app; simpl).
    eapply prf_add_lemma_under_implication_meta_meta with (h:=h').
    1-3: wf_auto2.
    + apply reorder_middle_to_last_meta. 1-4: wf_auto2. 
      rewrite -app_assoc. simpl. rewrite app_assoc.
      apply reorder_middle_to_last_meta. 1-4: wf_auto2.
      rewrite app_assoc.
      apply reorder_last_to_head_meta. 1-3: wf_auto2.
      rewrite app_comm_cons.  rewrite app_assoc. 
      apply reorder_last_to_head_meta. 1-3: wf_auto2.
      repeat rewrite app_comm_cons.
      rewrite <- app_nil_l with
                        (l:= map nh_patt l1).
      rewrite -app_assoc. rewrite app_comm_cons. simpl.
      rewrite <- app_nil_r with
                      (l:= (map nh_patt l1 ++ map nh_patt l2 ++ map nh_patt l3)).
      apply prf_clear_hyps_meta with
                      (l1 := (h :: ((h ---> h') :: []))) (l3 := []).
      1-4: wf_auto2.
      simpl.
      useBasicReasoning.
      apply modus_ponens; wf_auto2.
    + unfold patterns_of in H.
      repeat (rewrite map_app in H; simpl in H).
      rewrite -app_assoc.
      simpl.
      apply prf_clear_hyp_meta with
                          (l1 := (map nh_patt l1)).
      1-4:wf_auto2.
      apply reorder_last_to_middle_meta. 1-4:wf_auto2.
      assumption.
Defined.

Lemma MLGoal_Swap {Σ : Signature} Γ l1 l2 l3 name1 name2 h1 h2 g i:
  mkMLGoal Σ Γ (l1 ++ (mkNH _ name1 h1) :: l2 ++ (mkNH _ name2 h2) :: l3) g i ->
  mkMLGoal Σ Γ (l1 ++ (mkNH _ name2 h2) :: l2 ++ (mkNH _ name1 h1) :: l3) g i.
Proof.
  intro H.
  unfold of_MLGoal in *. simpl in *. intros WGg Wfl.
  assert (Pattern.wf (patterns_of l1) /\ Pattern.wf (patterns_of l2) /\ Pattern.wf (patterns_of l3)
        /\ well_formed h1 /\ well_formed h2) as [Wfl1 [Wfl2 [Wfl3 [Wfh1 Wfh2] ] ] ]. {
    clear -Wfl. unfold patterns_of in *; rewrite -> map_app in *.
    simpl in *. rewrite -> map_app in *. simpl in *.
    apply wfapp_proj_1 in Wfl as Wfl1.
    apply wfapp_proj_2 in Wfl. cbn in Wfl. destruct_andb! Wfl.
    apply wfapp_proj_1 in H0 as Wfl2.
    apply wfapp_proj_2 in H0. cbn in H0. destruct_andb! H0.
    firstorder.
  }
  ospecialize* H. 1: assumption.
  1: {
    unfold patterns_of. rewrite map_app. simpl. rewrite map_app. simpl.
    wf_auto2.
  }
  unfold patterns_of in *; rewrite -> map_app in *.
  simpl in *. rewrite -> map_app in *. simpl in *.
  apply reorder_head_to_middle_meta in H. 2-5: wf_auto2.
  rewrite app_comm_cons app_assoc in H.
  apply reorder_head_to_middle_meta in H. 2-5: wf_auto2.
  rewrite app_comm_cons app_assoc.
  apply reorder_middle_to_head_meta. 1-4: wf_auto2.
  rewrite app_comm_cons. rewrite -(app_assoc (h1 :: map nh_patt l1) _ (map nh_patt l3)).
  apply reorder_middle_to_head_meta. 1-4: wf_auto2. cbn.
  rewrite app_assoc. assumption.
Defined.

Ltac2 do_mlSwap (n1 : constr) (n2 : constr) :=
  Control.enter(fun () =>
    _ensureProofMode;
    _mlReshapeHypsBy2Names n1 n2;
    apply MLGoal_Swap;
    _mlReshapeHypsBackTwice
  )
.

Ltac2 Notation "mlSwap" n1(constr) "with" n2(constr) :=
  do_mlSwap n1 n2.

Tactic Notation "mlSwap" constr(n1) "with" constr(n2) :=
  let f := ltac2:(n1 n2 |- do_mlSwap (Option.get (Ltac1.to_constr n1)) (Option.get (Ltac1.to_constr n2))) in
  f n1 n2.

Ltac2 do_mlApplyIn (name1' : constr) (name2' : constr) :=
  Control.enter(fun () => 
    _ensureProofMode;
    _mlReshapeHypsBy2Names name1' name2';
    (
    (* Check the order of the hypotheses *)
    match! goal with
    | [ |- @of_MLGoal _ (@mkMLGoal _ _ (_ ++ ((@mkNH _ _ ?_h :: _) ++ (@mkNH _ _ (?_h ---> _) :: _))) _ _) ] =>
      apply MLGoal_ApplyIn;
      _mlReshapeHypsBackTwice
    | [ |- _ ] => _mlReshapeHypsBackTwice;
                  mlSwap $name1' with $name2';
                  _mlReshapeHypsBy2Names name2' name1' ;
                  apply MLGoal_ApplyIn;
                  _mlReshapeHypsBackTwice;
                  mlSwap $name1' with $name2'
    end
   )
  )
.

Ltac2 Notation "mlApply" n1(constr) "in" n2(constr) :=
  do_mlApplyIn n1 n2.

Tactic Notation "mlApply" constr(name1') "in" constr(name2') :=
  let f := ltac2:(name1' name2' |- do_mlApplyIn (Option.get (Ltac1.to_constr name1')) (Option.get (Ltac1.to_constr name2'))) in
  f name1' name2'.


Example ex_mlApplyIn {Σ : Signature} Γ a b c d e f i:
  well_formed a -> well_formed b ->
  well_formed c -> well_formed d ->
  well_formed e -> well_formed f ->
  Γ ⊢i (c---> a ---> c ---> (a ---> b) ---> a ---> b) using i.
Proof.
  intros.
  mlIntro.
  mlIntro.
  mlIntro.
  mlIntro.
  mlIntro.
  _mlReshapeHypsBy2Names "3" "4".
  _mlReshapeHypsBackTwice.
  _mlReshapeHypsBy2Names "4" "2".
  _mlReshapeHypsBackTwice.
  Fail mlSwap "3" with "3".
  Fail mlSwap "5" with "4".
  Fail mlSwap "1" with "6".
  mlSwap "3" with "4".
  mlApply "3" in "4".
  mlSwap "1" with "3".
  mlApply "3" in "1".
  mlAssumption.
Qed.

Lemma MLGoal_conjugate_hyps {Σ : Signature}
  (Γ : Theory)
  (l1 l2 l3 : hypotheses)
  (name1 name2 conj_name : string)
  (goal p1 p2 : Pattern)
  (info : ProofInfo):
  (* well_formed p1 -> well_formed p2 -> 
  Pattern.wf (map nh_patt (l1 ++ l2 ++ l3)) -> *)
  mkMLGoal Σ Γ ((mkNH _ conj_name (p1 and p2)) :: (l1 ++ (mkNH _ name1 p1) :: l2 ++ (mkNH _ name2 p2) :: l3)) goal info ->
  mkMLGoal Σ Γ (l1 ++ (mkNH _ name1 p1) :: l2 ++ (mkNH _ name2 p2) :: l3) goal info.
Proof.
  intro h1.
  mlExtractWF wfl wfg. 
  fromMLGoal.
  assert (well_formed p1 /\ well_formed p2) as [wfp1 wfp2].
  {
    unfold patterns_of in wfl.
    rewrite map_app in wfl. simpl in wfl. rewrite map_app in wfl. simpl in wfl.
    pose proof (wfl₁hl₂_proj_h _ _ _ wfl).
    (* pose proof (app_assoc (map nh_patt l1) (p1 :: map nh_patt l2) (p2 :: map nh_patt l3)). *)
    rewrite app_comm_cons app_assoc in wfl.
    pose proof (wfl₁hl₂_proj_h _ _ _ wfl).
    wf_auto2.
  }

  ospecialize* h1.
  simpl. exact wfg.
  simpl. wf_auto2.
  (* apply wf_cons. *)
  simpl in *.
  apply reorder_last_to_head_meta in h1.
  2-4: wf_auto2.
  eapply prf_add_lemma_under_implication_meta_meta with (h:=(p1 and p2)).
  1-3: wf_auto2.
  2: assumption.
  apply prf_conj_split_meta_meta.
  1-3: wf_auto2.
  1-2: unfold patterns_of; repeat (rewrite map_app; simpl).
  1-2: unfold patterns_of in *; repeat (rewrite map_app in wfl; simpl in wfl).
  - gapply nested_const_middle. try_solve_pile.
    1-3: wf_auto2.
  - rewrite app_comm_cons app_assoc.
    gapply nested_const_middle. try_solve_pile.
    1-3: wf_auto2.
Defined.

Lemma patt_and_comm_basic {Σ : Signature}
  (Γ : Theory)
  (φ1 φ2 : Pattern) :
  well_formed φ1 -> well_formed φ2 ->
  Γ ⊢i φ1 and φ2 ---> φ2 and φ1 using BasicReasoning.
Proof.
  intros wf1 wf2.
  pose proof (patt_and_comm) as H.
  eapply pf_iff_proj1 in H.
  eassumption.
  all: wf_auto2.
Defined.

Ltac2 do_mlConj (n1 : constr) (n2 : constr) (conj_name' : constr) :=
  Control.enter(fun () => 
    _ensureProofMode;
    do_failIfUsed conj_name';
    _mlReshapeHypsBy2Names n1 n2;
    apply MLGoal_conjugate_hyps with (conj_name := $conj_name');
    rewrite app_comm_cons;
    _mlReshapeHypsBackTwice;
    lazy_match! goal with
    | [ |- @of_MLGoal _ (@mkMLGoal _ _ ?l _ _) ] =>
      lazy_match! eval cbv in (index_of $n1 (names_of $l)) with
      | (Some ?i1) =>
         lazy_match! eval cbv in (index_of $n2 (names_of $l)) with
         | (Some ?i2) =>
           lazy_match! (eval cbv in (Nat.compare $i1 $i2)) with
           | (Lt) => ()
           | (Gt) => mlApplyMeta patt_and_comm_basic in $conj_name'
           | (Eq) => throw_pm_exn_with_goal "do_mlConj: Equal names were used"
           end
        | (None) => throw_pm_exn (Message.concat (Message.of_string "do_mlConj: No such name: ") (Message.of_constr n2))
        end
      | (None) => throw_pm_exn (Message.concat (Message.of_string "do_mlConj: No such name: ") (Message.of_constr n1))
      end
    end
  ).

Ltac2 Notation "mlConj" n1(constr) n2(constr) "as" n3(constr) :=
  do_mlConj n1 n2 n3.

Tactic Notation "mlConj" constr(n1) constr(n2) "as" constr(n3) :=
  let f := ltac2:(n1 n2 n3 |- do_mlConj (Option.get (Ltac1.to_constr n1)) (Option.get (Ltac1.to_constr n2)) (Option.get (Ltac1.to_constr n3))) in
  f n1 n2 n3.

Ltac2 rec do_mlConj_many l (name : constr) : unit :=
  match l with
  | [] => throw_pm_exn (Message.of_string "do_mlConj_many: empty list")
  | a :: t1 => 
    match t1 with
    | [] => throw_pm_exn (Message.of_string "do_mlConj_many: singleton list")
    | b :: t2 => 
      match t2 with
      | [] => mlConj $a $b as $name
      | _ :: _ => 
        do_mlConj_many t1 name;
        let hyps := do_getHypNames () in
        let newname := eval cbv in (fresh $hyps) in
        (* rename name into newname 
           TODO: optimise this with mlRename, which is independent of ML proofs: *)
        mlRename $name into $newname;
        mlConj $a $newname as $name;
        mlClear $newname
      end
    end
  end.

Ltac2 Notation "mlConj" l(list1(constr, ",")) "as" n3(constr) :=
  do_mlConj_many l n3.


  (**********************************************************************************)

Example ex_ml_conj_intro {Σ : Signature} Γ a b c d e f i:
   well_formed a -> well_formed b ->
   well_formed c -> well_formed d ->
   well_formed e -> well_formed f ->
   Γ ⊢i (a ---> b ---> c ---> d ---> e ---> f ---> (b and e)) using i.
Proof.
  intros wfa wfb wfc wfd wfe wff.
  mlIntro; mlIntro; mlIntro; mlIntro; mlIntro; mlIntro.
  Fail ltac2:(mlConj "1" as "conj").
  Fail ltac2:(mlConj "1" as "conj").
  Fail mlConj "0" "0" as "0".
  Fail mlConj "0" "0" as "00".
  mlConj "1" "4" as "CN1".
  mlConj "4" "1" as "CN2".
  mlAssumption.
Defined.

Example ex_ml_conj_many_intro {Σ : Signature} Γ a b c d e f i:
   well_formed a -> well_formed b ->
   well_formed c -> well_formed d ->
   well_formed e -> well_formed f ->
   Γ ⊢i a ---> b ---> c ---> d ---> e ---> f ---> (a and (b and (c and e))) using i.
Proof.
  intros wfa wfb wfc wfd wfe wff.
  mlIntro; mlIntro; mlIntro; mlIntro; mlIntro; mlIntro.
  ltac2:(mlConj "0", "1", "2", "4" as "conj").
  mlAssumption.
Defined.

(* This is an example and belongs to the end of this file.
   Its only purpose is only to show as many tactics as possible.\
 *)
 Example ex_and_of_equiv_is_equiv_2 {Σ : Signature} Γ p q p' q' i:
   well_formed p ->
   well_formed q ->
   well_formed p' ->
   well_formed q' ->
   Γ ⊢i (p <---> p') using i ->
   Γ ⊢i (q <---> q') using i ->
   Γ ⊢i ((p and q) <---> (p' and q')) using i.
Proof.
 intros wfp wfq wfp' wfq' pep' qeq'.
 pose proof (pip' := pep'). apply pf_conj_elim_l_meta in pip'; auto.
 pose proof (p'ip := pep'). apply pf_conj_elim_r_meta in p'ip; auto.
 pose proof (qiq' := qeq'). apply pf_conj_elim_l_meta in qiq'; auto.
 pose proof (q'iq := qeq'). apply pf_conj_elim_r_meta in q'iq; auto.

 toMLGoal.
 { wf_auto2. }
 unfold patt_iff.
 mlSplitAnd.
 - mlIntro "H0".
   mlDestructAnd "H0" as "H1" "H2".
   mlSplitAnd.
   + mlApplyMeta pip'.
     mlExactn 0.
   + mlApplyMeta qiq' in "H2".
     mlExact "H2".
 - mlIntro "H0".
   unfold patt_and at 2.
   unfold patt_not at 1.
   mlIntro "H1".
   mlDestructOr "H1" as "H2" "H3".
   + mlDestructAnd "H0" as "H3" "H4".
     unfold patt_not.
     mlApply "H2".
     mlClear "H2".
     mlClear "H4".
     fromMLGoal.
     exact p'ip.
   + mlAdd q'iq as "H1".
     mlDestructAnd "H0" as "H2" "H4".
     mlAssert ("Hq" : q).
     { wf_auto2. }
     { mlApply "H1". mlExact "H4". }
     unfold patt_not at 1.
     mlApply "H3".
     mlAssumption.
Defined.


#[local]
  Example ex_or_of_equiv_is_equiv_2 {Σ : Signature} Γ p q p' q' i:
    well_formed p ->
    well_formed q ->
    well_formed p' ->
    well_formed q' ->
    Γ ⊢i (p <---> p') using i ->
    Γ ⊢i (q <---> q') using i ->
    Γ ⊢i ((p or q) <---> (p' or q')) using i.
  Proof.
    intros wfp wfq wfp' wfq' pep' qeq'.

    pose proof (pip' := pep'). apply pf_conj_elim_l_meta in pip'; auto.
    pose proof (p'ip := pep'). apply pf_conj_elim_r_meta in p'ip; auto.
    pose proof (qiq' := qeq'). apply pf_conj_elim_l_meta in qiq'; auto.
    pose proof (q'iq := qeq'). apply pf_conj_elim_r_meta in q'iq; auto.

    toMLGoal.
    { wf_auto2. }
    unfold patt_iff.
    mlSplitAnd.
    - mlIntro "H0".
      mlDestructOr "H0" as "H1" "H2".
      mlLeft.
      + mlApplyMeta pip'.
        mlExact "H1".
      + mlRight.
        mlApplyMeta qiq'.
        mlExact "H2".
    - mlIntro "H0".
      mlDestructOr "H0" as "H1" "H2".
      mlLeft.
      + mlApplyMeta p'ip.
        mlExact "H1".
      + mlRight.
        mlApplyMeta q'iq.
        mlExact "H2". 
  Defined.


  Class MLReflexive {Σ : Signature} (op : Pattern -> Pattern -> Pattern) := {
    reflexive_op_well_formed : forall φ ψ,
      well_formed (op φ ψ) -> well_formed φ /\ well_formed ψ;
    mlReflexivity :
      forall Γ φ i, well_formed φ -> Γ ⊢i op φ φ using i;
  }.

  #[global]
  Instance patt_imp_is_reflexive {Σ : Signature} : @MLReflexive Σ patt_imp.
  Proof.
    constructor; intros.
    * wf_auto2.
    * gapply A_impl_A. try_solve_pile. assumption.
  Defined.

  #[export]
  Hint Resolve patt_imp_is_reflexive : core.

  #[global]
  Instance patt_iff_is_reflexive {Σ : Signature} : @MLReflexive Σ patt_iff.
  Proof.
    constructor; intros.
    * wf_auto2.
    * gapply pf_iff_equiv_refl. try_solve_pile. assumption.
  Defined.

  #[export]
  Hint Resolve patt_iff_is_reflexive : core.

  Lemma MLGoal_reflexivity {Σ : Signature} Γ l φ i op {_ : MLReflexive op} :
    mkMLGoal _ Γ l (op φ φ) i.
  Proof.
    intros HΓ. unfold of_MLGoal. simpl. intros wfl.
    eapply MP. 2: gapply nested_const.
    2: try_solve_pile. 2-3: wf_auto2.
    apply mlReflexivity.
    cbn in HΓ. by apply reflexive_op_well_formed in HΓ as [_ ?].
  Defined.

  Ltac2 do_mlReflexivity () :=
    Control.enter(fun () =>
      _ensureProofMode;
      lazy_match! goal with
      | [ |- @of_MLGoal _ (@mkMLGoal _ _ _ (?op ?_g ?_g) _) ] =>
        match! goal with (* error handling *)
        | [ |- _] => now (apply MLGoal_reflexivity; eauto)
        | [ |- _] =>
          throw_pm_exn
          (Message.concat (Message.of_string "do_mlReflexivity: ")
          (Message.concat (Message.of_constr op) (Message.of_string " is not reflexive!"))
          )
        end
      | [ |- _] => Message.print (Message.of_string "Goal is not shaped as φ = φ!"); fail
      end
    ).

  Ltac2 Notation "mlReflexivity" :=
    do_mlReflexivity ().


  Tactic Notation "mlReflexivity" :=
    ltac2:(do_mlReflexivity ()).

#[local]
  Example reflexive_imp_test1 {Σ : Signature} Γ p q p' q' i:
    well_formed p ->
    well_formed q ->
    well_formed p' ->
    well_formed q' ->
    Γ ⊢i p ---> p using i.
  Proof.
    intros. toMLGoal. wf_auto2.
    mlReflexivity.
  Defined.

#[local]
  Example notreflexive_and_test1 {Σ : Signature} Γ p q p' q' i:
    well_formed p ->
    well_formed q ->
    well_formed p' ->
    well_formed q' ->
    Γ ⊢i p and p using i.
  Proof.
    intros. toMLGoal. wf_auto2.
    Fail mlReflexivity.
  Abort.

#[local]
  Example reflexive_imp_test2 {Σ : Signature} Γ p q p' q' i:
    well_formed p ->
    well_formed q ->
    well_formed p' ->
    well_formed q' ->
    Γ ⊢i q ---> q' ---> p' ---> p ---> p using i.
  Proof.
    intros. repeat mlIntro.
    mlRevertLast.
    mlReflexivity.
  Defined.

#[local]
  Example reflexive_iff_test {Σ : Signature} Γ p q p' q' i:
    well_formed p ->
    well_formed q ->
    well_formed p' ->
    well_formed q' ->
    Γ ⊢i q ---> q' ---> p' ---> p <---> p using i.
  Proof.
    intros. do 3 mlIntro.
    mlReflexivity.
  Defined.

Lemma pf_iff_equiv_trans_obj {Σ : Signature} : forall Γ A B C i,
  well_formed A -> well_formed B -> well_formed C ->
  Γ ⊢i (A <---> B) ---> (B <---> C) ---> (A <---> C) using i.
Proof.
  intros * wfA wfB wfC.
  do 2 mlIntro.
  mlDestructAnd "0".
  mlDestructAnd "1".
  mlSplitAnd.
  pose proof (syllogism Γ _ _ _ wfA wfB wfC).
  use i in H.
  mlApplyMeta H in "2".
  mlApply "0" in "2".
  mlExact "0".
  pose proof (syllogism Γ _ _ _ wfC wfB wfA).
  use i in H.
  mlApplyMeta H in "4".
  mlApply "4" in "3".
  mlExact "3".
Defined.

Lemma pf_iff_equiv_sym_obj {Σ : Signature} Γ A B i :
  well_formed A -> well_formed B -> Γ ⊢i (A <---> B) ---> (B <---> A) using i.
Proof.
  intros wfa wfb.
  mlIntro.
  mlDestructAnd "0".
  mlSplitAnd; mlAssumption.
Defined.

(* TODO: make for other transitive relations too, then maybe move *)
Tactic Notation "mlTrans_iff" constr(b) :=
  match goal with
  | [ |- context[(mkMLGoal _ ?g ?h (patt_iff ?a ?c) ?i)] ] =>
      let Htrans := fresh in
        opose proof* (pf_iff_equiv_trans_obj g a b c i _ _ _) as Htrans;
        last (
          let Htrans2 := eval cbv in (fresh (map nh_name h)) in (
            mlAssert (Htrans2 : (a <---> b));
            last (
              mlApplyMeta Htrans in Htrans2;
              mlApply Htrans2;
              mlClear Htrans2
            )
          );
          last 2 [clear Htrans]
        )
  end.

Tactic Notation "emlTrans_iff" :=
  let ep := fresh in
    evar (ep : Pattern);
    mlTrans_iff ep;
    subst ep.

Lemma extract_common_from_equivalence_r {Σ : Signature} Γ a b c i :
  well_formed a -> well_formed b -> well_formed c ->
  Γ ⊢i (b and a <---> c and a) <---> (a ---> b <---> c) using i.
Proof with try solve [auto | wf_auto2].
  intros wfa wfb wfc.
  toMLGoal...
  pose proof (extract_common_from_equivalence Γ a b c wfa wfb wfc).
  use i in H.
  emlTrans_iff; only 6: mlExactMeta H...
  clear H Hwf. mlSplitAnd; mlIntro.
  * pose proof (patt_and_comm Γ a b wfa wfb).
    use i in H.
    emlTrans_iff; only 5: mlExactMeta H...
    pose proof (patt_and_comm Γ c a wfc wfa).
    use i in H0.
    emlTrans_iff; only 6: mlExactMeta H0...
    mlExact "0".
  * pose proof (patt_and_comm Γ b a wfb wfa).
    use i in H.
    emlTrans_iff; only 5: mlExactMeta H...
    pose proof (patt_and_comm Γ a c wfa wfc).
    use i in H0.
    emlTrans_iff; only 6: mlExactMeta H0...
    mlExact "0".
Defined.

Theorem provable_iff_top:
  ∀ {Σ : Signature} (Γ : Theory) (φ : Pattern)   (i : ProofInfo),
    well_formed φ ->
    Γ ⊢i φ using i ->
    Γ ⊢i φ <--->  patt_top using i .
Proof.
  intros.
  mlSplitAnd.
  2:{ mlIntro. mlExactMeta H0. }
  mlIntro.
  pose proof top_holds Γ.
  use i in H1.
  mlExactMeta H1.
Defined.

Theorem patt_and_id_r:
  ∀ {Σ : Signature} (Γ : Theory) (φ : Pattern),
    well_formed φ ->
    Γ ⊢i φ and patt_top <--->  φ using BasicReasoning .
Proof.
  intros.
  mlSplitAnd.
  * mlIntro.
    mlDestructAnd "0".
    mlAssumption.
  * mlIntro.
    mlSplitAnd.
    1: mlAssumption.
    mlIntro.
    mlAssumption.
Defined.
