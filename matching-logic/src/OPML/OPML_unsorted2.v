
Definition is_leftb {A B : Set} (x : A + B) : bool :=
match x with
| inl _ => true
| _ => false
end.

Definition is_rightb {A B : Set} (x : A + B) : bool :=
match x with
| inl _ => false
| _ => true
end.

Definition andb_split_1 (b1 b2 : bool) : andb b1 b2 = true -> b1 = true.
Proof.
  destruct b1, b2; simpl; try reflexivity.
  all: intros; congruence.
Defined.

Definition andb_split_2 (b1 b2 : bool) : andb b1 b2 = true -> b2 = true.
Proof.
  destruct b1, b2; simpl; try reflexivity.
  all: intros; congruence.
Defined.


From Coq Require Export ssreflect ssrfun ssrbool String.
From MatchingLogic Require Import extralibrary.

From Coq.Classes Require Export RelationClasses.

From stdpp Require Export
  base
  list
  countable
  infinite
  finite
.

From MatchingLogic Require Export Lattice.
From Equations Require Export -(notations) Equations.


Import ListNotations.

Set Transparent Obligations.

Set Default Proof Mode "Classic".

Class OPMLSorts := {
    opml_sort : Set;
    opml_sort_eqdec :: EqDecision opml_sort;
    opml_sort_countable :: Countable opml_sort;
    (* opml_subsort : relation opml_sort;
    opml_subsort_po :: PartialOrder opml_subsort; *)
}.

Class OPMLVariables {Ss : OPMLSorts} := mkOPMLVariables {
  opml_evar : Set;
  opml_svar : Set;
  opml_evar_eqdec :: EqDecision opml_evar;
  opml_evar_countable :: Countable opml_evar;
  (* opml_evar_infinite :: Infinite opml_evar; *)
  opml_svar_eqdec :: EqDecision opml_svar;
  opml_svar_countable :: Countable opml_svar;
  (* opml_svar_infinite :: Infinite opml_svar; *)

  evar_sort : opml_evar -> opml_sort;
  svar_sort : opml_svar -> opml_sort;

  opml_evar_infinite s ::
    Infinite {x : opml_evar & decide (evar_sort x = s)};
  opml_svar_infinite s ::
    Infinite {x : opml_svar & decide (svar_sort x = s)}
}.

Print Countable.
Search Countable.

Program Instance String_OPMLVariables {Ss : OPMLSorts} : OPMLVariables := {|
  opml_evar := opml_sort * string;
  opml_svar := opml_sort * string;
  evar_sort := fun x => fst x;
  svar_sort := fun x => fst x;
|}.
Next Obligation.
  unshelve econstructor.
  * intro l.
    pose (map (snd ∘ projT1) l) as l_mapped.
    pose (fresh l_mapped) as new.
    apply (existT (s, new)). simpl.
    destruct decide. reflexivity. by simpl in n.
  * intros. unfold fresh.
    simpl.
    intro.
    apply (@infinite_is_fresh _ string_infinite (map (snd ∘ projT1) xs)).
    unfold fresh.
    epose proof elem_of_list_fmap_1 (snd ∘ projT1) _ _ H.
    simpl in H0. assumption.
  * unfold fresh.
    intros xs ys EQ.
    pose proof (@infinite_fresh_Permutation _ string_infinite (map (snd ∘ projT1) xs) (map (snd ∘ projT1) ys)).
    unfold fresh in H. rewrite H. 2: reflexivity.
    by apply Permutation_map.
Defined.
Final Obligation.
  unshelve econstructor.
  * intro l.
    pose (map (snd ∘ projT1) l) as l_mapped.
    pose (fresh l_mapped) as new.
    apply (existT (s, new)). simpl.
    destruct decide. reflexivity. by simpl in n.
  * intros. unfold fresh.
    simpl.
    intro.
    apply (@infinite_is_fresh _ string_infinite (map (snd ∘ projT1) xs)).
    unfold fresh.
    epose proof elem_of_list_fmap_1 (snd ∘ projT1) _ _ H.
    simpl in H0. assumption.
  * unfold fresh.
    intros xs ys EQ.
    pose proof (@infinite_fresh_Permutation _ string_infinite (map (snd ∘ projT1) xs) (map (snd ∘ projT1) ys)).
    unfold fresh in H. rewrite H. 2: reflexivity.
    by apply Permutation_map.
Defined.


Check opml_evar_infinite.

Class OPMLSymbols {Ss : OPMLSorts} := {
  opml_symbol : Set;
  opml_sym_eqdec :: EqDecision opml_symbol;
  opml_sym_countable :: Countable opml_symbol;

  opml_arg_sorts :
    opml_symbol ->
    list opml_sort ;

  opml_ret_sort :
    opml_symbol ->
    opml_sort ;
}.

Class OPMLSignature := {
  opml_sorts :: OPMLSorts ;
  opml_variables :: OPMLVariables;
  opml_symbols :: OPMLSymbols;
}.

Section Syntax.

Context {Σ : OPMLSignature}.

Inductive OPMLPattern :=
(* | op_upcast
    (from to : opml_sort)
    (subsort : opml_subsort from to)
    (φ : OPMLPattern) *)
| op_bot
| op_bevar (dbi : nat)
| op_bsvar (dbi : nat)
| op_fevar (x : opml_evar)
| op_fsvar (X : opml_svar)
| op_imp (φ1 φ2 : OPMLPattern)
| op_app (σ : opml_symbol) (args : list OPMLPattern)
| op_eq (s1 s2 : opml_sort) (φ1 φ2 : OPMLPattern)
| op_ex (s : opml_sort) (φ : OPMLPattern)
| op_mu (s : opml_sort) (φ : OPMLPattern).

Section pat_ind.

  Variables
    (P : OPMLPattern -> Prop).
  Hypotheses
    (P_bot : P op_bot)
    (P_bevar : forall dbi, P (op_bevar dbi))
    (P_fevar : forall x, P (op_fevar x))
    (P_bsvar : forall dbi, P (op_bsvar dbi))
    (P_fsvar : forall x, P (op_fsvar x))
    (P_imp : forall φ, P φ -> forall ψ, P ψ -> P (op_imp φ ψ))
    (P_app : forall σ args, Forall P args -> P (op_app σ args))
    (P_ex : forall σ φ, P φ -> P (op_ex σ φ))
    (P_mu : forall σ φ, P φ -> P (op_mu σ φ))
    (P_eq : forall s1 s2 φ, P φ -> forall ψ, P ψ -> P (op_eq s1 s2 φ ψ)).

  Definition OPML_ind (φ : OPMLPattern) : P φ.
  Proof.
    revert φ.
    refine (fix OPML_ind φ :=
    match φ with
     | op_bot => P_bot
     | op_bevar dbi => P_bevar dbi
     | op_fevar x => P_fevar x
     | op_bsvar dbi => P_bsvar dbi
     | op_fsvar x => P_fsvar x
     | op_imp φ1 φ2 => P_imp _ (OPML_ind φ1) _ (OPML_ind φ2) 
     | op_app σ args => _
     | op_ex σ φ => P_ex σ _ (OPML_ind φ)
     | op_mu σ φ => P_mu σ _ (OPML_ind φ)
     | op_eq s1 s2 φ1 φ2 => P_eq s1 s2 _ (OPML_ind φ1) _ (OPML_ind φ2) 
    end).
    apply P_app.
    induction args; constructor.
    by apply OPML_ind.
    assumption.
  Defined.
End pat_ind.

Definition shift {T : Set} (f : nat -> T) (d : T)
  : nat -> T :=
fun n =>
match n with
| O => d
| S n' => f n'
end.

Definition update {T : Set} (n : nat) (d : T) (f : nat -> T)
  : nat -> T :=
  fun m => if decide (n = m) then d else f m.

Fixpoint app_ws (well_sorted : opml_sort -> OPMLPattern -> bool)
                (φs : list OPMLPattern)
                (ss : list opml_sort) {struct φs} :=
  match φs, ss with
  | [], [] => true
  | φ::φs, s::ss => well_sorted s φ &&
                    app_ws well_sorted φs ss
  | _, _ => false
  end.

Fixpoint well_sorted
  (esorts : nat -> option opml_sort)
  (ssorts : nat -> option opml_sort)
  (s : opml_sort)
  (p : OPMLPattern) {struct p} : bool :=
  match p with
   | op_bot => true
   | op_bevar dbi => decide (esorts dbi = Some s)
   | op_bsvar dbi => decide (ssorts dbi = Some s)
   | op_fevar x => decide (evar_sort x = s)
   | op_fsvar X => decide (svar_sort X = s)
   | op_imp φ1 φ2 => well_sorted esorts ssorts s φ1 &&
                     well_sorted esorts ssorts s φ2
   | op_app σ args =>
      decide (s = opml_ret_sort σ) &&
      app_ws (well_sorted esorts ssorts) args (opml_arg_sorts σ)
   | op_ex s0 φ => well_sorted (shift esorts (Some s0)) ssorts s φ
   | op_mu s0 φ => well_sorted esorts (shift ssorts (Some s0)) s φ
   | op_eq s1 s2 φ1 φ2
      => well_sorted esorts ssorts s1 φ1 &&
         well_sorted esorts ssorts s1 φ2 &&
         decide (s2 = s)
  end.

  Inductive infer_result :=
  | BadSort
  | AnySort
  | Sort (s : opml_sort).

  #[global]
  Instance infer_result_eqdec : EqDecision infer_result.
  Proof.
    solve_decision.
  Defined.

  Definition merge_sorts (r1 r2 : infer_result) : infer_result :=
  match r1, r2 with
  | BadSort, _ | _, BadSort => BadSort
  | Sort s1, Sort s2 => if decide (s1 = s2) then Sort s1 else BadSort
  | Sort s, _ | _, Sort s => Sort s
  | AnySort, AnySort => AnySort
  end.

  Fixpoint app_infer (infer : OPMLPattern -> infer_result)
                (φs : list OPMLPattern)
                (ss : list opml_sort)
                (r : opml_sort) {struct φs}
            : infer_result :=
  match φs, ss with
  | [], [] => Sort r
  | φ::φs, s::ss =>
    match infer φ with
    | Sort s' =>
      match decide (s' = s) with
      | left _ => app_infer infer φs ss r
      | right _ => BadSort
      end
    | AnySort => app_infer infer φs ss r
    | BadSort => BadSort
    end
  | _, _ => BadSort
  end.

  Fixpoint infer_sort
    (esorts : nat -> option opml_sort)
    (ssorts : nat -> option opml_sort)
    (p : OPMLPattern)
    : infer_result :=
  match p with
   | op_bot => AnySort
   | op_bevar dbi => match esorts dbi with
                     | Some s => Sort s
                     | None   => BadSort
                     end
   | op_bsvar dbi => match ssorts dbi with
                     | Some s => Sort s
                     | None   => BadSort
                     end
   | op_fevar x => Sort (evar_sort x)
   | op_fsvar X => Sort (svar_sort X)
   | op_imp φ1 φ2 => merge_sorts (infer_sort esorts ssorts φ1)
                                 (infer_sort esorts ssorts φ2)
   | op_app σ args =>
     app_infer (infer_sort esorts ssorts) args (opml_arg_sorts σ) (opml_ret_sort σ)
   | op_eq s1 s2 φ1 φ2 =>
     match merge_sorts (infer_sort esorts ssorts φ1)
                       (infer_sort esorts ssorts φ2) with
     | BadSort => BadSort
     | Sort s  => if decide (s = s1) then Sort s2 else BadSort
     | AnySort => Sort s2
     end
   | op_ex s0 φ => infer_sort (shift esorts (Some s0)) ssorts φ
   | op_mu s0 φ => infer_sort esorts (shift ssorts (Some s0)) φ
  end.

  Lemma app_infer_never_Any :
    forall φs ss esorts ssorts d,
      app_infer (infer_sort esorts ssorts) φs ss d <> AnySort.
  Proof.
    induction φs; simpl; intros; intro; case_match; try congruence.
    case_match; try congruence.
    case_match; try congruence.
  Defined.

  Lemma infer_sound_Any :
    forall φ esorts ssorts,
      infer_sort esorts ssorts φ = AnySort ->
      forall s, well_sorted esorts ssorts s φ.
  Proof.
    induction φ using OPML_ind; intros; simpl in *; auto.
    * case_match; simpl. 2: congruence.
      inversion H.
    * inversion H.
    * case_match; simpl. 2: congruence.
      inversion H.
    * inversion H.
    * destruct infer_sort eqn:Q1 in H; simpl in H; try congruence.
      all: destruct infer_sort eqn:Q2 in H; simpl in H; try congruence.
      - rewrite ->IHφ1, ->IHφ2; auto.
      - case_match; congruence.
    * exfalso. by apply app_infer_never_Any in H0.
    * destruct infer_sort eqn:Q1 in H; simpl in H; try congruence.
      all: destruct infer_sort eqn:Q2 in H; simpl in H; try congruence.
      - case_match; try congruence.
      - case_match; try congruence.
      - case_match; try congruence.
        case_match; try congruence.
  Defined.

  Lemma infer_sound_Sort :
    forall φ esorts ssorts s,
      infer_sort esorts ssorts φ = Sort s ->
      well_sorted esorts ssorts s φ.
  Proof.
    induction φ using OPML_ind; intros; simpl in *; auto.
    * case_match; simpl. 2: congruence.
      inversion H. destruct decide; auto.
    * inversion H. destruct decide; auto.
    * case_match; simpl. 2: congruence.
      inversion H. destruct decide; auto.
    * inversion H. destruct decide; auto.
    * destruct infer_sort eqn:Q1 in H; simpl in H; try congruence.
      all: destruct infer_sort eqn:Q2 in H; simpl in H; try congruence.
      - inversion H; subst. clear H.
        rewrite IHφ2; auto.
        rewrite infer_sound_Any; auto.
      - inversion H; subst. clear H.
        rewrite IHφ1; auto.
        rewrite infer_sound_Any; by auto.
      - case_match; try congruence.
        inversion H; subst. clear H.
        destruct decide; subst. 2: { by simpl in H0. }
        rewrite IHφ1; auto.
        rewrite IHφ2; by auto.
    * remember (opml_arg_sorts σ) as ss.
      clear Heqss. generalize dependent ss.
      induction H; simpl in *; intros.
      - case_match; try congruence.
        inversion H0. by rewrite decide_eq_same.
      - destruct ss eqn:Pss; try congruence.
        destruct (infer_sort esorts ssorts x) eqn:P;
          try congruence.
        + apply infer_sound_Any with (s := o) in P.
          rewrite P.
          specialize (IHForall _ H1).
          apply andb_true_iff in IHForall as [H11 H22].
          by rewrite H11 H22.
        + destruct decide in H1. 2: by simpl in H1. subst.
          rewrite H; auto.
          specialize (IHForall _ H1).
          apply andb_true_iff in IHForall as [H11 H22].
          by rewrite H11 H22.
    * case_match; try congruence.
      {
        inversion H; subst; clear H.
        rename H0 into H.
        destruct infer_sort eqn:Q1 in H; simpl in H; try congruence; destruct infer_sort eqn:Q2 in H; simpl in H; try congruence.
        - rewrite infer_sound_Any; auto.
          rewrite infer_sound_Any; auto.
          simpl. by rewrite decide_eq_same.
        - case_match; congruence.
      }
      {
        case_match.
        inversion H; subst; clear H.
        destruct decide; simpl in H1; try congruence.
        subst. clear H1.
        rename H0 into H.
        destruct infer_sort eqn:Q1 in H; simpl in H; try congruence; destruct infer_sort eqn:Q2 in H; simpl in H; try congruence.
        - inversion H; subst; clear H.
          rewrite IHφ2; auto.
          rewrite infer_sound_Any; auto.
          by rewrite decide_eq_same.
        - inversion H; subst; clear H.
          rewrite IHφ1; auto.
          rewrite infer_sound_Any; auto.
          by rewrite decide_eq_same.
        - case_match; try congruence.
          destruct decide; simpl in H0; try congruence. subst.
          inversion H; subst; clear H.
          rewrite IHφ2; auto.
          rewrite IHφ1; auto.
          by rewrite decide_eq_same.
        - congruence.
      }
  Defined.

  Lemma well_sorted_infer :
    forall φ esorts ssorts s,
      well_sorted esorts ssorts s φ = true ->
      infer_sort esorts ssorts φ = Sort s \/
      infer_sort esorts ssorts φ = AnySort.
  Proof.
     induction φ using OPML_ind; simpl; intros; auto; try congruence.
     * destruct decide. 2: by simpl in H. rewrite e.
       by left.
     * destruct decide. 2: by simpl in H. left.
       by rewrite e.
     * destruct decide. 2: by simpl in H. rewrite e.
       by left.
     * destruct decide. 2: by simpl in H. left.
       by rewrite e.
     * apply andb_true_iff in H as [H1 H2].
       apply IHφ1 in H1.
       apply IHφ2 in H2.
       destruct H1 as [H1 | H1], H2 as [H2 | H2];
         rewrite H1 H2; simpl; try by left.
       rewrite decide_eq_same; simpl; by left.
       by right.
     * apply andb_true_iff in H0 as [H0 H1].
       destruct decide. 2: by simpl in H0.
       subst. clear H0.
       remember (opml_arg_sorts σ) as sorts. clear Heqsorts.
       generalize dependent sorts.
       induction H; intros; simpl in *.
       - destruct sorts; try congruence. by left.
       - destruct sorts; try congruence.
         apply andb_true_iff in H1 as [H1_1 H1_2].
         apply H in H1_1 as [H1_1|H1_1]; rewrite H1_1.
         + rewrite decide_eq_same.
           apply IHForall in H1_2. assumption.
         + apply IHForall in H1_2. assumption.
     * apply andb_true_iff in H as [H H3].
       apply andb_true_iff in H as [H1 H2].
       destruct decide. 2: by simpl in H3. subst.
       apply IHφ1 in H1.
       apply IHφ2 in H2.
       destruct H1 as [H1 | H1], H2 as [H2 | H2];
         rewrite H1 H2; simpl; try by left.
       all: rewrite decide_eq_same; simpl; try by left.
       rewrite decide_eq_same; simpl; try by left.
  Qed.

Fixpoint free_evar_subst (ps : OPMLPattern) (y : opml_evar)
  (p : OPMLPattern) : OPMLPattern :=
match p with
 | op_fevar x => if decide (x = y) then ps else p
 | op_imp φ1 φ2 => op_imp (free_evar_subst ps y φ1) (free_evar_subst ps y φ2)
 | op_app σ args => op_app σ (map (free_evar_subst ps y) args)
 | op_ex s φ => op_ex s (free_evar_subst ps y φ)
 | op_mu s φ => op_mu s (free_evar_subst ps y φ)
 | r => r
end.

Fixpoint bevar_subst (ps : OPMLPattern) (x : nat)
  (p : OPMLPattern) : OPMLPattern :=
match p with
 | op_bevar n =>
   match compare_nat n x with
   (* | Nat_less _ _ _ => op_bevar n *)
   | Nat_equal _ _ _ => ps
   | _ => op_bevar n (* op_bevar (Nat.pred n) *)
   end
 | op_imp φ1 φ2 => op_imp (bevar_subst ps x φ1) (bevar_subst ps x φ2)
 | op_eq s1 s2 φ1 φ2 => op_eq s1 s2 (bevar_subst ps x φ1) (bevar_subst ps x φ2)
 | op_app σ args => op_app σ (map (bevar_subst ps x) args)
 | op_ex s φ => op_ex s (bevar_subst ps (S x) φ)
 | op_mu s φ => op_mu s (bevar_subst ps x φ)
 | r => r
end.

Fixpoint bsvar_subst (ps : OPMLPattern) (x : nat)
  (p : OPMLPattern) : OPMLPattern :=
match p with
 | op_bsvar n =>
   match compare_nat n x with
   (* | Nat_less _ _ _ => op_bevar n *)
   | Nat_equal _ _ _ => ps
   | _ => op_bevar n (* op_bevar (Nat.pred n) *)
   end
 | op_imp φ1 φ2 => op_imp (bsvar_subst ps x φ1) (bsvar_subst ps x φ2)
 | op_eq s1 s2 φ1 φ2 => op_eq s1 s2 (bsvar_subst ps x φ1) (bsvar_subst ps x φ2)
 | op_app σ args => op_app σ (map (bsvar_subst ps x) args)
 | op_ex s φ => op_ex s (bsvar_subst ps x φ)
 | op_mu s φ => op_mu s (bsvar_subst ps (S x) φ)
 | r => r
end.

Fixpoint opml_size (p : OPMLPattern) : nat :=
match p with
 | op_imp φ1 φ2 => 1 + opml_size φ1 + opml_size φ2
 | op_eq _ _ φ1 φ2 => 1 + opml_size φ1 + opml_size φ2
 | op_app σ args => 1 + foldr (fun φ acc => opml_size φ + acc) 0 args
 | op_ex s φ => 1 + opml_size φ
 | op_mu s φ => 1 + opml_size φ
 | _ => 1
end.

Lemma bevar_subst_opml_size :
  forall φ x n,
    opml_size (bevar_subst (op_fevar x) n φ) = opml_size φ.
Proof.
  induction φ using OPML_ind; simpl; intros; try reflexivity.
  * by case_match.
  * by erewrite ->IHφ1, ->IHφ2.
  * f_equal. induction H; simpl.
    reflexivity.
    rewrite IHForall.
    erewrite H.
    reflexivity.
  * by erewrite IHφ.
  * by erewrite IHφ.
  * by rewrite ->IHφ1, ->IHφ2.
Defined.

Fixpoint free_evars (φ : OPMLPattern) {struct φ} : gset (opml_evar) :=
match φ with
 | op_fevar x => {[x]}
 | op_imp φ1 φ2 => free_evars φ1 ∪ free_evars φ2
 | op_app σ args => foldr (fun x acc => free_evars x ∪ acc) ∅ args
 | op_eq s1 s2 φ1 φ2 => free_evars φ1 ∪ free_evars φ2
 | op_ex s φ => free_evars φ
 | op_mu s φ => free_evars φ
 | _ => ∅
end.

Fixpoint free_svars (φ : OPMLPattern) : gset opml_svar :=
match φ with
 | op_fsvar X => {[X]}
 | op_imp φ1 φ2 => free_svars φ1 ∪ free_svars φ2
 | op_app σ args => foldr (fun x acc => free_svars x ∪ acc) ∅ args
 | op_eq s1 s2 φ1 φ2 => free_svars φ1 ∪ free_svars φ2
 | op_ex s φ => free_svars φ
 | op_mu s φ => free_svars φ
 | _ => ∅
end.

Definition default : nat -> option opml_sort := fun _ : nat => None.

Fixpoint dep_filter {A} (f : A -> bool) (l : list A) {struct l} :
  list {a : A & f a}.
Proof.
  refine (
    match l with
    | [] => []
    | x::xs => _
    end
  ).
  destruct (f x) eqn:P.
  * exact (existT x P :: dep_filter A f xs).
  * exact (dep_filter A f xs).
Defined.

Definition fresh_evar (s : opml_sort) (φ : OPMLPattern) : { x : opml_evar & decide (evar_sort x = s) }.
Proof.
  pose (elements (free_evars φ)) as fs.
  pose (dep_filter (fun x => decide (evar_sort x = s)) fs) as filtered.
  simpl in filtered.
  exact (fresh filtered).
Defined.
Definition fresh_svar (s : opml_sort) (φ : OPMLPattern) :
  { x : opml_svar & decide (svar_sort x = s) }.
Proof.
  pose (elements (free_svars φ)) as fs.
  pose (dep_filter (fun x => decide (svar_sort x = s)) fs) as filtered.
  simpl in filtered.
  exact (fresh filtered).
Defined.

Definition is_weaker (f1 f2 : nat -> option opml_sort) : Prop :=
  forall n s, f2 n = Some s -> f1 n = Some s.

Notation "f '≤ₛ' g" := (is_weaker f g) (at level 50).

Lemma default_is_strongest :
  forall f, f ≤ₛ default.
Proof.
  intros f n σ H.
  unfold default in H.
  inversion H.
Defined.

Lemma is_weaker_refl :
  forall f, is_weaker f f.
Proof.
  intros. intro. intros.
  assumption.
Defined.

Lemma is_weaker_shift :
  forall f1 f2,
    is_weaker f1 f2 ->
    forall d,
      is_weaker (shift f1 d) (shift f2 d).
Proof.
  intros.
  unfold is_weaker.
  intros.
  destruct n; simpl in *. assumption.
  by apply H.
Defined.


Ltac invt H :=
inversion H; subst; clear H.

Lemma shift_update :
  forall {T: Set} (f : nat -> T) n d1 d2,
    shift (update n d1 f) d2 =
    update (S n) d1 (shift f d2).
Proof.
  intros. unfold shift, update.
  extensionality x.
  destruct x; simpl. reflexivity.
  destruct decide; simpl;
  destruct decide; simpl; try lia; reflexivity.
Defined.

Lemma well_sorted_weaken :
  forall φ s fe fe' fs fs',
    is_weaker fe' fe ->
    is_weaker fs' fs ->
    well_sorted fe fs s φ ->
    well_sorted fe' fs' s φ.
Proof.
  induction φ using OPML_ind; intros * Hw1 Hw2 Hwf; try by constructor.
  * simpl in *. destruct decide. 2: simpl in Hwf; congruence.
    clear Hwf. apply Hw1 in e.
    cbn. rewrite e. destruct decide; auto.
  * simpl in *. assumption.
  * simpl in *. destruct decide. 2: simpl in Hwf; congruence.
    clear Hwf. apply Hw2 in e.
    cbn. rewrite e. destruct decide; auto.
  * simpl in *. assumption.
  * simpl in *. apply andb_true_iff in Hwf as [Hwf1 Hwf2].
    erewrite IHφ1; try eassumption.
    erewrite IHφ2; try eassumption.
    reflexivity.
  * simpl in *.
    apply andb_split_1 in Hwf as H1. rewrite H1. simpl.
    apply andb_split_2 in Hwf.
    {
      clear - H Hwf Hw1 Hw2.
      remember (opml_arg_sorts σ) as sorts.
      clear Heqsorts. revert sorts Hwf.
      induction args; simpl in *; intros.
      + case_match; by auto.
      + case_match. by auto.
        subst.
        inversion H. subst. erewrite H2. 2-3: eassumption.
        2: by apply andb_split_1 in Hwf.
        eapply IHargs. assumption.
        by apply andb_split_2 in Hwf.
    }
  * simpl in *. eapply IHφ in Hwf. exact Hwf.
    by apply is_weaker_shift.
    assumption.
  * simpl in *. eapply IHφ in Hwf. exact Hwf.
    2: by apply is_weaker_shift.
    assumption.
  * simpl in *.
    erewrite IHφ1; try eassumption.
    erewrite IHφ2; try eassumption.
    simpl. apply andb_split_2 in Hwf. assumption.
    simpl. apply andb_split_1, andb_split_2 in Hwf. assumption.
    simpl. apply andb_split_1, andb_split_1 in Hwf. assumption.
Defined.

Lemma well_sorted_bevar_subst :
  forall φ ψ s s' fe fs n,
  well_sorted fe fs s φ ->            (* fe ∪ (n, s'), fs ⊢ φ : s *)
  well_sorted default default s' ψ -> (* ∅ , ∅            ⊢ ψ : s' *)
  fe n = Some s' ->                   (* fe ∖ n, fs       ⊢ φ[ψ/n] : s *)
  well_sorted (update n None fe) fs s (bevar_subst ψ n φ).
Proof.
  induction φ using OPML_ind; intros; simpl in *; trivial.
  * case_match; simpl.
    - destruct decide in H. 2: by simpl in H.
      unfold update.
      destruct decide.
      + lia.
      + simpl. rewrite e.
        rewrite decide_eq_same. reflexivity.
    - subst. rewrite H1 in H.
      destruct decide. 2: by simpl in H.
      inversion e. subst.
      eapply well_sorted_weaken. 3: eassumption.
      apply default_is_strongest.
      apply default_is_strongest.
    - destruct decide. 2: by simpl in H.
      unfold update.
      destruct decide.
      + lia.
      + simpl. rewrite e.
        rewrite decide_eq_same. reflexivity.
  * erewrite IHφ1, IHφ2; try by eassumption.
    reflexivity.
    by apply andb_split_2 in H.
    by apply andb_split_1 in H.
  * apply andb_split_1 in H0 as WF1. rewrite WF1.
    clear WF1. simpl.
    apply andb_split_2 in H0.
    {
      remember (opml_arg_sorts σ) as xs.
      clear Heqxs. generalize dependent xs.
      induction H; simpl; intros. assumption.
      case_match.
      - congruence.
      - apply andb_split_1 in H3 as H31.
        apply andb_split_2 in H3.
        erewrite H, IHForall; try eassumption.
        reflexivity.
    }
  * simpl in *.
    rewrite shift_update.
    erewrite IHφ; try by eauto.
  * simpl in *.
    erewrite IHφ; try by eauto.
  * erewrite IHφ1, IHφ2; try by eassumption.
    by apply andb_split_2 in H.
    by apply andb_split_1, andb_split_2 in H.
    by apply andb_split_1, andb_split_1 in H.
Defined.

End Syntax.

Module Test.

  Inductive sorts := bool | nat.
  Inductive symbols := add | is0 | zero | succ | true | false.

  #[global]
  Instance sorts_eqdec : EqDecision sorts.
  Proof.
    solve_decision.
  Defined.

  #[global]
  Program Instance sorts_finite : Finite sorts := {
    enum := [bool; nat];
  }.
  Next Obligation.
    compute_done.
  Defined.
  Next Obligation.
    destruct x; set_solver.
  Defined.

  #[global]
  Instance symbols_eqdec : EqDecision symbols.
  Proof.
    solve_decision.
  Defined.

  #[global]
  Program Instance symbols_finite : Finite symbols := {
    enum := [add; is0; zero; succ; true; false];
  }.
  Next Obligation.
    compute_done.
  Defined.
  Next Obligation.
    destruct x; set_solver.
  Defined.

  Program Instance NatSig : OPMLSignature := {|
    opml_sorts := {|
      opml_sort := sorts;
    |};
    opml_variables := String_OPMLVariables;
    opml_symbols := {|
      opml_symbol := symbols;
      opml_arg_sorts :=
        fun x =>
          match x with
          | add => [nat; nat]
          | is0 => [nat]
          | zero => []
          | succ => [nat]
          | true => []
          | false => []
          end;
      opml_ret_sort :=
        fun x =>
          match x with
          | add => nat
          | is0 => bool
          | zero => nat
          | succ => nat
          | true => bool
          | false => bool
          end;
    |};
  |}.

  Open Scope string_scope.
  Goal
    well_sorted  default default nat (op_fevar (nat, "x")).
  Proof.
    by cbn.
  Qed.

  Goal
    well_sorted default default nat (op_ex nat (op_app succ [op_fevar (nat, "x")])).
  Proof.
    by cbn.
  Qed.

  Goal
    well_sorted default default bool (op_ex nat (op_app is0 [op_bevar 0])).
  Proof.
    by cbn.
  Qed.

End Test.

Module Semantics.
Section Semantics.
  Context {Σ : OPMLSignature}.

  Inductive hlist {A : Type} {F : A -> Type} : list A -> Type :=
  | hnil : hlist []
  | hcons {x : A} {xs : list A} : F x -> hlist xs -> hlist (x :: xs)
.

  Declare Scope opml_scope.
  Delimit Scope opml_scope with opml.
  Notation "[ ]" := hnil (format "[ ]") : opml_scope.
  Notation "[ x ]" := (hcons _ x hnil)  : opml_scope.
  Notation "[ x ; y ; .. ; z ]" := (hcons x (hcons y .. (hcons z hnil) ..))  : opml_scope.

  Program Definition test_list : @hlist bool (fun x => _) [true; false] :=
    [1; true]%opml.
  Next Obligation.
    destruct x.
    exact nat.
    exact bool.
  Defined.
  Print test_list_obligation_1.
  Check test_list.

  Program Definition test_list2 : @hlist bool (fun x => _) [true; false] :=
    [{[1]} : propset nat; {[true]} : propset bool]%opml.
  Next Obligation.
    apply propset. destruct x.
    exact nat.
    exact bool.
  Defined.
  Print test_list2_obligation_1.
  Check test_list.

  Record OPMLModel := {
    opml_carrier :> opml_sort -> Set;
    opml_app (σ : opml_symbol) :
       @hlist _ opml_carrier (opml_arg_sorts σ) -> propset (opml_carrier (opml_ret_sort σ));
    opml_inhabited (s : opml_sort) : Inhabited (opml_carrier s)
  }.

  Section with_model.

  Context {M : OPMLModel}.
  Record OPMLValuation : Type := {
    evar_valuation (x : opml_evar) : opml_carrier M (evar_sort x);
    svar_valuation (X : opml_svar) : propset (opml_carrier M (svar_sort X)) ;
  }.

  Fixpoint pointwise_elem_of {A} T ss {struct ss} :
    (* (l : @hlist A T ss)
    (lps : @hlist A (fun s => propset (T s)) ss) *)
    @hlist A T ss ->
    @hlist A (fun s => propset (T s)) ss ->
    Prop. (* := *)
  Proof.
    refine (match ss with
      | []    => fun _ _ => True
      | s::ss => fun l l' =>
        (match l in (@hlist _ _ l1)
          return (l1 = s::ss -> Prop) with
        | hnil =>
          fun (H : [] = s :: ss) => False_rect Prop ltac:(discriminate H)
        | @hcons _ _ a l0 x xs =>
          fun (H : a :: l0 = s::ss) =>
            (match l' in (@hlist _ _ l1')
               return l1' = s::ss -> Prop with
             | hnil => fun (H0 : [] = s :: ss) => False_rect Prop ltac:(discriminate H0)
             | @hcons _ _ a' l0' y ys =>
               fun (H0 : a' :: l0' = s :: ss) =>
                 x ∈ y /\ pointwise_elem_of _ _ ss _ _
             end
            ) eq_refl
        end) eq_refl
      end).
    * injection H. injection H0. intros. rewrite H4. rewrite H2.
      typeclasses eauto.
    * injection H. intros. rewrite H1 in xs. exact xs.
    * injection H0. intros. rewrite H1 in ys. exact ys.
  Defined.
  Print pointwise_elem_of.

  Goal
    pointwise_elem_of _ _
      test_list test_list2.
  Proof.
    by cbn.
  Qed.

  Definition app_ext
    (σ : opml_symbol)
    (args : @hlist _ (fun s => propset (opml_carrier M s)) (opml_arg_sorts σ))
    : propset (opml_carrier M (opml_ret_sort σ)) :=
  PropSet (
    fun e => exists (l : @hlist _ (opml_carrier M) (opml_arg_sorts σ)),
      pointwise_elem_of _ _ l args /\ e ∈ opml_app M σ l
  ).

  Fixpoint map_to_hlist {A} (F : A -> Type) (f : forall (a : A), F a) (l : list A) {struct l} : @hlist Type id (map F l).
  Proof.
    refine (
    match l return @hlist _ _ (map F l) with
    | []    => hnil
    | x::xs => let Y := map_to_hlist _ F f xs in
                hcons (f x) Y
    end
    ).
  Defined.
  Print map_to_hlist.

  Fixpoint app_map (l : list OPMLPattern)
    {ls}
    (pf : app_ws (well_sorted default default) l ls)
    (f : forall (φ :OPMLPattern) {s}
         (pf : well_sorted default default s φ)
         (psize : opml_size φ < 1 + foldr (fun φ acc => opml_size φ + acc) 0 l), propset (opml_carrier M s)) {struct l} :
    @hlist _ (fun x => propset (opml_carrier M x)) ls
    .
  Proof.
    (* refine (
    match l return  -> @hlist _ (fun x => propset (opml_carrier M x)) ls with
    | []    => _
    | x::xs => _
    end eq_refl
    ). *)
    clear app_map.
    revert ls f pf.
    induction l; intros.
    * (* nil *)
      simpl in *.
      destruct ls.
      - exact hnil.
      - congruence.
    * (* cons *)
      simpl in *.
      destruct ls.
      - congruence.
      - apply andb_split_1 in pf as pf1.
        apply andb_split_2 in pf as pf2.
        apply hcons.
        + eapply f.
          exact pf1.
          lia.
        + apply IHl.
          ** intros. eapply f. exact pf0. lia.
          ** assumption.
  Defined.

  Program Definition update_evar_val
    (ev : opml_evar)
    (x : opml_carrier M (evar_sort ev))
    (val : OPMLValuation) : OPMLValuation :=
    {|
    evar_valuation := fun ev' : opml_evar => _;
      (* if decide (ev = ev')
      then x
      else evar_valuation val ev' ; *)
    svar_valuation := (svar_valuation val)
    |}.
  Next Obligation.
    destruct (decide (ev = ev')).
    * rewrite -e. exact x.
    * exact (evar_valuation val ev').
  Defined.

  Program Definition update_svar_val
    (sv : opml_svar)
    (X : propset (opml_carrier M (svar_sort sv)))
    (val : OPMLValuation) : OPMLValuation :=
    {|
    evar_valuation := (evar_valuation val);
    svar_valuation := fun sv' : opml_svar =>
      if decide (sv = sv') is left _ then _ else svar_valuation val sv' ;
    |}.
  Next Obligation.
    exact X.
  Defined.

  Require Import Coq.Program.Equality.

  (* Oké-e ha a nem well-sorted dolgoknak valami default értéket
     adjunk, és így elhagyjuk a well-sorted judgementet (Hws-t) *)
  Equations? opml_eval (ρ : OPMLValuation) (φ : OPMLPattern) {s}
    (Hws : well_sorted default default s φ)
      : propset (opml_carrier M s) by wf (opml_size φ) :=
    opml_eval ρ (op_fevar x) pf    := _ ;
    opml_eval ρ (op_fsvar X) pf    := _;
    opml_eval ρ (op_bevar x) pf    := ∅ ;
    opml_eval ρ (op_bsvar x) pf    := ∅ ;
    opml_eval ρ op_bot       pf    := ∅ ;
    opml_eval ρ (op_app σ args) pf := _;
    opml_eval ρ (op_imp φ1 φ2)  pf := (⊤ ∖ (opml_eval ρ φ1 _)) ∪ (opml_eval ρ φ2 _);
    opml_eval ρ (op_eq s1 s2 φ1 φ2) pf := _;
    opml_eval ρ (op_ex s0 φ)    pf := _;
    opml_eval ρ (op_mu s0 φ)    pf := _.
    Proof.
      * (* op_fevar *)
        epose {[ evar_valuation ρ x ]} as d.
        exact d.
        Unshelve.
        destruct decide.
        - rewrite e. typeclasses eauto.
        - simpl in pf. congruence.
      * (* op_fsvar *)
        epose (svar_valuation ρ X) as d.
        destruct decide.
        - rewrite <- e. exact d.
        - simpl in pf. congruence.
      * (* op_imp *)
        by apply andb_split_1 in pf.
      * lia.
      * (* op_imp *)
        by apply andb_split_2 in pf.
      * lia.
      * (* op_app *)
        apply andb_split_1 in pf as pf1.
        apply andb_split_2 in pf as pf2.
        pose (app_ext σ (app_map args pf2 (opml_eval ρ))) as X.
        destruct decide.
        rewrite e. exact X.
        inversion pf1.
      * (* op_eq *)
        apply andb_split_1 in pf as pf1.
        apply andb_split_1 in pf1 as pf0.
        apply andb_split_2 in pf1 as pf2. clear pf1.
        rename pf0 into pf1.
        apply andb_split_2 in pf as pf3. clear pf.
        destruct decide. 2: { simpl in *. congruence. }
        epose (X1 := opml_eval ρ φ1 s1 pf1 _).
        epose (X2 := opml_eval ρ φ2 s1 pf2 _).
        exact (PropSet (fun e => X1 = X2)).
        Unshelve.
        all: lia.
      * (* op_ex *)
        eapply (propset_fa_union (
          fun c : opml_carrier M s0 =>
            let newx := fresh_evar s0 φ in
            opml_eval (update_evar_val (projT1 newx) _ ρ)
                      (bevar_subst (op_fevar (projT1 newx)) 0 φ)
                      _ _ _
        )).
        Unshelve.
        - pose proof (projT2 newx) as Is. simpl in Is.
          destruct decide. 2: simpl in Is; congruence.
          rewrite e. exact c.
        - eapply (well_sorted_bevar_subst _ (op_fevar (projT1 newx)) s s0 _ _ 0) in pf.
          3: reflexivity.
          2: { cbn. exact (projT2 newx). }
          clear -pf.
          assert (update 0 None (shift default (Some s0)) = default). {
            unfold update, shift.
            extensionality x. destruct x; simpl.
            reflexivity.
            reflexivity.
          }
          rewrite H in pf.
          exact pf.
        - rewrite bevar_subst_opml_size. lia.
      * (* op_mu *)
        exact ∅.
    Defined.
  Print opml_eval.

  Definition satM φ s (ws : well_sorted default default s φ) :=
    forall ρ, opml_eval ρ φ ws = ⊤.
  Definition Theory := propset OPMLPattern.
    (* dependent pairs are not well-supported by stdpp *)
  Definition satT (Γ : Theory) :=
    forall p, p ∈ Γ ->
      exists s, { pf : well_sorted default default s p & satM p s pf }.

  Import PropExtensionality.
  #[export]
  Instance propset_leibniz_equiv A : LeibnizEquiv (propset A).
  Proof.
    intros x y H. unfold equiv in H. unfold set_equiv_instance in H.
    destruct x,y.
    apply f_equal. apply functional_extensionality.
    intros x. apply propositional_extensionality.
    specialize (H x). destruct H as [H1 H2].
    split; auto.
  Qed.

  Fixpoint HForall {J} {A : J -> Type}
    (P : ∀ j, A j -> Prop)
    {js : list J} (v : @hlist J A js) {struct v} : Prop :=
    match v with
    | hnil => True
    | hcons x xs => P _ x ∧ HForall P xs
    end.

  Fixpoint HBiForall {J1 J2} {A1 : J1 -> Type} {A2 : J2 -> Type}
    (P : ∀ j1 j2, A1 j1 -> A2 j2 -> Prop)
    {js1 : list J1}
    {js2 : list J2}
    (v1 : @hlist J1 A1 js1) (v2 : @hlist J2 A2 js2)
      {struct v1} : Prop :=
    match v1, v2 with
    | hnil, hnil => True
    | hcons x xs, hcons y ys => P _ _ x y ∧ HBiForall P xs ys
    | _, _ => False
    end.

  Fixpoint hmap {J} {A B : J -> Type}
    (f : ∀ j, A j -> B j)
    {js : list J} (v : @hlist J A js) : @hlist J B js :=
  match v with
  | hnil => hnil
  | hcons x xs => hcons (f _ x) (hmap f xs)
  end.

End with_model.
End Semantics.
End Semantics.

Module TestSemantics.
  Import Test.
  Import Semantics.

  Definition nat_carrier (x : sorts) :=
  match x with
  | bool => Datatypes.bool
  | nat => Datatypes.nat
  end.

  Program Definition nat_app
    (σ : symbols)
    (l : @hlist _ nat_carrier (opml_arg_sorts σ))
    : propset (nat_carrier (opml_ret_sort σ)) :=
  match σ as s with
  | add  => _
  | is0  => _
  | zero => {[0]}
  | succ => _
  | true => {[Datatypes.true]}
  | false => {[Datatypes.false]}
  end.
  Next Obligation.
    inversion l; subst.
    inversion X; subst.
    simpl in *.
    exact {[H0 + H1]}.
  Defined.
  Next Obligation.
    inversion l.
    subst.
    simpl in H0.
    exact {[match H0 with
            | O => Datatypes.true
            | _ => Datatypes.false
            end ]}.
  Defined.
  Next Obligation.
    inversion l. subst.
    simpl in *.
    exact {[S H0]}.
  Defined.

  Program Definition NatModel : OPMLModel := {|
    opml_carrier := nat_carrier;
    opml_app := nat_app;
  |}.
  Next Obligation.
    destruct s; simpl; repeat constructor.
  Defined.

  Definition op_not (φ : OPMLPattern) :=
    op_imp φ op_bot.
  Definition op_all (s0 : opml_sort) (φ : OPMLPattern) :=
    op_not (op_ex s0 (op_not φ)).

  Definition NatTheory : Theory :=
  {[
    op_eq bool nat (op_app is0 [op_app zero []]) (op_app true []);
    op_all nat (op_eq bool nat (op_app is0 [op_app succ [op_bevar 0]]) (op_app false []))
  ]}.

  Require Import Coq.Program.Equality.

  Goal
    @satT _ NatModel NatTheory.
  Proof.
    unfold satT.
    intros.
    unfold NatTheory in *.
    apply elem_of_union in H as [|].
    {
      apply elem_of_singleton in H. subst.
      exists nat.
      simpl.
      eapply existT.
      Unshelve.
      2: reflexivity.
      unfold satM.
      intros.
      simp opml_eval.
      simpl. cbn.
      unfold opml_eval_obligation_8.
      simpl. cbn.
      simp opml_eval.
      unfold opml_eval_obligation_7.
      cbn.
      unfold decide. (* simpl never - this should be unfolded manually *)
      simpl. cbn.
      (* set_eq does not work for some reason *)
      apply set_eq.
      intros. split. set_solver.
      intro. apply elem_of_PropSet.
      unfold app_ext.
      apply set_eq.
      split; intro X; apply elem_of_PropSet; destruct X as [c [X1 X2]].
      * simpl in c. dependent destruction c. dependent destruction c.
        simpl in X1. destruct X1 as [X1 _].
        simp opml_eval in X1. unfold opml_eval_obligation_7 in X1.
        cbn in X1. unfold decide in X1. simpl in X1. cbn in X1.
        unfold app_ext in X1.
        destruct X1 as [? [? ?]]. cbn in H0.
        simpl in H1. apply elem_of_singleton in H1. subst.
        exists hnil. simpl; split; set_solver.
      * simpl in c. dependent destruction c.
        simpl in X2. apply elem_of_singleton in X2. subst.
        simpl.
        eexists (hcons _ hnil). Unshelve. 2: exact 0.
        (* for some reason, if 0 is put into _, we get a type error *)
        simpl. split.
        - simp opml_eval. unfold opml_eval_obligation_7. unfold decide.
          simpl. cbn. split. 2: auto.
          unfold app_ext. apply elem_of_PropSet.
          exists hnil.
          simpl. split. auto.
          apply elem_of_singleton. reflexivity.
        - cbn. set_solver.
     }
     {
       apply elem_of_singleton in H. subst.
       exists nat.
       simpl.
       eapply existT.
       Unshelve.
       2: reflexivity.
       unfold satM.
       intros. unfold op_all, op_not.
       simp opml_eval.
       unfold opml_eval_obligation_9.
       rewrite union_empty_r_L.
       apply complement_full_iff_empty.
       apply propset_fa_union_empty.
       intros.
       simpl. simp opml_eval.

       (* NOTE: this works very poorly in a dependently-typed setting:
          remember (fresh_evar _ _) as x.

       (* Some magic happens here that I don't understand *)
       dependent inversion x.
       simpl. simpl in i.
       rewrite i.
       unfold is_true, is_left in i. simpl.
       dependent destruction i; simpl in *. *)
       simp opml_eval.
       unfold opml_eval_obligation_8, decide. simpl.
       rewrite union_empty_r_L.
       apply complement_empty_iff_full.
       simp opml_eval. unfold opml_eval_obligation_7, decide. simpl. cbn.
       simp opml_eval. unfold opml_eval_obligation_7, decide. simpl. cbn.
       simp opml_eval. unfold opml_eval_obligation_1.
       simpl. unfold Semantics.update_evar_val_obligation_1.
       destruct decide. 2: congruence.
       simpl. unfold eq_rect.
       (* again, some magic *)
       dependent destruction e.
       apply set_eq.
       intros. split. set_solver.
       intro. apply elem_of_PropSet.
       unfold app_ext.
       apply set_eq.
       split; intro X; apply elem_of_PropSet; destruct X as [c0 [X1 X2]].
       * simpl in X1. do 2 dependent destruction c0.
         destruct X1 as [X1 _].
         destruct X1 as [pars X1].
         do 2 dependent destruction pars.
         cbn in *.
         decompose [and] X1. clear X1.
         apply elem_of_singleton in H1. subst.
         apply elem_of_singleton in H2. subst.
         apply elem_of_singleton in X2. subst.
         exists hnil. set_solver.
       * simpl in *. apply elem_of_singleton in X2. subst.
         eexists (hcons _ hnil); simpl; cbn.
         Unshelve. 2: exact (S c).
         simpl. split; try split. 2: set_solver.
         apply elem_of_PropSet.
         eexists (hcons _ hnil); simpl; cbn.
         Unshelve. 2: exact c. set_solver.
     }
  Qed.

(* sort inference + well_sortedness? *)

End TestSemantics.
