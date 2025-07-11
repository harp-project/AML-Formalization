From Coq Require Import Btauto.

From MatchingLogic Require Export
    Signature
    extralibrary
    stdpp_ext.


(* TODO have different type for element variable and for set variable index *)
Definition db_index := nat.

(* begin snippet Pattern *)
Inductive Pattern {Σ : Signature} : Set :=
| patt_free_evar (x : evar)
| patt_free_svar (x : svar)
| patt_bound_evar (n : db_index)
| patt_bound_svar (n : db_index)
| patt_sym (sigma : symbols) :  Pattern
| patt_app (phi1 phi2 : Pattern)
| patt_bott
| patt_imp (phi1 phi2 : Pattern)
| patt_exists (phi : Pattern)
| patt_mu (phi : Pattern)
.
(* end snippet Pattern *)

Global
Instance Pattern_eqdec {Σ : Signature} : EqDecision Pattern.
Proof. solve_decision. Defined.

Global Instance Pattern_countable {Σ : Signature} (sc : Countable symbols) : Countable Pattern.
Proof.
  set (enc :=
         fix go p : gen_tree (unit
                              + ((@symbols (@ml_symbols Σ))
                                 + (((@evar variables) + db_index)
                                    + ((@svar variables) + db_index))))%type :=
           match p with
           | patt_bott => GenLeaf (inl ())
           | patt_sym s => GenLeaf (inr (inl s))
           | patt_free_evar x => GenLeaf (inr (inr (inl (inl x))))
           | patt_free_svar X => GenLeaf (inr (inr (inr (inl X))))
           | patt_bound_evar n => GenLeaf (inr (inr (inl (inr n))))
           | patt_bound_svar n => GenLeaf (inr (inr (inr (inr n))))
           | patt_app p1 p2 => GenNode 0 [go p1; go p2]
           | patt_imp p1 p2 => GenNode 1 [go p1; go p2]
           | patt_exists p' => GenNode 2 [go p']
           | patt_mu p' => GenNode 3 [go p']
           end
      ).

  set (dec :=
         fix go (p : gen_tree (unit
                              + ((@symbols (@ml_symbols Σ))
                                 + (((@evar variables) + db_index)
                                    + ((@svar variables) + db_index))))%type) : Pattern :=
           match p with
           | GenLeaf (inl ()) => patt_bott
           | GenLeaf (inr (inl s)) => patt_sym s
           | GenLeaf (inr (inr (inl (inl x)))) => patt_free_evar x
           | GenLeaf (inr (inr (inr (inl X)))) => patt_free_svar X
           | GenLeaf (inr (inr (inl (inr n)))) => patt_bound_evar n
           | GenLeaf (inr (inr (inr (inr n)))) => patt_bound_svar n
           | GenNode 0 [p1; p2] => patt_app (go p1) (go p2)
           | GenNode 1 [p1; p2] => patt_imp (go p1) (go p2)
           | GenNode 2 [p'] => patt_exists (go p')
           | GenNode 3 [p'] => patt_mu (go p')
           | _ => patt_bott (* dummy *)
           end
      ).

  refine (inj_countable' enc dec _).
  intros x.
  induction x; simpl; congruence.
Defined.

Fixpoint count_binders
  {Σ : Signature}
  (ϕ : Pattern)
  : nat :=
  match ϕ with
  | patt_free_evar _ => 0
  | patt_free_svar _ => 0
  | patt_bound_evar _ => 0
  | patt_bound_svar _ => 0
  | patt_sym _ => 0
  | patt_bott => 0
  | patt_imp ϕ₁ ϕ₂ =>
    count_binders ϕ₁ +
    count_binders ϕ₂
  | patt_app ϕ₁ ϕ₂ =>
    count_binders ϕ₁ +
    count_binders ϕ₂
  | patt_exists ϕ' =>
    S (count_binders ϕ')
  | patt_mu ϕ' =>
    S (count_binders ϕ')
  end
.

Definition Theory {Σ : Signature} := propset Pattern.

Section syntax.
  Context {Σ : Signature}.

  Fixpoint pat_size (p : Pattern) : nat :=
      match p with
      | patt_app ls rs => 1 + (pat_size ls) + (pat_size rs)
      | patt_imp ls rs => 1 + (pat_size ls) + (pat_size rs)
      | patt_exists p' => 1 + pat_size p'
      | patt_mu p' => 1 + pat_size p'
      | _ => 1
      end.

(*   Global Instance PatternSize : Size Pattern := {
    size := pat_size;
  }. *)

(*   Arguments PatternSize /. *)

  (** The free names of a type are defined as follow.  Notice the
  [exists] and [mu] cases: they do not bind any name. *)

  Definition EVarSet := gset evar.
  Definition SVarSet := gset svar.

  Fixpoint free_evars (phi : Pattern)
    : EVarSet :=
    match phi with
    | patt_free_evar x => singleton x
    | patt_free_svar X => empty
    | patt_bound_evar x => empty
    | patt_bound_svar X => empty
    | patt_sym sigma => empty
    | patt_app phi1 phi2 => union (free_evars phi1) (free_evars phi2)
    | patt_bott => empty
    | patt_imp phi1 phi2 => union (free_evars phi1) (free_evars phi2)
    | patt_exists phi => free_evars phi
    | patt_mu phi => free_evars phi
    end.

  Fixpoint free_svars (phi : Pattern)
    : SVarSet :=
    match phi with
    | patt_free_evar x => empty
    | patt_free_svar X => singleton X
    | patt_bound_evar x => empty
    | patt_bound_svar X => empty
    | patt_sym sigma => empty
    | patt_app phi1 phi2 => union (free_svars phi1) (free_svars phi2)
    | patt_bott => empty
    | patt_imp phi1 phi2 => union (free_svars phi1) (free_svars phi2)
    | patt_exists phi => free_svars phi
    | patt_mu phi => free_svars phi
    end.

  Definition free_evars_of_list (l : list Pattern) : EVarSet :=
    union_list (map free_evars l).

  Lemma free_evars_of_list_foldr :
    forall l g,
      free_evars (foldr patt_imp g l) =
      free_evars g ∪ free_evars_of_list l.
  Proof.
    induction l; intro g; set_solver.
  Qed.

  (* for bound set variables *)
  Fixpoint no_negative_occurrence_db_b (dbi : db_index) (ϕ : Pattern) : bool :=
    match ϕ with
    | patt_free_evar _ | patt_free_svar _ | patt_bound_evar _ | patt_sym _ | patt_bott => true
    | patt_bound_svar n => true
    | patt_app ϕ₁ ϕ₂ => no_negative_occurrence_db_b dbi ϕ₁ && no_negative_occurrence_db_b dbi ϕ₂
    | patt_imp ϕ₁ ϕ₂ => no_positive_occurrence_db_b dbi ϕ₁ && no_negative_occurrence_db_b dbi ϕ₂
    | patt_exists ϕ' => no_negative_occurrence_db_b dbi ϕ'
    | patt_mu ϕ' => no_negative_occurrence_db_b (S dbi) ϕ'
    end
  with
  no_positive_occurrence_db_b (dbi : db_index) (ϕ : Pattern) : bool :=
    match ϕ with
    | patt_free_evar _ | patt_free_svar _ | patt_bound_evar _ | patt_sym _ | patt_bott => true
    | patt_bound_svar n => if decide (n = dbi) is left _ then false else true
    | patt_app ϕ₁ ϕ₂ => no_positive_occurrence_db_b dbi ϕ₁ && no_positive_occurrence_db_b dbi ϕ₂
    | patt_imp ϕ₁ ϕ₂ => no_negative_occurrence_db_b dbi ϕ₁ && no_positive_occurrence_db_b dbi ϕ₂
    | patt_exists ϕ' => no_positive_occurrence_db_b dbi ϕ'
    | patt_mu ϕ' => no_positive_occurrence_db_b (S dbi) ϕ'                                  
    end.

  (* for free element variables *)
  Fixpoint evar_has_positive_occurrence (x : evar) (ϕ : Pattern) : bool :=
    match ϕ with
    | patt_free_evar x' => if decide (x = x') is left _ then true else false
    | patt_free_svar _ | patt_bound_evar _ | patt_bound_svar _ | patt_sym _ | patt_bott => false
    | patt_app ϕ₁ ϕ₂ => evar_has_positive_occurrence x ϕ₁ || evar_has_positive_occurrence x ϕ₂
    | patt_imp ϕ₁ ϕ₂ => evar_has_negative_occurrence x ϕ₁ || evar_has_positive_occurrence x ϕ₂
    | patt_exists ϕ' => evar_has_positive_occurrence x ϕ'
    | patt_mu ϕ' => evar_has_positive_occurrence x ϕ'
    end
  with
  evar_has_negative_occurrence (x : evar) (ϕ : Pattern) : bool :=
    match ϕ with
    | patt_free_evar _ | patt_free_svar _ | patt_bound_evar _ | patt_bound_svar _ | patt_sym _ | patt_bott => false
    | patt_app ϕ₁ ϕ₂ => evar_has_negative_occurrence x ϕ₁ || evar_has_negative_occurrence x ϕ₂
    | patt_imp ϕ₁ ϕ₂ => evar_has_positive_occurrence x ϕ₁ || evar_has_negative_occurrence x ϕ₂
    | patt_exists ϕ' => evar_has_negative_occurrence x ϕ'
    | patt_mu ϕ' => evar_has_negative_occurrence x ϕ'
    end.

  (* for free set variables *)
  Fixpoint svar_has_positive_occurrence (X : svar) (ϕ : Pattern) : bool :=
    match ϕ with
    | patt_free_svar X' => if decide (X = X') is left _ then true else false
    | patt_free_evar _ | patt_bound_evar _ | patt_bound_svar _ | patt_sym _ | patt_bott => false
    | patt_app ϕ₁ ϕ₂ => svar_has_positive_occurrence X ϕ₁ || svar_has_positive_occurrence X ϕ₂
    | patt_imp ϕ₁ ϕ₂ => svar_has_negative_occurrence X ϕ₁ || svar_has_positive_occurrence X ϕ₂
    | patt_exists ϕ' => svar_has_positive_occurrence X ϕ'
    | patt_mu ϕ' => svar_has_positive_occurrence X ϕ'
    end
  with
  svar_has_negative_occurrence (X : svar) (ϕ : Pattern) : bool :=
    match ϕ with
    | patt_free_evar _ | patt_free_svar _ | patt_bound_evar _ | patt_bound_svar _ | patt_sym _ | patt_bott => false
    | patt_app ϕ₁ ϕ₂ => svar_has_negative_occurrence X ϕ₁ || svar_has_negative_occurrence X ϕ₂
    | patt_imp ϕ₁ ϕ₂ => svar_has_positive_occurrence X ϕ₁ || svar_has_negative_occurrence X ϕ₂
    | patt_exists ϕ' => svar_has_negative_occurrence X ϕ'
    | patt_mu ϕ' => svar_has_negative_occurrence X ϕ'
    end.

  Fixpoint well_formed_positive (phi : Pattern) : bool :=
    match phi with
    | patt_free_evar _ => true
    | patt_free_svar _ => true
    | patt_bound_evar _ => true
    | patt_bound_svar _ => true
    | patt_sym _ => true
    | patt_app psi1 psi2 => well_formed_positive psi1 && well_formed_positive psi2
    | patt_bott => true
    | patt_imp psi1 psi2 => well_formed_positive psi1 && well_formed_positive psi2
    | patt_exists psi => well_formed_positive psi
    | patt_mu psi => no_negative_occurrence_db_b 0 psi && well_formed_positive psi
    end.

  Fixpoint well_formed_closed_mu_aux (phi : Pattern) (max_ind_svar : db_index) : bool :=
    match phi with
    | patt_free_evar _ => true
    | patt_free_svar _ => true
    | patt_bound_evar n => true
    | patt_bound_svar n => if decide (n < max_ind_svar) is left _ then true else false
    | patt_sym _ => true
    | patt_app psi1 psi2 => well_formed_closed_mu_aux psi1 max_ind_svar &&
                            well_formed_closed_mu_aux psi2 max_ind_svar
    | patt_bott => true
    | patt_imp psi1 psi2 => well_formed_closed_mu_aux psi1 max_ind_svar &&
                            well_formed_closed_mu_aux psi2 max_ind_svar
    | patt_exists psi => well_formed_closed_mu_aux psi max_ind_svar
    | patt_mu psi => well_formed_closed_mu_aux psi (S max_ind_svar)
    end.

  Fixpoint well_formed_closed_ex_aux (phi : Pattern) (max_ind_evar : db_index) : bool :=
    match phi with
    | patt_free_evar _ => true
    | patt_free_svar _ => true
    | patt_bound_evar n => if decide (n < max_ind_evar) is left _ then true else false
    | patt_bound_svar n => true
    | patt_sym _ => true
    | patt_app psi1 psi2 => well_formed_closed_ex_aux psi1 max_ind_evar &&
                            well_formed_closed_ex_aux psi2 max_ind_evar
    | patt_bott => true
    | patt_imp psi1 psi2 => well_formed_closed_ex_aux psi1 max_ind_evar &&
                            well_formed_closed_ex_aux psi2 max_ind_evar
    | patt_exists psi => well_formed_closed_ex_aux psi (S max_ind_evar)
    | patt_mu psi => well_formed_closed_ex_aux psi max_ind_evar
    end.

  Definition well_formed_closed (phi : Pattern) : bool
    := well_formed_closed_mu_aux phi 0 && well_formed_closed_ex_aux phi 0.

  Lemma well_formed_closed_ex_aux_ind (phi : Pattern) (ind_evar1 ind_evar2 : db_index) :
    ind_evar1 <= ind_evar2 ->
    well_formed_closed_ex_aux phi ind_evar1 = true->
    well_formed_closed_ex_aux phi ind_evar2 = true.
  Proof.
    intros H H0.
    generalize dependent ind_evar1. generalize dependent ind_evar2.
    induction phi; intros ind_evar_2 ind_evar_1 Heqevar H;
      simpl in *; repeat case_match; try (naive_bsolver lia); auto.
    eapply IHphi. 2: eassumption. lia.
  Qed.

  Lemma well_formed_closed_mu_aux_ind (phi : Pattern) (ind_svar1 ind_svar2 : db_index) :
    ind_svar1 <= ind_svar2  ->
    well_formed_closed_mu_aux phi ind_svar1 = true ->
    well_formed_closed_mu_aux phi ind_svar2 = true.
  Proof.
    intros H H1.
    generalize dependent ind_svar1. generalize dependent ind_svar2.
    induction phi; intros ind_svar_2 ind_svar_1 Hleqsvar;
      simpl in *; repeat case_match; try (naive_bsolver lia); auto.
    eapply IHphi. lia.
  Qed.
  
  Definition well_formed (phi : Pattern) := well_formed_positive phi && well_formed_closed phi.



  Lemma well_formed_bott:
    well_formed patt_bott.
  Proof. reflexivity. Qed.

  Lemma well_formed_sym s:
    well_formed (patt_sym s).
  Proof. reflexivity. Qed.

Lemma well_formed_imp ϕ₁ ϕ₂:
  well_formed ϕ₁ = true ->
  well_formed ϕ₂ = true ->
  well_formed (patt_imp ϕ₁ ϕ₂) = true.
Proof.
  unfold well_formed. unfold well_formed_closed. simpl.
  intros H1 H2.
  naive_bsolver.
Qed.

Lemma well_formed_app ϕ₁ ϕ₂:
  well_formed ϕ₁ = true ->
  well_formed ϕ₂ = true ->
  well_formed (patt_app ϕ₁ ϕ₂) = true.
Proof.
  unfold well_formed,well_formed_closed.
  naive_bsolver.
Qed.

Lemma well_formed_ex_app ϕ₁ ϕ₂:
  well_formed (patt_exists ϕ₁) = true ->
  well_formed (patt_exists ϕ₂) = true ->
  well_formed (patt_exists (patt_app ϕ₁ ϕ₂)) = true.
Proof.
  unfold well_formed,well_formed_closed.
  naive_bsolver.
Qed.

Lemma well_formed_impl_well_formed_ex ϕ:
  well_formed ϕ = true ->
  well_formed (patt_exists ϕ) = true.
Proof.
  unfold well_formed,well_formed_closed.
  intros. destruct_andb!. simpl.
  eapply well_formed_closed_ex_aux_ind with (ind_evar2 := 1) in H2. 2: lia.
  naive_bsolver.
Qed.


  (* TODO: why is this Private? It can be useful for not only 0 dbi *)
  Lemma Private_wfc_impl_no_neg_pos_occ psi maxsvar dbi:
    well_formed_closed_mu_aux psi maxsvar = true ->
    maxsvar <= dbi ->
    no_negative_occurrence_db_b dbi psi = true
    /\ no_positive_occurrence_db_b dbi psi = true.
  Proof.
    move: dbi maxsvar.
    induction psi; intros dbi maxsvar Hwfc Hleq; simpl; auto; cbn.
    - split.
      { auto. }
      simpl in Hwfc.
      unfold no_positive_occurrence_db_b.
      repeat case_match; auto.
      subst. lia.
    - split.
      + simpl in Hwfc.
        destruct_andb!.
        unfold no_negative_occurrence_db_b.
        naive_bsolver auto.
      + simpl in Hwfc.
        destruct_andb!.
        unfold no_positive_occurrence_db_b.
        naive_bsolver auto.
    - split.
      + simpl in Hwfc.
        destruct_andb!. naive_bsolver auto.
      + simpl in Hwfc.
        destruct_andb!. naive_bsolver auto.
    - simpl in Hwfc.
      naive_bsolver auto.
    - simpl in Hwfc.
      eapply IHpsi.
      1: eassumption. lia.
  Qed.

  Corollary wfc_impl_no_neg_occ psi dbi:
    well_formed_closed_mu_aux psi 0 = true ->
    no_negative_occurrence_db_b dbi psi = true.
  Proof.
    intros H.
    unfold well_formed_closed in H.
    pose proof (HX := Private_wfc_impl_no_neg_pos_occ).
    specialize (HX psi 0 dbi H).
    simpl in HX.
    specialize (HX ltac:(lia)).
    destruct HX as [HX1 HX2].
    apply HX1.
  Qed.

  Corollary wfc_impl_no_pos_occ psi dbi:
    well_formed_closed_mu_aux psi 0 = true ->
    no_positive_occurrence_db_b dbi psi = true.
  Proof.
    intros H.
    unfold well_formed_closed in H.
    pose proof (HX := Private_wfc_impl_no_neg_pos_occ).
    specialize (HX psi 0 dbi H).
    simpl in HX.
    specialize (HX ltac:(lia)).
    destruct HX as [HX1 HX2].
    apply HX2.
  Qed.



  Lemma well_formed_app_1 : forall (phi1 phi2 : Pattern),
      well_formed (patt_app phi1 phi2) -> well_formed phi1.
  Proof.
    unfold well_formed. simpl. intros phi1 phi2 H.
    apply andb_true_iff in H as [Hpos Hclos].
    apply andb_true_iff in Hclos as [Hcl1 Hcl2]. simpl in Hcl1, Hcl2.
    apply andb_true_iff in Hpos as [Hpos1 Hpos2].
    apply andb_true_iff in Hcl1 as [Hcl11 Hcl12].
    apply andb_true_iff in Hcl2 as [Hcl21 Hcl22].
    rewrite -> Hpos1. unfold well_formed_closed. simpl.
    now rewrite -> Hcl11, -> Hcl21.
  Qed.

  Lemma well_formed_app_2 : forall (phi1 phi2 : Pattern),
      well_formed (patt_app phi1 phi2) -> well_formed phi2.
  Proof.
    unfold well_formed. simpl. intros phi1 phi2 H.
    apply andb_true_iff in H as [Hpos Hclos].
    apply andb_true_iff in Hclos as [Hcl1 Hcl2]. simpl in Hcl1, Hcl2.
    apply andb_true_iff in Hpos as [Hpos1 Hpos2].
    apply andb_true_iff in Hcl1 as [Hcl11 Hcl12].
    apply andb_true_iff in Hcl2 as [Hcl21 Hcl22].
    rewrite -> Hpos2. unfold well_formed_closed. simpl.
    now rewrite -> Hcl12, -> Hcl22.
  Qed.

  Lemma free_svars_exists : forall (ϕ : Pattern),
    free_svars (patt_exists ϕ) = free_svars ϕ.
  Proof. done. Qed.

  Lemma wfc_impl_no_neg_pos_occ p m:
    well_formed_closed_mu_aux p m ->
    (no_negative_occurrence_db_b m p && no_positive_occurrence_db_b m p) = true.
  Proof.
    intros H.
    move: m H.
    induction p; intros m H; simpl; simpl in H; cbn; auto.
    - repeat case_match; try reflexivity; try lia. congruence.
    - apply andb_prop in H. destruct H as [H1 H2].
      specialize (IHp1 m H1). specialize (IHp2 m H2).
      naive_bsolver.
    - apply andb_prop in H. destruct H as [H1 H2].
      specialize (IHp1 m H1). specialize (IHp2 m H2).
      naive_bsolver.
  Qed.

    
  Fixpoint mu_free (p : Pattern) : bool :=
  match p with
   | patt_free_evar x => true
   | patt_free_svar x => true
   | patt_bound_evar n => true
   | patt_bound_svar n => true
   | patt_sym sigma => true
   | patt_app phi1 phi2 => mu_free phi1 && mu_free phi2
   | patt_bott => true
   | patt_imp phi1 phi2 => mu_free phi1 && mu_free phi2
   | patt_exists phi => mu_free phi
   | patt_mu phi => false
  end.

  (* Fragment of matching logic without set variables and mu *)
  Fixpoint set_free (p : Pattern) : bool :=
  match p with
   | patt_free_evar x => true
   | patt_free_svar x => false
   | patt_bound_evar n => true
   | patt_bound_svar n => false
   | patt_sym sigma => true
   | patt_app phi1 phi2 => set_free phi1 && set_free phi2
   | patt_bott => true
   | patt_imp phi1 phi2 => set_free phi1 && set_free phi2
   | patt_exists phi => set_free phi
   | patt_mu phi => false
  end.

  Lemma set_free_implies_mu_free p:
    set_free p = true -> mu_free p = true.
  Proof.
    intros H.
    induction p; simpl in *; destruct_and?; split_and?; auto.
    all: naive_bsolver.
  Qed.


  Theorem mu_free_wfp φ :
    mu_free φ -> well_formed_positive φ.
  Proof.
    induction φ; intros Hmf; simpl; auto.
    all: simpl in Hmf; naive_bsolver.
  Qed.


  Lemma wf_imp_wfc ϕ:
    well_formed ϕ -> well_formed_closed ϕ.
  Proof.
    intros H. apply andb_prop in H. tauto.
  Qed.


  Definition evar_is_fresh_in x ϕ := x ∉ free_evars ϕ.
  Definition svar_is_fresh_in x ϕ := x ∉ free_svars ϕ.

  (** This function is used for linear contexts *)
  Fixpoint count_evar_occurrences (x : evar) (p : Pattern) :=
    match p with
    | patt_free_evar x' => if decide (x' = x) is left _ then 1 else 0 
    | patt_free_svar _ => 0
    | patt_bound_evar _ => 0
    | patt_bound_svar _ => 0
    | patt_sym _ => 0
    | patt_app phi1 phi2 => count_evar_occurrences x phi1 + count_evar_occurrences x phi2 
    | patt_bott => 0
    | patt_imp phi1 phi2 => count_evar_occurrences x phi1 + count_evar_occurrences x phi2 
    | patt_exists phi' => count_evar_occurrences x phi'
    | patt_mu phi' => count_evar_occurrences x phi'
    end.

  Lemma count_evar_occurrences_0 (x : evar) (p : Pattern) :
    x ∉ free_evars p <->
    count_evar_occurrences x p = 0.
  Proof.
    split.
    {
    intros H.
    induction p; simpl in H; simpl; auto.
    - apply not_elem_of_singleton_1 in H.
      destruct (decide (x0 = x)). subst. contradiction. reflexivity.
    - apply not_elem_of_union in H. destruct H as [H1 H2].
      rewrite IHp1; [assumption|].
      rewrite IHp2; [assumption|].
      reflexivity.
    - apply not_elem_of_union in H. destruct H as [H1 H2].
      rewrite IHp1; [assumption|].
      rewrite IHp2; [assumption|].
      reflexivity.
    }
    {
      intros H.
      induction p; simpl in H; simpl; auto.
      2-5, 7: set_solver.
      - destruct (decide (x0 = x)); set_solver.
      - rewrite Nat.eq_add_0 in H.
        destruct H as [H0 H1]. set_solver.
      - rewrite Nat.eq_add_0 in H.
        destruct H as [H0 H1]. set_solver.
    }
  Qed.

  Lemma count_evar_occurrences_not_0 (x : evar) (p : Pattern) :
    x ∈ free_evars p <->
    count_evar_occurrences x p > 0.
  Proof.
    split.
    {
    intros H.
    induction p; simpl in H; simpl; auto.
    2-5, 7: set_solver.
    - destruct decide. lia. set_solver.
    - apply elem_of_union in H as [H | H].
      + apply IHp1 in H. lia.
      + apply IHp2 in H. lia.
    - apply elem_of_union in H as [H | H].
      + apply IHp1 in H. lia.
      + apply IHp2 in H. lia.
    }
    {
      intros H.
      induction p; simpl in H; simpl; auto.
      2-5, 7: lia.
      - destruct (decide (x0 = x)). set_solver. lia.
      - assert (count_evar_occurrences x p1 > 0 ∨ count_evar_occurrences x p2 > 0) by lia.
        set_solver.
      - assert (count_evar_occurrences x p1 > 0 ∨ count_evar_occurrences x p2 > 0) by lia.
      set_solver.
    }
  Qed.

End syntax.


Lemma well_formed_app_proj1 {Σ : Signature} p q:
  well_formed (patt_app p q) ->
  well_formed p.
Proof.
  intros H.
  unfold well_formed,well_formed_closed in *. simpl in *.
  naive_bsolver.
Qed.

Lemma well_formed_app_proj2 {Σ : Signature} p q:
  well_formed (patt_app p q) ->
  well_formed q.
Proof.
  intros H.
  unfold well_formed,well_formed_closed in *. simpl in *.
  naive_bsolver.
Qed.

Lemma well_formed_imp_proj1 {Σ : Signature} p q:
  well_formed (patt_imp p q) ->
  well_formed p.
Proof.
  intros H.
  unfold well_formed,well_formed_closed in *. simpl in *.
  naive_bsolver.
Qed.

Lemma well_formed_imp_proj2 {Σ : Signature} p q:
  well_formed (patt_imp p q) ->
  well_formed q.
Proof.
  intros H.
  unfold well_formed,well_formed_closed in *. simpl in *.
  naive_bsolver.
Qed.


Definition well_formed_xy {Σ : Signature} (x y : nat) (ϕ : Pattern) : bool :=
  well_formed_positive ϕ &&
  well_formed_closed_ex_aux ϕ x &&
  well_formed_closed_mu_aux ϕ y
.

Lemma wfxy00_wf {Σ : Signature} (ϕ : Pattern) :
  well_formed_xy 0 0 ϕ = well_formed ϕ.
Proof.
  unfold well_formed,well_formed_closed,well_formed_xy.
  simpl.
  rewrite -andb_assoc.
  rewrite [well_formed_closed_mu_aux _ _ && well_formed_closed_ex_aux _ _]andb_comm.
  reflexivity.
Qed.

Lemma wf_wfxy00 {Σ : Signature} (ϕ : Pattern) :
  well_formed ϕ = well_formed_xy 0 0 ϕ
.
Proof. rewrite wfxy00_wf. reflexivity. Qed.

Lemma wf_wfxy00_compose {Σ : Signature} (ϕ : Pattern) :
  well_formed_xy 0 0 ϕ = true ->
  well_formed ϕ = true
.
Proof.
  intros H. rewrite wf_wfxy00. exact H.
Qed.

Lemma wf_wfxy00_decompose {Σ : Signature} (ϕ : Pattern) :
  well_formed ϕ = true ->
  well_formed_xy 0 0 ϕ = true
.
Proof.
  intros H. rewrite -wf_wfxy00. exact H.
Qed.

Definition lwf_xy {Σ : Signature} (x y : nat) (l : list Pattern)
  := fold_right andb true (map (well_formed_xy x y) l).

Definition lwf_positive {Σ : Signature} (l : list Pattern)
  := fold_right andb true (map well_formed_positive l).

Definition lwf_cmu {Σ : Signature} n (l : list Pattern)
  := fold_right andb true (map (fun p => well_formed_closed_mu_aux p n) l).

Definition lwf_cex {Σ : Signature} n (l : list Pattern)
  := fold_right andb true (map (fun p => well_formed_closed_ex_aux p n) l).

Definition wf {Σ : Signature} (l : list Pattern) := fold_right andb true (map well_formed l).

Lemma wf_lwf_xy {Σ : Signature} (l : list Pattern) :
  wf l = lwf_xy 0 0 l
.
Proof.
  unfold wf, lwf_xy.
  induction l; simpl.
  { reflexivity. }
  {
    rewrite IHl.
    rewrite -wfxy00_wf.
    reflexivity.
  }
Qed.

Lemma wf_lwf_xy_compose {Σ : Signature} (l : list Pattern) :
  lwf_xy 0 0 l = true ->
  wf l = true
.
Proof.
  intros H. rewrite wf_lwf_xy. exact H.
Qed.

Lemma wf_lwf_xy_decompose {Σ : Signature} (l : list Pattern) :
  wf l = true ->
  lwf_xy 0 0 l = true
.
Proof.
  intros H. rewrite -wf_lwf_xy. exact H.
Qed.

Lemma wf_corr {Σ : Signature} (l : list Pattern) :
  wf l = lwf_positive l && lwf_cmu 0 l && lwf_cex 0 l
.
Proof.
  unfold wf,lwf_positive,lwf_cmu,lwf_cex,well_formed,well_formed_closed.
  induction l; simpl.
  { reflexivity. }
  {
    rewrite IHl.
    btauto.
  }
Qed.

Lemma lwf_xy_decompose {Σ : Signature} (x y : nat) (l : list Pattern) :
  lwf_xy x y l = lwf_positive l && lwf_cmu y l && lwf_cex x l
.
Proof.
  unfold lwf_xy,lwf_positive,lwf_cmu,lwf_cex,well_formed_xy.
  induction l; simpl.
  { reflexivity. }
  {
    rewrite IHl. simpl.
    btauto.
  }
Qed.

Lemma lwf_xy_cons
  {Σ : Signature} (m n : nat) (x : Pattern) (xs : list Pattern)
  :
  lwf_xy m n (x::xs) = well_formed_xy m n x && lwf_xy m n xs
.
Proof. reflexivity. Qed.

Lemma lwf_xy_cons_compose
  {Σ : Signature} (m n : nat) (x : Pattern) (xs : list Pattern)
  :
  well_formed_xy m n x = true /\ lwf_xy m n xs = true ->
  lwf_xy m n (x::xs) = true
.
Proof.
  intros H.
  rewrite lwf_xy_cons.
  destruct H as [H1 H2].
  rewrite H1 H2.
  reflexivity.
Qed.

Lemma lwf_xy_cons_decompose
  {Σ : Signature} (m n : nat) (x : Pattern) (xs : list Pattern)
  :
  lwf_xy m n (x::xs) = true ->
  well_formed_xy m n x = true /\ lwf_xy m n xs = true
.
Proof.
  intros H.
  rewrite lwf_xy_cons in H.
  naive_bsolver.
Qed.

Lemma lwf_positive_cons
  {Σ : Signature} (x : Pattern) (xs : list Pattern)
  :
  lwf_positive (x::xs) = well_formed_positive x && lwf_positive xs
.
Proof. reflexivity. Qed.

Lemma lwf_cmu_cons
  {Σ : Signature} (n : nat) (x : Pattern) (xs : list Pattern)
  :
  lwf_cmu n (x::xs) = well_formed_closed_mu_aux x n && lwf_cmu n xs
.
Proof. reflexivity. Qed.

Lemma lwf_cex_cons
  {Σ : Signature} (n : nat) (x : Pattern) (xs : list Pattern)
  :
  lwf_cex n (x::xs) = well_formed_closed_ex_aux x n && lwf_cex n xs
.
Proof. reflexivity. Qed.

Lemma lwf_xy_app
  {Σ : Signature} (m n : nat) (xs ys : list Pattern)
  :
  lwf_xy m n (xs ++ ys) = lwf_xy m n xs && lwf_xy m n ys
.
Proof.
  induction xs; simpl.
  { reflexivity. }
  { rewrite 2!lwf_xy_cons. rewrite IHxs. btauto. }
Qed.

Lemma lwf_xy_app_compose
  {Σ : Signature} (m n : nat) (xs ys : list Pattern)
  :
  lwf_xy m n xs = true /\ lwf_xy m n ys = true ->
  lwf_xy m n (xs ++ ys) = true
.
Proof.
  intros H.
  rewrite lwf_xy_app.
  destruct H as [H1 H2].
  rewrite H1 H2.
  reflexivity.
Qed.

Lemma lwf_xy_app_decompose
  {Σ : Signature} (m n : nat) (xs ys : list Pattern)
  :
  lwf_xy m n (xs ++ ys) = true ->
  lwf_xy m n xs = true /\ lwf_xy m n ys = true
.
Proof.
  intros H.
  rewrite lwf_xy_app in H.
  naive_bsolver.
Qed.

Lemma lwf_positive_app
  {Σ : Signature} (xs ys : list Pattern)
  :
  lwf_positive (xs++ys) = lwf_positive xs && lwf_positive ys
.
Proof.
  induction xs; simpl.
  { reflexivity. }
  { rewrite 2!lwf_positive_cons. rewrite IHxs. btauto. }
Qed.


Lemma lwf_cmu_app
  {Σ : Signature} (n : nat) (xs ys : list Pattern)
  :
  lwf_cmu n (xs++ys) = lwf_cmu n xs && lwf_cmu n ys
.
Proof.
  induction xs; simpl.
  { reflexivity. }
  { rewrite 2!lwf_cmu_cons. rewrite IHxs. btauto. }
Qed.

Lemma lwf_cex_app
  {Σ : Signature} (n : nat) (xs ys : list Pattern)
  :
  lwf_cex n (xs++ys) = lwf_cex n xs && lwf_cex n ys
.
Proof.
  induction xs; simpl.
  { reflexivity. }
  { rewrite 2!lwf_cex_cons. rewrite IHxs. btauto. }
Qed.

(* TODO: maybe generalize to any connective? *)
Lemma well_formed_foldr {Σ : Signature} g xs :
  well_formed g = true ->
  wf xs = true ->
  well_formed (foldr patt_imp g xs) = true.
Proof.
  intros wfg wfxs.
  induction xs.
  - simpl. exact wfg.
  - simpl. unfold wf in wfxs. simpl in wfxs.
    apply andb_prop in wfxs. destruct wfxs.
    apply well_formed_imp.
    { assumption. }
    { apply IHxs. assumption. }
Qed.

Lemma wf_take {Σ : Signature} n xs :
  wf xs = true ->
  wf (take n xs) = true.
Proof.
  unfold wf. intros H.
  rewrite map_take.
  rewrite foldr_andb_true_take; auto.
Qed.

Lemma wf_drop {Σ : Signature} n xs:
  wf xs = true ->
  wf (drop n xs) = true.
Proof.
  unfold wf. intros H.
  rewrite map_drop.
  rewrite foldr_andb_true_drop; auto.
Qed.

Lemma wf_insert {Σ : Signature} n p xs:
  wf xs = true ->
  well_formed p = true ->
  wf (<[n := p]> xs) = true.
Proof.
  intros wfxs wfp.
  move: xs wfxs.
  induction n; intros xs wfxs; destruct xs; simpl; auto.
  - unfold wf in wfxs. simpl in wfxs. apply andb_prop in wfxs.
    destruct wfxs as [wfp0 wfxs].
    unfold wf. simpl. rewrite wfp. rewrite wfxs.
    reflexivity.
  - unfold wf in wfxs. simpl in wfxs. apply andb_prop in wfxs.
    destruct wfxs as [wfp0 wfxs].
    unfold wf. simpl.
    unfold wf in IHn.
    rewrite wfp0.
    rewrite IHn; auto.
Qed.

Lemma wf_tail' {Σ : Signature} p xs:
  wf (p :: xs) = true ->
  wf xs = true.
Proof.
  unfold wf. intros H. simpl in H. apply andb_prop in H. rewrite (proj2 H). reflexivity.
Qed.

Lemma wf_cons {Σ : Signature} x xs:
  well_formed x = true ->
  wf xs = true ->
  wf (x :: xs) = true.
Proof.
  intros wfx wfxs.
  unfold wf. simpl. rewrite wfx.
  unfold wf in wfxs. rewrite wfxs.
  reflexivity.
Qed.

 Lemma wf_app {Σ : Signature} xs ys:
  wf xs = true ->
  wf ys = true ->
  wf (xs ++ ys) = true.
Proof.
  intros wfxs wfys.
  unfold wf in *.
  rewrite map_app.
  rewrite foldr_app.
  rewrite wfys.
  rewrite wfxs.
  reflexivity.
Qed.

(* TODO move somewhere else *)
Lemma wfapp_proj_1 {Σ : Signature} l₁ l₂:
  wf (l₁ ++ l₂) = true ->
  wf l₁ = true.
Proof.
  intros H.
  apply (wf_take (length l₁)) in H.
  rewrite take_app in H.
  rewrite Nat.sub_diag firstn_all take_0 app_nil_r in H.
  exact H.
Qed.

Lemma wfapp_proj_2 {Σ : Signature} l₁ l₂:
  wf (l₁ ++ l₂) = true ->
  wf l₂ = true.
Proof.
  intros H.
  apply (wf_drop (length l₁)) in H.
  rewrite drop_app in H.
  rewrite Nat.sub_diag drop_all drop_0 in H.
  exact H.
Qed.

Lemma wfl₁hl₂_proj_l₁ {Σ : Signature} l₁ h l₂:
  wf (l₁ ++ h :: l₂) ->
  wf l₁.
Proof.
  apply wfapp_proj_1.
Qed.

Lemma wfl₁hl₂_proj_h {Σ : Signature} l₁ h l₂:
  wf (l₁ ++ h :: l₂) ->
  well_formed h.
Proof.
  intros H. apply wfapp_proj_2 in H. unfold wf in H.
  simpl in H. apply andb_prop in H as [H1 H2].
  exact H1.
Qed.

Lemma wfl₁hl₂_proj_l₂ {Σ : Signature} l₁ h l₂:
  wf (l₁ ++ h :: l₂) ->
  wf l₂.
Proof.
  intros H. apply wfapp_proj_2 in H. unfold wf in H.
  simpl in H. apply andb_prop in H as [H1 H2].
  exact H2.
Qed.

Lemma wfl₁hl₂_proj_l₁l₂ {Σ : Signature} l₁ h l₂:
  wf (l₁ ++ h :: l₂) ->
  wf (l₁ ++ l₂).
Proof.
  intros H.
  pose proof (wfl₁hl₂_proj_l₁ _ _ _ H).
  pose proof (wfl₁hl₂_proj_l₂ _ _ _ H).
  apply wf_app; assumption.
Qed.


Definition wfPattern {Σ : Signature} := {p : Pattern | well_formed p = true}.

Global Instance wfPattern_eqdec {Σ : Signature} : EqDecision wfPattern.
Proof.
  solve_decision.
Defined.

Global Instance wfPattern_countable {Σ : Signature} : Countable wfPattern.
Proof.
  apply countable_sig.
  solve_decision.
Defined.

Global Instance Pattern_infinite {Σ : Signature} :
  Infinite Pattern.
Proof.
  apply inj_infinite with
    (f := patt_free_evar)
    (g := fun p => (match p with patt_free_evar x => Some x | _ => None end) ).
  intros x. reflexivity.
Defined.

Global Instance wfPattern_infinite {Σ : Signature} :
  Infinite wfPattern.
Proof.
  apply inj_infinite with
    (f := fun x => exist (fun p : Pattern => well_formed p = true) (patt_free_evar x) erefl)
    (g := fun wp => (match proj1_sig wp with patt_free_evar x => Some x | _ => None end) ).
  intros x. reflexivity.
Defined.


Lemma map_wf :
  forall {Σ : Signature} (f : Pattern -> Pattern) l,
    wf l -> (forall p, well_formed p -> well_formed (f p)) ->
    wf (map f l).
Proof.
  induction l; intros; try by cbn in *.
  cbn in *.
  destruct_andb! H. apply H0 in H1.
  specialize (IHl H2 H0). unfold wf in IHl.
  by rewrite H1 IHl.
Qed.

(* Allows splitting `wf` without unfolding in-place. *)
Lemma wf_cons_iff {Σ : Signature} x l : wf (x :: l) <-> well_formed x /\ wf l.
Proof.
  unfold wf. simpl. apply andb_true_iff.
Defined.

Section corollaries.
  Context {Σ : Signature}.

  Lemma Forall_wf_map {A} (t : A -> Pattern) l : Forall (well_formed ∘ t) l <-> wf (map t l).
  Proof.
    intros. etransitivity. apply Forall_fold_right. unfold wf.
    rewrite -> 2 foldr_map, foldr_andb_equiv_foldr_conj.
    reflexivity.
  Qed.

  Corollary wf_fold_left {A : Type} (f : Pattern -> A -> Pattern) (t : A -> Pattern) x xs :
    well_formed x ->
    wf (map t xs) ->
    (forall a b, well_formed a -> well_formed (t b) -> well_formed (f a b)) ->
    well_formed (fold_left f xs x).
  Proof.
    intros. apply fold_left_ind with (Q := well_formed ∘ t);
    only 2: apply Forall_wf_map; auto.
  Defined.

  Corollary wf_foldr {A : Type} (f : A -> Pattern -> Pattern) (t : A -> Pattern) x xs :
    well_formed x ->
    wf (map t xs) ->
    (forall a b, well_formed a -> well_formed (t b) -> well_formed (f b a)) ->
    well_formed (foldr f x xs).
  Proof.
    intros.
    apply foldr_ind with (Q := well_formed ∘ t);
    only 2: apply Forall_wf_map; auto.
  Qed.

  Corollary mf_fold_left {A : Type} (f : Pattern -> A -> Pattern) (t : A -> Pattern) x xs :
    mu_free x ->
    foldr (fun c a => mu_free c && a) true (map t xs) ->
    (forall a b, mu_free a -> mu_free (t b) -> mu_free (f a b)) ->
    mu_free (fold_left f xs x).
  Proof.
    intros.
    apply fold_left_ind with (Q := mu_free ∘ t);
    only 2: apply Forall_fold_right;
    only 2: rewrite -> foldr_map, foldr_andb_equiv_foldr_conj in H0;
    auto.
  Qed.

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

End corollaries.

Ltac size_induction φ :=
match type of φ with
| Pattern => let sz := fresh "sz" in
             let Hsz := fresh "Hsz" in
             let H := fresh "H" in
               remember (pat_size φ) as sz eqn:H;
               assert (pat_size φ <= sz) as Hsz by lia;
               clear H;
               revert φ Hsz;
               let sz' := fresh "sz" in
               let IHsz := fresh "IHsz" in
               induction sz as [|sz' IHsz]; intros φ Hsz; [
                 destruct φ; simpl pat_size in Hsz; lia
               |
                 destruct φ;
(*                  unfold PatternSize in Hsz, IHsz; *)
                 simpl in Hsz
(*                  replace pat_size with (size : Pattern -> nat) in * by reflexivity *)
               ]
end.

Local Lemma test_ind :
  forall {Σ : Signature} (φ : Pattern),
    size (∅ : EVarSet) = 0 -> pat_size φ = pat_size (patt_app φ φ).
Proof.
  intros ? φ.
  size_induction φ.
  6: {
Abort.


Module BoundVarSugar.
  (* Element variables - bound *)
  Notation b0 := (patt_bound_evar 0).
  Notation b1 := (patt_bound_evar 1).
  Notation b2 := (patt_bound_evar 2).
  Notation b3 := (patt_bound_evar 3).
  Notation b4 := (patt_bound_evar 4).
  Notation b5 := (patt_bound_evar 5).
  Notation b6 := (patt_bound_evar 6).
  Notation b7 := (patt_bound_evar 7).
  Notation b8 := (patt_bound_evar 8).
  Notation b9 := (patt_bound_evar 9).

  Notation B0 := (patt_bound_svar 0).
  Notation B1 := (patt_bound_svar 1).
  Notation B2 := (patt_bound_svar 2).
  Notation B3 := (patt_bound_svar 3).
  Notation B4 := (patt_bound_svar 4).
  Notation B5 := (patt_bound_svar 5).
  Notation B6 := (patt_bound_svar 6).
  Notation B7 := (patt_bound_svar 7).
  Notation B8 := (patt_bound_svar 8).
  Notation B9 := (patt_bound_svar 9).

End BoundVarSugar.

Module Notations.
  Declare Scope ml_scope.
  Delimit Scope ml_scope with ml.
  Notation "a ⋅ b" := (patt_app a b) (at level 66, left associativity) : ml_scope.
  Notation "⊥" := patt_bott : ml_scope.
  Notation "a ---> b"  := (patt_imp a b) (at level 75, right associativity) : ml_scope.
  Notation "'ex' , phi" := (patt_exists phi) (at level 80) : ml_scope.
  Notation "'mu' , phi" := (patt_mu phi) (at level 80) : ml_scope.

  (*Notation "AC [ p ]" := (subst_ctx AC p) (at level 90) : ml_scope.*)
End Notations.
