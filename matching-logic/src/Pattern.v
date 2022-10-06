From Coq Require Import ssreflect ssrfun ssrbool.

From stdpp Require Import countable infinite.
From stdpp Require Import pmap gmap mapset fin_sets propset.
Require Import stdpp_ext.

Require Import extralibrary.

From MatchingLogic Require Export
    Signature.


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
                              + ((@symbols Σ)
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
                              + ((@symbols Σ)
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

Section syntax.
    Context {Σ : Signature}.

Fixpoint size (p : Pattern) : nat :=
    match p with
    | patt_app ls rs => 1 + (size ls) + (size rs)
    | patt_imp ls rs => 1 + (size ls) + (size rs)
    | patt_exists p' => 1 + size p'
    | patt_mu p' => 1 + size p'
    | _ => 0
    end.


Fixpoint size' (p : Pattern) : nat :=
    match p with
    | patt_app ls rs => 1 + (size' ls) + (size' rs)
    | patt_imp ls rs => 1 + (size' ls) + (size' rs)
    | patt_exists p' => 1 + size' p'
    | patt_mu p' => 1 + size' p'
    | _ => 1
    end.

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
  destruct_and!.
  split_and!; auto.
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
  intros. destruct_and!. split_and!; auto.
  eapply well_formed_closed_ex_aux_ind in H2. simpl. eassumption. lia.
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
        destruct_and!.
        unfold no_negative_occurrence_db_b.
        split_and!; naive_bsolver auto.
      + simpl in Hwfc.
        destruct_and!.
        unfold no_positive_occurrence_db_b.
        split_and!; naive_bsolver auto.
    - split.
      + simpl in Hwfc.
        destruct_and!. split_and!; naive_bsolver auto.
      + simpl in Hwfc.
        destruct_and!. split_and!; naive_bsolver auto.
    - simpl in Hwfc.
      split_and!; naive_bsolver auto.
    - simpl in Hwfc.
      split_and!; eapply IHpsi.
      1,3: eassumption. all: lia.
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
    x ∉ free_evars p ->
    count_evar_occurrences x p = 0.
  Proof.
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
  Qed.


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
      destruct_and!. split_and!; assumption.
    - apply andb_prop in H. destruct H as [H1 H2].
      specialize (IHp1 m H1). specialize (IHp2 m H2).
      destruct_and!. split_and!; assumption.
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
  Qed.


  Theorem mu_free_wfp φ :
    mu_free φ -> well_formed_positive φ.
  Proof.
    induction φ; intros Hmf; simpl; auto.
    all: simpl in Hmf; destruct_and!; rewrite -> IHφ1, -> IHφ2; auto.
  Qed.


Lemma wf_imp_wfc ϕ:
well_formed ϕ -> well_formed_closed ϕ.
Proof.
intros H. apply andb_prop in H. tauto.
Qed.


Definition evar_is_fresh_in x ϕ := x ∉ free_evars ϕ.
Definition svar_is_fresh_in x ϕ := x ∉ free_svars ϕ.

End syntax.


Lemma well_formed_app_proj1 {Σ : Signature} p q:
  well_formed (patt_app p q) ->
  well_formed p.
Proof.
  intros H.
  unfold well_formed,well_formed_closed in *. simpl in *.
  destruct_and!.
  unfold well_formed,well_formed_closed. split_and!; assumption.
Qed.

Lemma well_formed_app_proj2 {Σ : Signature} p q:
  well_formed (patt_app p q) ->
  well_formed q.
Proof.
  intros H.
  unfold well_formed,well_formed_closed in *. simpl in *.
  destruct_and!.
  unfold well_formed,well_formed_closed. split_and!; assumption.
Qed.

Lemma well_formed_imp_proj1 {Σ : Signature} p q:
  well_formed (patt_imp p q) ->
  well_formed p.
Proof.
  intros H.
  unfold well_formed,well_formed_closed in *. simpl in *.
  destruct_and!.
  unfold well_formed,well_formed_closed. split_and!; assumption.
Qed.

Lemma well_formed_imp_proj2 {Σ : Signature} p q:
  well_formed (patt_imp p q) ->
  well_formed q.
Proof.
  intros H.
  unfold well_formed,well_formed_closed in *. simpl in *.
  destruct_and!.
  unfold well_formed,well_formed_closed. split_and!; assumption.
Qed.

Definition wf {Σ : Signature} (l : list Pattern) := fold_right andb true (map well_formed l).

Definition lwf_positive {Σ : Signature} (l : list Pattern)
  := fold_right andb true (map well_formed_positive l).

Definition lwf_cmu {Σ : Signature} n (l : list Pattern)
  := fold_right andb true (map (fun p => well_formed_closed_mu_aux p n) l).

Definition lwf_cex {Σ : Signature} n (l : list Pattern)
  := fold_right andb true (map (fun p => well_formed_closed_ex_aux p n) l).


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
exact H.
Qed.

Lemma wfapp_proj_2 {Σ : Signature} l₁ l₂:
wf (l₁ ++ l₂) = true ->
wf l₂ = true.
Proof.
intros H.
apply (wf_drop (length l₁)) in H.
rewrite drop_app in H.
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