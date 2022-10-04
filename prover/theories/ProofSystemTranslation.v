From Coq Require Import ssreflect ssrfun ssrbool.

From Coq Require Import Strings.String.
From Coq Require Import Logic.PropExtensionality Logic.Eqdep_dec Logic.Classical_Prop.
From Equations Require Import Equations.

From stdpp Require Export base gmap fin_sets sets list countable.
From MatchingLogic Require Import Syntax Semantics StringSignature ProofSystem ProofMode.
From MatchingLogicProver Require Import Named NamedProofSystem NMatchers.

From stdpp Require Import base finite gmap mapset listset_nodup numbers propset list.

Import ProofSystem.Notations.

(* TODO: move this near to the definition of Pattern *)
Derive NoConfusion for Pattern.
Derive Subterm for Pattern.

Ltac invert_tuples :=
  repeat (match goal with
          | [H: (?x1,?y1)=(?x2,?y2) |- _] => inversion H; clear H; subst
          end).

Ltac do_rewrites_everywhere := 
  repeat (match goal with
  | [H: ?l = ?r , H' : _ |- _] => rewrite H in H'; simpl in H'
  end).

Ltac case_match_in_hyp H :=
  lazymatch type of H with
  | context [ match ?x with _ => _ end ] => destruct x eqn:?
  end.


(* In an empty context, this rewrites: *)
(* ∃ (x.x) /\ (∃ y.y) ~> (∃ x.x) /\ (∃ x.x) *)
(* But in some other context C, it might rewrite *)
(* C[∃ (x.x) /\ (∃ y.y)] ~> C[(∃ z.z) /\ (∃ z.z)] *)
(* because we might see some ∃ z.z in the context C. *)


(* TODO we have to implement the two-phase approach to proof system translation.
   The cache-based on was too complicated, so I removed the proofs from this file.
*)
(*
Record AlphaConversion {Σ : Signature} :=
  {
    ac_list : list evar ;
  }.

Definition AlphaConversion_valid {Σ : Signature}
  (ac : AlphaConversion) (nϕ : NamedPattern)
  := (ac_list ac) ## elements (named_free_evars nϕ).

Print NamedPattern.
*)

(*
Definition head_or_id {Σ : Signature}
  (l : list evar) (p : NamedPattern) : NamedPattern 
  match l with
  | [] => p
  | (x::xs) => 
*)

Fixpoint number_of_exists
  {Σ : Signature} (ϕ : NamedPattern) : nat :=
  match ϕ with
  | npatt_app phi1 phi2
    => number_of_exists phi1 + number_of_exists phi2
  | npatt_imp phi1 phi2
    => number_of_exists phi1 + number_of_exists phi2
  | npatt_exists _ phi
    => S (number_of_exists phi)
  | npatt_mu _ phi
    => number_of_exists phi
  | _ => 0
  end.

  Fixpoint number_of_mus
  {Σ : Signature} (ϕ : NamedPattern) : nat :=
  match ϕ with
  | npatt_app phi1 phi2
    => number_of_mus phi1 + number_of_mus phi2
  | npatt_imp phi1 phi2
    => number_of_mus phi1 + number_of_mus phi2
  | npatt_exists _ phi
    => (number_of_mus phi)
  | npatt_mu _ phi
    => S ( number_of_mus phi)
  | _ => 0
  end.

Fixpoint rename {Σ : Signature}
  (bevs : list evar)
  (bsvs : list svar)
  (fevs : gmap evar evar)
  (fsvs : gmap svar svar)
  (nϕ : NamedPattern)
  : NamedPattern :=
  match nϕ with
  | npatt_evar x
    => match (fevs !! x) with
       | None => npatt_evar x
       | Some y => npatt_evar y
       end
  | npatt_svar X
       => match (fsvs !! X) with
          | None => npatt_svar X
          | Some Y => npatt_svar Y
          end
  | npatt_sym s => npatt_sym s
  | npatt_bott => npatt_bott
  | npatt_imp phi1 phi2 =>
    npatt_imp
      (rename bevs bsvs fevs fsvs phi1)
      (rename (drop (number_of_exists phi1) bevs)
              (drop (number_of_mus phi1) bsvs)
              fevs fsvs phi2) 
  | npatt_app phi1 phi2 =>
    npatt_app
      (rename bevs bsvs fevs fsvs phi1)
      (rename (drop (number_of_exists phi1) bevs)
      (drop (number_of_exists phi1) bsvs)
              fevs fsvs phi2) 
  | npatt_exists x phi =>
    match bevs with
    | [] => npatt_exists x phi
    | (y::ys)
      => npatt_exists y
          (rename ys bsvs (<[x:=y]>fevs) fsvs phi)
    end
  | npatt_mu X phi =>
    match bsvs with
    | [] => npatt_mu X phi
    | (Y::Ys)
      => npatt_mu Y
          (rename bevs Ys fevs (<[X:=Y]>fsvs) phi)
    end
  end.


  Record PartialBijection (A : Type)
    {_eqd : EqDecision A}
    {_cnt : Countable A}
     :=
  mkPartialBijection
  {
    pbr : gset (prod A A) ;
    pb1 : forall (x y1 y2 : A),
      (x,y1) ∈ pbr -> (x,y2) ∈ pbr -> y1 = y2 ;
    pb2 : forall (x1 x2 y : A),
      (x1,y) ∈ pbr -> (x2,y) ∈ pbr -> x1 = x2 ;
  }.

  Lemma pb_eq_dep (A : Type) 
    {_eqd : EqDecision A}
    {_cnt : Countable A}
    (s s' : gset (prod A A))
    pf1 pf1' pf2 pf2'
    : s = s' ->
      @mkPartialBijection A _eqd _cnt s pf1 pf2 = @mkPartialBijection A _eqd _cnt s' pf1' pf2'.
    Proof.
      intros H.
      subst s'.
      f_equal; apply proof_irrelevance.
    Qed.

  Arguments pbr {A%type_scope} {_eqd _cnt} p.

  Definition myswap {A : Type} (p : prod A A) : prod A A := (p.2, p.1).

  Program Definition pbr_converse {A : Type}
    {_eqd : EqDecision A}
    {_cnt : Countable A}
    (R : PartialBijection A) : PartialBijection A
  := {|
    pbr := (set_map myswap (pbr R))  ;
  |}.
  Next Obligation.
    intros ??????? H1 H2.
    rewrite elem_of_map in H1.
    rewrite elem_of_map in H2.
    destruct H1 as [[x11 x12] [H11 H12]].
    destruct H2 as [[x21 x22] [H21 H22]].
    simpl in *.
    inversion H11; clear H11; inversion H21; clear H21; subst.
    destruct R as [r pf1 pf2]; simpl in *.
    naive_solver.
  Qed.
  Next Obligation.
    intros ??????? H1 H2.
    rewrite elem_of_map in H1.
    rewrite elem_of_map in H2.
    destruct H1 as [[x11 x12] [H11 H12]].
    destruct H2 as [[x21 x22] [H21 H22]].
    simpl in *.
    inversion H11; clear H11; inversion H21; clear H21; subst.
    destruct R as [r pf1 pf2]; simpl in *.
    naive_solver.
  Qed.
 
  Lemma pbr_converse_sym (A : Type)
    {_eqd : EqDecision A}
    {_cnt : Countable A}
    (R : PartialBijection A)
    : forall (x y : A), ((x,y) ∈ (pbr (pbr_converse R))) <-> ((y,x) ∈ (pbr R)).
  Proof.
    intros x y.
    destruct R as [r pf1 pf2]; simpl.
    rewrite elem_of_map.
    unfold myswap.
    split; intros H.
    {
      destruct H as [[a1 a2] [H1 H2]].
      simpl in *.
      naive_solver.
    }
    {
      exists (y,x).
      split;[reflexivity|assumption].
    }
  Qed.

  Definition related {A : Type} (u v : prod A A) : Prop
  := u.1 = v.1 \/ u.2 = v.2.

  Definition unrelated {A : Type} (u v : prod A A) : Prop
  := ~ (related u v).

  #[global]
  Instance related_dec (A : Type)
    {eq_dec : EqDecision A}
  : RelDecision (@unrelated A).
  Proof.
    solve_decision.
  Defined.

  Program Definition pb_update
  {A : Type}
  {_eqd : EqDecision A}
  {_cnt : Countable A}
  (pb : PartialBijection A)
  (x y : A)
  : PartialBijection A := {|
    pbr := (filter (unrelated (x,y)) (pbr pb) ) ∪ {[ (x,y) ]} ;
  |}.
  Next Obligation.
    intros ???? ????? H1 H2.
    rewrite elem_of_union in H1.
    rewrite elem_of_union in H2.
    rewrite elem_of_singleton in H1.
    rewrite elem_of_singleton in H2.
    rewrite elem_of_filter in H1.
    rewrite elem_of_filter in H2.
    destruct pb.
    unfold unrelated,related in *.
    simpl in *.
    naive_solver.
  Qed.
 Next Obligation.
  intros ???? ????? H1 H2.
  rewrite elem_of_union in H1.
  rewrite elem_of_union in H2.
  rewrite elem_of_singleton in H1.
  rewrite elem_of_singleton in H2.
  rewrite elem_of_filter in H1.
  rewrite elem_of_filter in H2.
  destruct pb.
  unfold unrelated,related in *.
  simpl in *.
  naive_solver.
 Qed.

 Lemma pbr_update_converse
  {A : Type}
  {_eqd : EqDecision A}
  {_cnt : Countable A}
  (R : PartialBijection A)
  : forall x y, pbr_converse (pb_update R x y) = pb_update (pbr_converse R) y x.
  Proof.
    intros x y.
    destruct R as [r pf1 pf2]; simpl in *.
    unfold pb_update,pbr_converse; simpl.
    apply pb_eq_dep.
    rewrite set_map_union_L.
    rewrite set_map_singleton_L.
    simpl.

    cut ((@set_map (A * A) (gset (A * A)) _ (A * A) (gset (A * A)) _ _ _ myswap (filter (unrelated (x, y)) r)) = (filter (unrelated (y, x)) (set_map myswap r))).
    {
      intros H. rewrite H. reflexivity.
    }
    apply anti_symm with (S := @subseteq (gset (prod A A)) _).
    { apply _. }
    1,2: rewrite elem_of_subseteq; intros x0 Hx0.
    {
      rewrite elem_of_map in Hx0.
      destruct Hx0 as [[x' y'] [Hx'y'1 Hx'y'2]].
      rewrite elem_of_filter in Hx'y'2.
      rewrite elem_of_filter.
      rewrite elem_of_map.
      unfold unrelated,related,myswap in *.
      simpl in *.
      subst.
      naive_solver.
    }
    {
      rewrite elem_of_filter in Hx0.
      rewrite elem_of_map in Hx0.
      rewrite elem_of_map.
      unfold unrelated,related,myswap in *.
      simpl in *.
      exists (x0.2, x0.1). simpl.
      rewrite -surjective_pairing.
      rewrite elem_of_filter. simpl.
      naive_solver.
    }
  Qed.


  Inductive alpha_equiv'
    {Σ : Signature}
    (R : PartialBijection evar)
    (R' : PartialBijection svar)
    : relation NamedPattern
    :=
    | ae_evar (x y : evar) (pf : (x, y) ∈ (pbr R))
      : alpha_equiv' R R' (npatt_evar x) (npatt_evar y)
    | ae_svar (X Y : svar) (pf : (X, Y) ∈ (pbr R'))
      : alpha_equiv' R R' (npatt_svar X) (npatt_svar Y)
    | ae_app
      (t t' u u' : NamedPattern)
      (tEt' : alpha_equiv' R R' t t')
      (uEu' : alpha_equiv' R R' u u')
      : alpha_equiv' R R' (npatt_app t u) (npatt_app t' u')
    | ae_imp
      (t t' u u' : NamedPattern)
      (tEt' : alpha_equiv' R R' t t')
      (uEu' : alpha_equiv' R R' u u')
      : alpha_equiv' R R' (npatt_imp t u) (npatt_imp t' u')
    | ae_bott : alpha_equiv' R R' npatt_bott npatt_bott
    | ae_sym (s : symbols) : alpha_equiv' R R' (npatt_sym s) (npatt_sym s) 
    | ae_ex (x y : evar) (t u : NamedPattern)
      (tEu : alpha_equiv'
        (pb_update R x y) R' t u)
      : alpha_equiv' R R'
        (npatt_exists x t)
        (npatt_exists y u)
    | ae_mu (X Y : svar) (t u : NamedPattern)
      (tEu : alpha_equiv'
        R (pb_update R' X Y) t u)
      : alpha_equiv' R R'
        (npatt_mu X t)
        (npatt_mu Y u)
  .

  #[global]
  Instance myswap_involutive
    (A : Type) :
    Involutive (=) (@myswap A).
  Proof.
    unfold Involutive.
    intros p.
    destruct p.
    unfold myswap.
    reflexivity.
  Qed.

  #[global]
  Instance myswap_inj (A : Type) : Inj (=) (=) (@myswap A).
  Proof.
    intros p1 p2 Hp1p2.
    unfold myswap in Hp1p2.
    destruct p1,p2.
    simpl in *.
    inversion Hp1p2.
    subst.
    reflexivity.
  Qed.

  #[global]
  Instance set_map_involutive (A C : Type)
    {_eoAC : ElemOf A C}
    {_eleAC : Elements A C}
    {_singAC : Singleton A C}
    {_emptyC : Empty C}
    {_uniC : Union C}
    {_interC : Intersection C}
    {_difC : Difference C}
    {_eqdecA : EqDecision A}
    {_finac : FinSet A C}
    (f : A -> A)
    {_injF : Inj (=) (=) f}
    {_invF : Involutive (=) f}
    {_lC : LeibnizEquiv C}
    :
    Involutive (=) (@set_map A C _eleAC A C _singAC _emptyC _uniC f).
  Proof.
    intros x.
    unfold set_map.
    rewrite -[x in _ = x]list_to_set_elements_L.
    rewrite elements_list_to_set.
    {
      rewrite NoDup_fmap.
      apply NoDup_elements.
    }
    rewrite -list_fmap_compose.
    unfold compose.
    under [fun x0 => _]functional_extensionality => x0.
    {
      rewrite _invF.
      over.
    }
    fold (@Coq.Init.Datatypes.id A).
    rewrite list_fmap_id.
    reflexivity.
  Qed.

  #[global]
  Instance pbr_converse_involutive
    (A : Type)
    {_eqd : EqDecision A}
    {_cnt : Countable A}
     : Involutive (=) (@pbr_converse A _eqd _cnt).
  Proof.
    unfold Involutive.
    intros R.
    destruct R.
    apply pb_eq_dep.
    simpl.
    rewrite cancel.
    reflexivity.
  Qed.

  Lemma alpha_equiv_converse'
    {Σ : Signature}
    (R : PartialBijection evar)
    (R' : PartialBijection svar)
    : forall x y,
      alpha_equiv' R R' x y ->
      alpha_equiv' (pbr_converse R) (pbr_converse R') y x.
  Proof.
    intros x y H.
    induction H; try (solve [constructor; auto]).
      { constructor. rewrite pbr_converse_sym; assumption. }
      { constructor. rewrite pbr_converse_sym; assumption. }
      { constructor. rewrite pbr_update_converse in IHalpha_equiv'. assumption. }
      { constructor. rewrite pbr_update_converse in IHalpha_equiv'. assumption. }
  Qed.

  Lemma alpha'_sym
    {Σ : Signature}
    (R : PartialBijection evar)
    (R' : PartialBijection svar)
    : forall x y,
      alpha_equiv' R R' x y <->
      alpha_equiv' (pbr_converse R) (pbr_converse R') y x.
  Proof.
    intros x y; split; intros H.
    {
      apply alpha_equiv_converse'.
      apply H.
    }
    { 
      rewrite -[R](@cancel (PartialBijection evar) _ eq (@pbr_converse evar _ _)).
      rewrite -[R'](@cancel (PartialBijection svar) _ eq (@pbr_converse svar _ _)).
      apply alpha_equiv_converse'.
      apply H.
    }
  Qed.

  #[global]
  Instance alpha'_dec
    {Σ : Signature}
    (R : PartialBijection evar)
    (R' : PartialBijection svar)
    : RelDecision (alpha_equiv' R R').
  Proof.
    unfold RelDecision.
    intros x y.
    unfold Decision.
    move: R R' y.
    (*remember (size' x) as szx.*)
    induction x; intros R R' y; destruct y; try (solve [repeat constructor]);
      try (solve [right; intros HH; inversion HH]).
    {
      destruct (decide ((x, x0) ∈ pbr R)).
      {
        left. constructor. assumption.
      }
      {
        right. intros HContra. inversion HContra.
        contradiction.
      }
    }
    {
      destruct (decide ((X, X0) ∈ pbr R')).
      {
        left. constructor. assumption.
      }
      {
        right. intros HContra. inversion HContra.
        contradiction.
      }
    }
    {
      destruct (decide (sigma = sigma0)).
      {
        left. subst. constructor.
      }
      {
        right. intros HContra. inversion HContra.
        contradiction.
      }
    }
    {
      specialize (IHx1 R R' y1).
      specialize (IHx2 R R' y2).
      destruct IHx1, IHx2.
      {
        left. constructor; assumption.
      }
      all: right; intros HContra; inversion HContra; contradiction.
    }
    {
      specialize (IHx1 R R' y1).
      specialize (IHx2 R R' y2).
      destruct IHx1, IHx2.
      {
        left. constructor; assumption.
      }
      all: right; intros HContra; inversion HContra; contradiction.
    }
    {
      pose proof (IH' := IHx (pb_update R x x1) R' y).
      destruct IH'.
      {
        left. constructor. assumption.
      }
      {
        right. intros HContra. inversion HContra. clear HContra.
        subst.
        contradiction.
      }
    }
    {
      pose proof (IH' := IHx R (pb_update R' X X0) y).
      destruct IH'.
      {
        left. constructor. assumption.
      }
      {
        right. intros HContra. inversion HContra. clear HContra.
        subst.
        contradiction.
      }
    }
  Defined.

  Definition twice {A : Type} (x : A) : prod A A := (x, x).

  #[global]
  Instance twice_inj {A : Type} : Inj (=) (=) (@twice A).
  Proof.
    intros x y H.
    inversion H.
    reflexivity.
  Qed.

  Program Definition diagonal
    {A : Type}
    {_eqd : EqDecision A}
    {_cnt : Countable A}
    (S : gset A)
     : PartialBijection A :=
    {|
      pbr := set_map twice S ;
    |}.
  Next Obligation.
    intros ??????? H1 H2.
    rewrite elem_of_map in H1.
    rewrite elem_of_map in H2.
    destruct H1 as [w1 [Hw1 H'w1]].
    destruct H2 as [w2 [Hw2 H'w2]].
    inversion Hw1; clear Hw1; subst.
    inversion Hw2; clear Hw2; subst.
    reflexivity.
  Qed.
  Next Obligation.
    intros ??????? H1 H2.
    rewrite elem_of_map in H1.
    rewrite elem_of_map in H2.
    destruct H1 as [w1 [Hw1 H'w1]].
    destruct H2 as [w2 [Hw2 H'w2]].
    inversion Hw1; clear Hw1; subst.
    inversion Hw2; clear Hw2; subst.
    reflexivity.
  Qed.

  Definition alpha_equiv {Σ : Signature} (phi psi : NamedPattern) : Prop :=
    alpha_equiv'
      (diagonal (named_free_evars phi ∪ named_free_evars psi))
      (diagonal (named_free_svars phi ∪ named_free_svars psi))
      phi psi
  .

  #[global]
  Instance alpha_dec
    {Σ : Signature}
    : RelDecision alpha_equiv.
  Proof.
    intros x y.
    apply alpha'_dec.
  Defined.

  Lemma myswap_twice (A : Type) : myswap ∘ (@twice A) = twice.
  Proof.
    apply functional_extensionality.
    intros x. reflexivity.
  Qed.

  Lemma pbr_converse_diagonal (A : Type) {_eqd : EqDecision A} {_cnt : Countable A} (S : gset A):
    pbr_converse (diagonal S) = diagonal S.
  Proof.
    unfold diagonal,pbr_converse.
    apply pb_eq_dep.
    simpl.
    unfold set_map.
    apply anti_symm with (S := @subseteq (gset (prod A A)) _).
    { apply _. }
    1,2: rewrite elem_of_subseteq; intros x Hx.
    {
      rewrite elem_of_list_to_set in Hx.
      rewrite elem_of_list_to_set.
      rewrite elements_list_to_set in Hx.
      { apply NoDup_fmap.
        { apply _. }
        { apply NoDup_elements. }
      }
      rewrite -list_fmap_compose in Hx.
      rewrite myswap_twice in Hx.
      exact Hx.
    }
    {
      rewrite elem_of_list_to_set.
      rewrite elem_of_list_to_set in Hx.
      rewrite elements_list_to_set.
      { apply NoDup_fmap.
        { apply _. }
        { apply NoDup_elements. }
      }
      rewrite -list_fmap_compose.
      rewrite myswap_twice.
      exact Hx.
    }
  Qed.

  Lemma alpha_equiv_sym
  {Σ : Signature}
  : forall x y,
    alpha_equiv x y <->
    alpha_equiv y x.
  Proof.
    intros x y.
    unfold alpha_equiv.
    rewrite alpha'_sym.
    rewrite !pbr_converse_diagonal.
    rewrite [named_free_evars y ∪ named_free_evars x]union_comm_L.
    rewrite [named_free_svars y ∪ named_free_svars x]union_comm_L.
    apply reflexivity.
  Qed.

  Lemma alpha_equiv_refl {Σ : Signature} :
    forall p, alpha_equiv p p.
  Proof.
    intros p.
    unfold alpha_equiv.
    do 2 rewrite union_idemp_L.
    cut (forall R R', pbr (diagonal (named_free_evars p)) ⊆ (pbr R) ->
      pbr (diagonal (named_free_svars p)) ⊆ (pbr R')
     -> alpha_equiv' R R' p p).
    {
      intros H. apply H; apply reflexivity.
    }
    
    induction p; intros H1 H2; constructor; try set_solver.
    {
      simpl in *.
      apply IHp.
      {
        simpl in *.
        rewrite elem_of_subseteq.
        intros x0 Hx0.
        rewrite elem_of_map in Hx0.
        destruct Hx0 as [x' [Hx'1 Hx'2]].
        subst.
        rewrite elem_of_union.
        rewrite elem_of_singleton.
        unfold twice.
        destruct (decide (x = x')).
        {
          subst. right. reflexivity.
        }
        {
          left.
          rewrite elem_of_filter.
          unfold unrelated,related.
          simpl.
          set_solver.
        }
      }
      {
        assumption.
      }
    }
    {
      apply IHp.
      {
        assumption.
      }
      {
        simpl in *.
        rewrite elem_of_subseteq.
        intros [X1 X2] HX1X2.
        rewrite elem_of_map in HX1X2.
        destruct HX1X2 as [X3 [HX3 HX4]].
        unfold twice in *.
        simpl in *.
        inversion HX3. clear HX3. subst.
        rewrite elem_of_union. 
        destruct (decide (X3 = X)).
        {
          subst. right. rewrite elem_of_singleton. reflexivity.
        }
        {
          left.
          rewrite elem_of_filter.
          unfold unrelated,related.
          simpl.
          set_solver.
        }
      }
    }
  Qed.

  Fixpoint npfoldtopdown {Σ : Signature} {State : Type} 
    (f : State -> NamedPattern -> State)
    (state : State) (nϕ : NamedPattern)
    : (State)%type
  :=
    match nϕ with
    | npatt_evar x => f state (npatt_evar x)
    | npatt_svar X => f state (npatt_svar X)
    | npatt_sym s => f state (npatt_sym s)
    | npatt_bott => f state npatt_bott
    | npatt_imp nϕ1 nϕ2 =>
      let state' := f state (npatt_imp nϕ1 nϕ2) in
      let state'' := npfoldtopdown f state' nϕ1 in
      let state''' := npfoldtopdown f state' nϕ2 in
      state'''      
    | npatt_app nϕ1 nϕ2 =>
      let state' := f state (npatt_app nϕ1 nϕ2) in
      let state'' := npfoldtopdown f state' nϕ1 in
      let state''' := npfoldtopdown f state' nϕ2 in
      state'''
    | npatt_exists x nϕ' =>
      let state' := f state (npatt_exists x nϕ') in
      let state'' := npfoldtopdown f state' nϕ' in
      state''
    | npatt_mu X nϕ' =>
      let state' := f state (npatt_mu X nϕ') in
      let state'' := npfoldtopdown f state' nϕ' in
      state''
    end.
  

  Record CollapseState {Σ : Signature} := mkCollapseState {
    cs_history : list NamedPattern;
  }.

  Definition lookup_or
    {Σ : Signature}
    (state : CollapseState)
    (nϕ : NamedPattern)
    (owise : (CollapseState * NamedPattern)%type)
    : (CollapseState * NamedPattern)%type
    := match (list_find (alpha_equiv nϕ) (cs_history state)) with
    | Some (_, nϕ') => (state, nϕ')
    | None => owise
    end.


  Definition lookup_or_node
    {Σ : Signature}
    (state : CollapseState)
    (nϕ : NamedPattern)
    (owise : (CollapseState * NamedPattern)%type)
    : (CollapseState * NamedPattern)%type
    := lookup_or state nϕ (mkCollapseState Σ ((owise.2)::(cs_history owise.1)), (owise.2)).

  Definition lookup_or_leaf
    {Σ : Signature}
    (state : CollapseState)
    (nϕ : NamedPattern)
    : (CollapseState * NamedPattern)%type
    := lookup_or_node state nϕ (state, nϕ).


  Program Fixpoint collapse_aux
    {Σ : Signature}
    (state : CollapseState)
    (nϕ : NamedPattern)
    : (CollapseState * NamedPattern)%type
  :=
    match nϕ with
    | npatt_evar x
      => lookup_or_leaf state nϕ
    | npatt_svar X
      => lookup_or_leaf state nϕ
    | npatt_bott
      => lookup_or_leaf state nϕ
    | npatt_sym s
      => lookup_or_leaf state nϕ
    | npatt_imp nϕ1 nϕ2
      => lookup_or_node state nϕ
        ( let res := collapse_aux state nϕ1 in
          let res' := collapse_aux (res.1) nϕ2 in
          (res'.1, (npatt_imp res.2 res'.2))
        )
    | npatt_app nϕ1 nϕ2
        => lookup_or_node state nϕ
          ( let res := collapse_aux state nϕ1 in
            let res' := collapse_aux (res.1) nϕ2 in
            (res'.1, (npatt_app res.2 res'.2))
          )
    | npatt_exists x nϕ'
      => lookup_or_node state nϕ
        (
          let res := collapse_aux state nϕ' in
          (res.1, (npatt_exists x res.2))
        )
    | npatt_mu X nϕ'
        => lookup_or_node state nϕ
          (
            let res := collapse_aux state nϕ' in
            (res.1, (npatt_mu X res.2))
          )
    end.

    Definition collapse
    {Σ : Signature}
    (nϕ : NamedPattern)
    : NamedPattern :=
    (collapse_aux (mkCollapseState Σ []) nϕ).2.

    (* (exists x. x) ---> (exists y. (y ---> exists z. z)) *)

    Lemma lookup_or_leaf_alpha
      {Σ : Signature}
      (state : CollapseState)
      (nϕ : NamedPattern)
      : alpha_equiv (lookup_or_leaf state nϕ).2 nϕ.
    Proof.
      unfold lookup_or_leaf, lookup_or_node, lookup_or.
      simpl.
      destruct (list_find (alpha_equiv nϕ) (cs_history state)) as [[n phi] |] eqn:Heq; simpl.
      {
        rewrite list_find_Some in Heq.
        destruct Heq as [H1 [H2 H3]].
        apply alpha_equiv_sym.
        assumption.
      }
      {
        apply alpha_equiv_refl.
      }
    Qed.


    Lemma alpha_equiv'_impl_almost_same_evars {Σ : Signature} R R' nϕ1 nϕ2:
      alpha_equiv' R R' nϕ1 nϕ2 ->
      forall x1, x1 ∈ (named_free_evars nϕ1) ->
        exists x2, x2 ∈ (named_free_evars nϕ2) /\
          (x1, x2) ∈ pbr R.
    Proof.
      intros Halpha x1 Hx1.
      induction Halpha; simpl in *.
      {
        rewrite elem_of_singleton in Hx1.
        subst.
        exists y.
        rewrite elem_of_singleton.
        split;[reflexivity|assumption].
      }
      { exfalso. set_solver. }
      {
        rewrite elem_of_union in Hx1.
        destruct Hx1 as [Hx1|Hx1].
        {
          specialize (IHHalpha1 Hx1).
          destruct IHHalpha1 as [x2 [Hx21 Hx22]].
          exists x2.
          rewrite elem_of_union.
          naive_solver.
        }
        {
          specialize (IHHalpha2 Hx1).
          destruct IHHalpha2 as [x2 [Hx21 Hx22]].
          exists x2.
          rewrite elem_of_union.
          naive_solver.
        }
      }
      {
        rewrite elem_of_union in Hx1.
        destruct Hx1 as [Hx1|Hx1].
        {
          specialize (IHHalpha1 Hx1).
          destruct IHHalpha1 as [x2 [Hx21 Hx22]].
          exists x2.
          rewrite elem_of_union.
          naive_solver.
        }
        {
          specialize (IHHalpha2 Hx1).
          destruct IHHalpha2 as [x2 [Hx21 Hx22]].
          exists x2.
          rewrite elem_of_union.
          naive_solver.
        }
      }
      { exfalso. set_solver. }
      { exfalso. set_solver. }
      {
        destruct (decide (x1 = x)).
        {
          subst. clear -Hx1. exfalso. set_solver.
        }
        {
          feed specialize IHHalpha.
          {
            set_solver.
          }
          destruct IHHalpha as [x2 [Hx21 Hx22]].
          rewrite elem_of_union in Hx22.
          rewrite elem_of_filter in Hx22.
          unfold unrelated,related in Hx22.
          rewrite elem_of_singleton in Hx22.
          simpl in Hx22.
          destruct Hx22; try naive_solver.
          exists x2. set_solver.
        }
      }
      {
        specialize (IHHalpha Hx1).
        exact IHHalpha.
      }
    Qed.

    Lemma alpha_equiv'_impl_almost_same_svars {Σ : Signature} R R' nϕ1 nϕ2:
      alpha_equiv' R R' nϕ1 nϕ2 ->
      forall X1, X1 ∈ (named_free_svars nϕ1) ->
        exists X2, X2 ∈ (named_free_svars nϕ2) /\
          (X1, X2) ∈ pbr R'.
    Proof.
      intros Halpha X1 HX1.
      induction Halpha; simpl in *.
      { exfalso. set_solver. }
      {
        rewrite elem_of_singleton in HX1.
        subst.
        exists Y.
        rewrite elem_of_singleton.
        split;[reflexivity|assumption].
      }
      {
        rewrite elem_of_union in HX1.
        destruct HX1 as [HX1|HX1].
        {
          specialize (IHHalpha1 HX1).
          destruct IHHalpha1 as [X2 [HX21 HX22]].
          exists X2.
          rewrite elem_of_union.
          naive_solver.
        }
        {
          specialize (IHHalpha2 HX1).
          destruct IHHalpha2 as [X2 [HX21 HX22]].
          exists X2.
          rewrite elem_of_union.
          naive_solver.
        }
      }
      {
        rewrite elem_of_union in HX1.
        destruct HX1 as [HX1|HX1].
        {
          specialize (IHHalpha1 HX1).
          destruct IHHalpha1 as [X2 [HX21 HX22]].
          exists X2.
          rewrite elem_of_union.
          naive_solver.
        }
        {
          specialize (IHHalpha2 HX1).
          destruct IHHalpha2 as [X2 [HX21 HX22]].
          exists X2.
          rewrite elem_of_union.
          naive_solver.
        }
      }
      { exfalso. set_solver. }
      { exfalso. set_solver. }
      {
        specialize (IHHalpha HX1).
        exact IHHalpha.
      }
      {
        destruct (decide (X1 = X)).
        {
          subst. clear -HX1. exfalso. set_solver.
        }
        {
          feed specialize IHHalpha.
          {
            set_solver.
          }
          destruct IHHalpha as [X2 [HX21 HX22]].
          rewrite elem_of_union in HX22.
          rewrite elem_of_filter in HX22.
          unfold unrelated,related in HX22.
          rewrite elem_of_singleton in HX22.
          simpl in HX22.
          destruct HX22; try naive_solver.
          exists X2. set_solver.
        }
      }
    Qed.

    Lemma alpha_equiv_impl_same_evars {Σ : Signature} nϕ1 nϕ2:
      alpha_equiv nϕ1 nϕ2 ->
      (named_free_evars nϕ1) = (named_free_evars nϕ2).
    Proof.
      intros Halpha.
      unfold alpha_equiv in Halpha.
      pose proof (H1 := alpha_equiv'_impl_almost_same_evars _ _ nϕ1 nϕ2 Halpha).
      pose proof (H2 := alpha_equiv'_impl_almost_same_evars _ _ nϕ2 nϕ1 (proj1 (alpha_equiv_sym nϕ1 nϕ2) Halpha)).
      simpl in *. unfold twice in *.
      apply anti_symm with (S := @subseteq (gset (evar)) _).
      { apply _. }
      {
        rewrite elem_of_subseteq.
        intros x Hx.
        specialize (H1 _ Hx).
        destruct H1 as [x2 [Hx21 Hx22]].
        rewrite elem_of_map in Hx22.
        destruct Hx22 as [x0 [Hx01 Hx02]].
        inversion Hx01; clear Hx01; subst.
        assumption.
      }
      {
        rewrite elem_of_subseteq.
        intros x Hx.
        specialize (H2 _ Hx).
        destruct H2 as [x2 [Hx21 Hx22]].
        rewrite elem_of_map in Hx22.
        destruct Hx22 as [x0 [Hx01 Hx02]].
        inversion Hx01; clear Hx01; subst.
        assumption.
      }
    Qed.

    Lemma alpha_equiv_impl_same_svars {Σ : Signature} nϕ1 nϕ2:
      alpha_equiv nϕ1 nϕ2 ->
      (named_free_svars nϕ1) = (named_free_svars nϕ2).
    Proof.
      intros Halpha.
      unfold alpha_equiv in Halpha.
      pose proof (H1 := alpha_equiv'_impl_almost_same_svars _ _ nϕ1 nϕ2 Halpha).
      pose proof (H2 := alpha_equiv'_impl_almost_same_svars _ _ nϕ2 nϕ1 (proj1 (alpha_equiv_sym nϕ1 nϕ2) Halpha)).
      simpl in *. unfold twice in *.
      apply anti_symm with (S := @subseteq (gset (svar)) _).
      { apply _. }
      {
        rewrite elem_of_subseteq.
        intros x Hx.
        specialize (H1 _ Hx).
        destruct H1 as [x2 [Hx21 Hx22]].
        rewrite elem_of_map in Hx22.
        destruct Hx22 as [x0 [Hx01 Hx02]].
        inversion Hx01; clear Hx01; subst.
        assumption.
      }
      {
        rewrite elem_of_subseteq.
        intros x Hx.
        specialize (H2 _ Hx).
        destruct H2 as [x2 [Hx21 Hx22]].
        rewrite elem_of_map in Hx22.
        destruct Hx22 as [x0 [Hx01 Hx02]].
        inversion Hx01; clear Hx01; subst.
        assumption.
      }
    Qed.

    Lemma alpha_equiv_same_size {Σ : Signature}
      (nϕ1 nϕ2 : NamedPattern) R R'
      : alpha_equiv' R R' nϕ1 nϕ2 ->
        nsize' nϕ1 = nsize' nϕ2.
    Proof.
      intros H.
      induction H; simpl; lia.
    Qed.

    Lemma collapse_aux_nsize' {Σ : Signature}
      (state : CollapseState)
      (nϕ : NamedPattern)
      : nsize' (collapse_aux state nϕ).2 = nsize' nϕ.
    Proof.
      move: state.
      induction nϕ; intros state; simpl;
        unfold lookup_or_leaf,lookup_or_node,lookup_or,alpha_equiv;
        repeat case_match; subst; simpl; try lia;
      match goal with
      | [H' : list_find _ _ = Some _ |- _] =>
        rewrite list_find_Some in H';
        destruct_and!;
        match goal with
        | [ Ha: alpha_equiv' _ _ _ _ |- _] => apply alpha'_sym in Ha
        end;
        erewrite alpha_equiv_same_size;[|eassumption];reflexivity
      | _ => congruence
      end.
    Qed.

    Definition list_of_pairs_apply {A B : Type}
    {_eqdA : EqDecision A}
    {_eqdB : EqDecision B}
    (x : A) (s : list (prod A B))
     : list B
   := fmap snd (filter (fun p => p.1 = x) s).

   Definition list_of_pairs_compose {A B C : Type}
      {_eqdA : EqDecision A}
      {_eqdB : EqDecision B}
      {_eqdC : EqDecision C}
      (s1 : list (prod A B))
      (s2 : list (prod B C))
      : list (prod A C)
    := foldr (fun (p : prod A B) (g' : list (prod A C)) =>
        let a := p.1 in
        let b := p.2 in
        g' ++ (fmap (fun (c : C) => (a,c))  (list_of_pairs_apply b s2))
    ) [] s1.


    Lemma list_of_pairs_compose_correct {A B C : Type}
    {_eqdA : EqDecision A}
    {_eqdB : EqDecision B}
    {_eqdC : EqDecision C}
    (s1 : list (prod A B))
    (s2 : list (prod B C))
    : forall (a : A) (c : C),
      (a, c) ∈ (list_of_pairs_compose s1 s2)
      <-> exists (b : B), (a, b) ∈ s1 /\ (b, c) ∈ s2.
    Proof.
      intros a c.
      unfold list_of_pairs_compose.
      split; intros H'.
      {
        induction s1; simpl in *.
        {
          inversion H'.
        }
        {
          rewrite elem_of_app in H'.
          destruct H' as [H'|H'].
          {
            specialize (IHs1 H').
            destruct IHs1 as [b [Hb1 Hb2]].
            exists b.
            split.
            {
              right. exact Hb1.
            }
            {
              exact Hb2.
            }
          }
          {
            unfold fmap in H'.
            rewrite elem_of_list_fmap in H'.
            destruct H' as [y [Hy1 Hy2]].
            inversion Hy1; clear Hy1; subst.
            unfold list_of_pairs_apply in Hy2.
            unfold fmap in Hy2.
            rewrite elem_of_list_fmap in Hy2.
            destruct Hy2 as [[b c][Hc1 Hc2]].
            simpl in Hc1. subst y.
            unfold filter in Hc2.
            rewrite elem_of_list_filter in Hc2.
            destruct a0 as [a0 b0]. simpl in *.
            destruct Hc2 as [Hc2 Hc3].
            simpl in Hc2. subst b.
            exists b0.
            split.
            {
              left.
            }
            {
              exact Hc3.
            }
          }
        }
      }
      {
        move: a c H'.
        induction s1; intros a' c' H'; simpl.
        {
          destruct H' as [b [Hb1 Hb2]].
          inversion Hb1.  
        }
        {
          destruct H' as [b [Hb1 Hb2]].
          rewrite elem_of_app.
          destruct a as [a'' b'']. simpl in *.
          inversion Hb1; clear Hb1; subst.
          {
            specialize (IHs1 a'' c').
            destruct (decide ((a'',b'') ∈ s1)).
            {
              feed specialize IHs1.
              {
                exists b''. split; assumption.
              }
              left. apply IHs1.
            }
            {
              right.
              unfold fmap.
              rewrite elem_of_list_fmap.
              exists c'.
              split;[reflexivity|].
              unfold list_of_pairs_apply.
              unfold filter.
              rewrite elem_of_list_fmap.
              exists (b'', c').
              split;[reflexivity|].
              rewrite elem_of_list_filter.
              simpl.
              split;[reflexivity|assumption].
            }
          }
          {
            specialize (IHs1 a' c').
            feed specialize IHs1.
            {
              exists b.
              split; assumption.
            }
            left. apply IHs1.
          }
        }
      }
    Qed.

    Program Definition pb_compose {A : Type}
      {_eqd : EqDecision A }
      {_cnd : Countable A }
      (pb1 pb2 : PartialBijection A)
      : PartialBijection A
    := {|
      pbr := list_to_set (list_of_pairs_compose (elements (pbr pb1)) (elements (pbr pb2))) ;
    |}.
    Next Obligation.
      intros A _eqd _cnt pb1 pb2 x y1 y2 H1 H2.
      rewrite elem_of_list_to_set in H1.
      rewrite elem_of_list_to_set in H2.
      rewrite list_of_pairs_compose_correct in H1.
      rewrite list_of_pairs_compose_correct in H2.
      destruct H1 as [B1 [HB11 HB12]].
      destruct H2 as [B2 [HB21 HB22]].
      rewrite elem_of_elements in HB11.
      rewrite elem_of_elements in HB22.
      rewrite elem_of_elements in HB12.
      rewrite elem_of_elements in HB21.

      destruct pb1 as [pbA pbApf1 pbApf2], pb2 as [pbB pbBpf1 pbBpf2].
      simpl in *.
      pose proof (pbApf1 _ _ _ HB11 HB21).
      subst B2.
      pose proof (pbBpf1 _ _ _ HB22 HB12).
      subst y2.
      reflexivity.
    Qed.
    Next Obligation.
    intros A _eqd _cnt pb1 pb2 x y1 y2 H1 H2.
    rewrite elem_of_list_to_set in H1.
    rewrite elem_of_list_to_set in H2.
    rewrite list_of_pairs_compose_correct in H1.
    rewrite list_of_pairs_compose_correct in H2.
    destruct H1 as [B1 [HB11 HB12]].
    destruct H2 as [B2 [HB21 HB22]].
    rewrite elem_of_elements in HB11.
    rewrite elem_of_elements in HB22.
    rewrite elem_of_elements in HB12.
    rewrite elem_of_elements in HB21.

    destruct pb1 as [pbA pbApf1 pbApf2], pb2 as [pbB pbBpf1 pbBpf2].
    simpl in *.
    pose proof (pbBpf2 _ _ _ HB22 HB12).
    subst B2.
    pose proof (pbApf2 _ _ _ HB11 HB21).
    subst y1.
    reflexivity.
  Qed.
  
  Lemma compose_update {A : Type} {_eqd : EqDecision A} {_cnt : Countable A}
    (R1 R2 : PartialBijection A) (x y z : A) :
  pbr (pb_compose (pb_update R1 x y) (pb_update R2 y z))
  ⊆ pbr (pb_update (pb_compose R1 R2) x z).
  Proof.
    destruct R1, R2.
    simpl.
      rewrite elem_of_subseteq.
      intros [e1 e2] H.
      rewrite elem_of_list_to_set in H.
      rewrite list_of_pairs_compose_correct in H.
      destruct H as [e' [He'1 He'2]].
      rewrite elem_of_elements in He'1.
      rewrite elem_of_elements in He'2.
      rewrite elem_of_union in He'1.
      rewrite elem_of_union in He'2.
      rewrite elem_of_filter in He'1.
      rewrite elem_of_filter in He'2.
      rewrite elem_of_singleton in He'1.
      rewrite elem_of_singleton in He'2.
      rewrite elem_of_union.
      rewrite elem_of_filter.
      rewrite elem_of_singleton.
      rewrite elem_of_list_to_set.
      rewrite list_of_pairs_compose_correct.
      setoid_rewrite elem_of_elements.
      unfold unrelated, related in *.
      naive_solver.
  Qed.

  Lemma pb_update_mono {A : Type}
    {_eqd : EqDecision A }
    {_cnd : Countable A }
    (R1 R2 : PartialBijection A)
    (x y : A) :
    pbr R1 ⊆ pbr R2 ->
    pbr (pb_update R1 x y) ⊆ pbr (pb_update R2 x y).
  Proof.
    intros H.
    unfold pb_update. simpl.
    apply union_mono.
    {
      unfold filter.
      rewrite elem_of_subseteq.
      intros aa Haa.
      rewrite elem_of_filter in Haa.
      rewrite elem_of_filter.
      destruct Haa as [H1 H2].
      split;[assumption|].
      set_solver.
    }
    {
      apply reflexivity.
    }
  Qed.


  Lemma alpha'_mono {Σ : Signature}
    (R1 R2 : PartialBijection evar)
    (R'1 R'2 : PartialBijection svar)
    (t u : NamedPattern)
    : 
      pbr R1 ⊆ pbr R2 ->
      pbr R'1 ⊆ pbr R'2 ->
      alpha_equiv' R1 R'1 t u ->
      alpha_equiv' R2 R'2 t u.
  Proof.
    intros H1 H2 Ha.
    move: R2 R'2 H1 H2.
    induction Ha; intros R2 R'2 H1 H2; constructor; auto.
    {
      apply IHHa.
      {
        apply pb_update_mono.
        exact H1.
      }
      {
        apply H2.
      }
    }
    {
      apply IHHa.
      { apply H1. }
      {
        apply pb_update_mono.
        exact H2.
      }
    }
  Qed.


  Lemma compose_alpha' {Σ : Signature}
    (R1 R2 : PartialBijection evar)
    (R'1 R'2 : PartialBijection svar)
    (t u v : NamedPattern):
    alpha_equiv' R1 R'1 t u ->
    alpha_equiv' R2 R'2 u v ->
    alpha_equiv' (pb_compose R1 R2) (pb_compose R'1 R'2) t v.
  Proof.
    intros Htu Huv.
    move : R1 R2 R'1 R'2 t v Htu Huv.
    induction u; intros R1 R2 R'1 R'2 t v Htu Huv; inversion Htu; inversion Huv; clear Htu; clear Huv; subst;
      constructor.
    {
      unfold pb_compose. simpl.
      rewrite elem_of_list_to_set.
      rewrite list_of_pairs_compose_correct.
      exists x.
      do 2 rewrite elem_of_elements.
      split; assumption.
    }
    {
      unfold pb_compose. simpl.
      rewrite elem_of_list_to_set.
      rewrite list_of_pairs_compose_correct.
      exists X.
      do 2 rewrite elem_of_elements.
      split; assumption.
    }
    { naive_solver. }
    { naive_solver. }
    { naive_solver. }
    { naive_solver. }
    { 
      pose proof (H'' := IHu _ _ _ _ _ _ tEu tEu0).
      eapply alpha'_mono;[apply compose_update|idtac|].
      2: apply H''.
      apply reflexivity.
    }
    {
      eapply alpha'_mono;[|apply compose_update|idtac].
      2: apply IHu.
      3: apply tEu0.
      2: apply tEu.
      apply reflexivity.
    }
  Qed.

  Lemma diagonal_mono {A : Type}
  {_eqd : EqDecision A }
  {_cnd : Countable A }
  ( R1 R2 : gset A)
  : R1 ⊆ R2 -> pbr (diagonal R1) ⊆ pbr (diagonal R2).
  Proof.
    intros H.
    unfold diagonal. simpl.
    apply set_map_mono;[|assumption].
    unfold pointwise_relation.
    intros a. reflexivity.
  Qed.


    Lemma collapse_aux_alpha'
      {Σ : Signature}
      (state : CollapseState)
      (nϕ : NamedPattern)
      : alpha_equiv (collapse_aux state nϕ).2 nϕ.
    Proof.
      remember (nsize' nϕ) as sz.
      assert (Hsz: nsize' nϕ <= sz) by lia.
      clear Heqsz.

      move: nϕ Hsz state.
      induction sz; intros nϕ Hsz state; destruct nϕ;
        simpl in *; try lia; try apply lookup_or_leaf_alpha.
      {
        unfold lookup_or_node,lookup_or. simpl.
        repeat case_match.
        {
          subst. simpl.
          rewrite list_find_Some in H.
          destruct H as [H1 [H2 H3]].
          apply alpha_equiv_sym.
          apply H2.
        }
        {
          simpl.
          clear H.

          constructor; simpl; unfold alpha_equiv in *.
          {
            pose proof (IH1 := (IHsz nϕ1 ltac:(lia) state)).
            pose proof (IH2 := (IHsz nϕ2 ltac:(lia) state)).
            pose proof (H1e := alpha_equiv_impl_same_evars _ _ IH1).
            pose proof (H1s := alpha_equiv_impl_same_svars _ _ IH1).
    
            rewrite H1e H1s.

            eapply alpha'_mono;[idtac|idtac|apply IH1].
            {
              apply diagonal_mono.
              rewrite H1e. clear. set_solver.
            }
            {
              apply diagonal_mono.
              rewrite H1s. clear. set_solver.
            }
          }
          {
            erewrite alpha_equiv_impl_same_evars.
            2: apply IHsz; lia.
            erewrite alpha_equiv_impl_same_svars.
            2: apply IHsz; lia.
            
            eapply alpha'_mono.
            3: { eapply IHsz. lia. }
            { apply diagonal_mono. clear. set_solver. } 
            { apply diagonal_mono. clear. set_solver. } 
          }
        }
      }
      {
        unfold lookup_or_node,lookup_or. simpl.
        repeat case_match.
        {
          subst. simpl.
          rewrite list_find_Some in H.
          destruct H as [H1 [H2 H3]].
          apply alpha_equiv_sym.
          apply H2.
        }
        {
          simpl.
          clear H.

          constructor; simpl; unfold alpha_equiv in *.
          {
            pose proof (IH1 := (IHsz nϕ1 ltac:(lia) state)).
            pose proof (IH2 := (IHsz nϕ2 ltac:(lia) state)).
            pose proof (H1e := alpha_equiv_impl_same_evars _ _ IH1).
            pose proof (H1s := alpha_equiv_impl_same_svars _ _ IH1).
    
            rewrite H1e H1s.

            eapply alpha'_mono;[idtac|idtac|apply IH1].
            {
              apply diagonal_mono.
              rewrite H1e. clear. set_solver.
            }
            {
              apply diagonal_mono.
              rewrite H1s. clear. set_solver.
            }
          }
          {
            erewrite alpha_equiv_impl_same_evars.
            2: apply IHsz; lia.
            erewrite alpha_equiv_impl_same_svars.
            2: apply IHsz; lia.
            
            eapply alpha'_mono.
            3: { eapply IHsz. lia. }
            { apply diagonal_mono. clear. set_solver. } 
            { apply diagonal_mono. clear. set_solver. } 
          }
        }
      }
      {
        unfold lookup_or_node,lookup_or. simpl.
        repeat case_match; simpl.
        {
          rewrite list_find_Some in H.
          destruct H as [H1 [H2 H3]].
          apply alpha_equiv_sym.
          apply H2.
        }
        {
          clear H.
          constructor.
          eapply alpha'_mono.
          3: apply IHsz; lia.
          { 
            eapply transitivity.
            {
              eapply diagonal_mono.
              erewrite alpha_equiv_impl_same_evars.
              2: apply IHsz; lia.
              rewrite union_idemp_L.
              apply reflexivity.
            }
            simpl.
            rewrite elem_of_subseteq.
            intros [e1 e2] He1e2.
            rewrite elem_of_map in He1e2.
            destruct He1e2 as [x' [H1 H2]].
            unfold twice in H1. inversion H1. subst. clear H1.
            rewrite elem_of_union.
            rewrite elem_of_singleton.
            destruct (decide (x = x')).
            {
              subst. right. reflexivity.
            }
            {
              rewrite elem_of_filter.
              unfold unrelated,related.
              simpl.
              left.
              split;[naive_solver|].
              rewrite elem_of_map.
              exists x'.
              split;[reflexivity|].
              rewrite elem_of_union.
              left.
              rewrite elem_of_difference.
              rewrite elem_of_singleton.
              split;[|congruence].
              erewrite alpha_equiv_impl_same_evars.
              { exact H2. }
              apply IHsz.
              lia.
            }
          }
          {
            eapply transitivity.
            {
              eapply diagonal_mono.
              erewrite alpha_equiv_impl_same_svars.
              2: apply IHsz; lia.
              rewrite union_idemp_L.
              apply reflexivity.
            }
            simpl.
            rewrite elem_of_subseteq.
            intros [e1 e2] He1e2.
            rewrite elem_of_map in He1e2.
            destruct He1e2 as [x' [H1 H2]].
            unfold twice in H1. inversion H1. subst. clear H1.
            rewrite elem_of_map.
            exists x'.
            split;[reflexivity|].
            rewrite elem_of_union.
            right. assumption.
          }
        }
      }
      {
        unfold lookup_or_node,lookup_or. simpl.
        repeat case_match; simpl.
        {
          rewrite list_find_Some in H.
          destruct H as [H1 [H2 H3]].
          apply alpha_equiv_sym.
          apply H2.
        }
        {
          clear H.
          constructor.
          eapply alpha'_mono.
          3: apply IHsz; lia.
          { 
            eapply transitivity.
            {
              eapply diagonal_mono.
              erewrite alpha_equiv_impl_same_evars.
              2: apply IHsz; lia.
              rewrite union_idemp_L.
              apply reflexivity.
            }
            simpl.
            rewrite elem_of_subseteq.
            intros [e1 e2] He1e2.
            rewrite elem_of_map in He1e2.
            destruct He1e2 as [x' [H1 H2]].
            unfold twice in H1. inversion H1. subst. clear H1.

            rewrite elem_of_map.
            exists x'.
            split;[reflexivity|].
            rewrite elem_of_union.
            right. assumption.
          }
          {
            eapply transitivity.
            {
              eapply diagonal_mono.
              erewrite alpha_equiv_impl_same_svars.
              2: apply IHsz; lia.
              rewrite union_idemp_L.
              apply reflexivity.
            }
            simpl.
            rewrite elem_of_subseteq.
            intros [e1 e2] He1e2.
            rewrite elem_of_map in He1e2.
            destruct He1e2 as [X' [H1 H2]].
            unfold twice in H1. inversion H1. subst. clear H1.
            
            rewrite elem_of_union.
            rewrite elem_of_singleton.
            destruct (decide (X = X')).
            {
              subst. right. reflexivity.
            }
            {
              rewrite elem_of_filter.
              unfold unrelated,related.
              simpl.
              left.
              split;[naive_solver|].
              rewrite elem_of_map.
              exists X'.
              split;[reflexivity|].
              rewrite elem_of_union.
              left.
              rewrite elem_of_difference.
              rewrite elem_of_singleton.
              split;[|congruence].
              erewrite alpha_equiv_impl_same_svars.
              { exact H2. }
              apply IHsz.
              lia.
            }
          }
        }
      }
    Qed.

    Definition alpha_equiv_in_history_are_equal {Σ : Signature}
      (state : CollapseState) : Prop
      := forall (nϕ1 nϕ2 : NamedPattern),
          nϕ1 ∈ (cs_history state) ->
          nϕ2 ∈ (cs_history state) ->
          alpha_equiv nϕ1 nϕ2 ->
          nϕ1 = nϕ2
    .



    Lemma lookup_or_leaf_preserves_aeihae {Σ : Signature} (state : CollapseState)
      (nϕ : NamedPattern) :
      alpha_equiv_in_history_are_equal state ->
      alpha_equiv_in_history_are_equal (lookup_or_leaf state nϕ).1
    .
    Proof.
      intros H.
      unfold lookup_or_leaf,lookup_or_node,lookup_or.
      destruct (list_find (alpha_equiv nϕ) (cs_history state)) eqn:Heq.
      {
        destruct p as [n nϕ'].
        simpl.
        exact H.
      }
      {
        simpl.
        rewrite list_find_None in Heq.
        rewrite Forall_forall in Heq.
        unfold alpha_equiv_in_history_are_equal in *.
        destruct state as [hist].
        simpl in *.
        intros.
        rewrite elem_of_cons in H0.
        rewrite elem_of_cons in H1.
        destruct H0,H1; subst; simpl in *.
        { reflexivity. }
        { 
          specialize (Heq _ H1).
          contradiction.
        }
        {
          specialize (Heq _ H0).
          apply alpha_equiv_sym in H2.
          contradiction.
        }
        {
          apply H; assumption.
        }
      }
    Qed.

    Lemma lookup_or_node_preserves_aeihae {Σ : Signature} (state : CollapseState)
      (nϕ : NamedPattern) :
      alpha_equiv_in_history_are_equal state ->
      alpha_equiv_in_history_are_equal (lookup_or_leaf state nϕ).1
    .
    Proof.
      intros H.
      unfold lookup_or_leaf,lookup_or_node,lookup_or.
      destruct (list_find (alpha_equiv nϕ) (cs_history state)) eqn:Heq.
      {
        destruct p as [n nϕ'].
        simpl.
        exact H.
      }
      {
        simpl.
        rewrite list_find_None in Heq.
        rewrite Forall_forall in Heq.
        unfold alpha_equiv_in_history_are_equal in *.
        destruct state as [hist].
        simpl in *.
        intros.
        rewrite elem_of_cons in H0.
        rewrite elem_of_cons in H1.
        destruct H0,H1; subst; simpl in *.
        { reflexivity. }
        { 
          specialize (Heq _ H1).
          contradiction.
        }
        {
          specialize (Heq _ H0).
          apply alpha_equiv_sym in H2.
          contradiction.
        }
        {
          apply H; assumption.
        }
      }
    Qed.

    Lemma xy_diagonal {A : Type} {_eqd : EqDecision A} {_cnt : Countable A} (x y : A) (S : gset A)
      : (x,y) ∈ pbr (diagonal S) -> x = y.
    Proof.
      intros H.
      unfold diagonal in H. simpl in H.
      rewrite elem_of_map in H.
      destruct H as [x' Hx'].
      unfold twice in Hx'.
      destruct Hx' as [Hx'1 Hx'2].
      inversion Hx'1.
      subst. reflexivity.
    Qed.
(**)
    Lemma collapse_arg_in_history {Σ : Signature} (state : CollapseState) (nϕ : NamedPattern) :
    (collapse_aux state nϕ).2 ∈ cs_history (collapse_aux state nϕ).1
    .
    Proof.
      induction nϕ; simpl; unfold lookup_or_leaf,lookup_or_node,lookup_or;
      repeat case_match; simpl in *; subst;
      match goal with [ H : list_find _ _ = Some _ |- _] => apply list_find_Some in H | _ => idtac end;
      destruct_and?; try solve [left];
      match goal with [ H : _ !! _ = Some _ |- _ ] => apply elem_of_list_lookup_2 in H | _ => idtac end;
      try assumption.
    Qed.

    Lemma history_collapse_aux_subset {Σ : Signature} (state : CollapseState) (nϕ : NamedPattern) :
      cs_history state ⊆ cs_history (collapse_aux state nϕ).1
    .
    Proof.
      move: state.
      induction nϕ; intros state; simpl; unfold lookup_or_leaf,lookup_or_node,lookup_or; simpl;
        repeat case_match; subst; simpl; set_solver.
    Qed.
    
    Definition history_subpattern_closed {Σ : Signature}
      (state : CollapseState) : Prop
      := forall (nϕ1 nϕ2 : NamedPattern),
          is_nsubpattern_of_ind nϕ1 nϕ2 ->
          nϕ2 ∈ (cs_history state) ->
          nϕ1 ∈ (cs_history state)
    .
    
    Lemma collapse_preserves_sc {Σ : Signature} (state : CollapseState) (nϕ : NamedPattern) :
      history_subpattern_closed state ->
      history_subpattern_closed (collapse_aux state nϕ).1
    .
    Proof.
      unfold history_subpattern_closed.
      move: state.
      induction nϕ; intros state H nϕ1' nϕ2' Hsub Hin;
        simpl in *; unfold lookup_or_leaf,lookup_or_node,lookup_or in *; repeat case_match; subst; simpl in *;
        match goal with [ H : list_find _ _ = Some _ |- _] => apply list_find_Some in H | _ => idtac end;
        destruct_and?;
        match goal with [ H : alpha_equiv _ _ |- _] => inversion H; subst; clear H| _ => idtac end;
        match goal with [H : _ ∈ pbr (diagonal _) |- _] => apply xy_diagonal in H; subst | _ => idtac end;
        try solve [eapply H;[apply Hsub|]; assumption];
        match goal with [ H : list_find _ _ = None |- _] => apply list_find_None in H | _ => idtac end;
        rewrite elem_of_cons in Hin; destruct Hin as [Hin|Hin]; subst;
        try solve [(inversion Hsub; clear Hsub; subst; try solve [left];
        try solve [right; assumption])];
        try solve [right; eauto with nocore];
        idtac 
      .
      {
        inversion Hsub; clear Hsub; subst.
        {
          rewrite elem_of_cons.
          left.
          reflexivity.
        }
        {
          rewrite elem_of_cons.
          right.
          unfold elem_of.
          epose proof (Htmp := history_collapse_aux_subset (collapse_aux state nϕ1).1 nϕ2).
          unfold subseteq in Htmp.
          unfold list_subseteq in Htmp.
          apply Htmp.
          eapply IHnϕ1.
          { naive_solver. }
          { eassumption. }
          apply collapse_arg_in_history.
        }
        {
          rewrite elem_of_cons.
          right.
          eapply IHnϕ2.
          { naive_solver. }
          { eassumption. }
          apply collapse_arg_in_history.
        }
      }
      {

        inversion Hsub; clear Hsub; subst.
        {
          rewrite elem_of_cons.
          left.
          reflexivity.
        }
        {
          rewrite elem_of_cons.
          right.
          unfold elem_of.
          epose proof (Htmp := history_collapse_aux_subset (collapse_aux state nϕ1).1 nϕ2).
          unfold subseteq in Htmp.
          unfold list_subseteq in Htmp.
          apply Htmp.
          eapply IHnϕ1.
          { naive_solver. }
          { eassumption. }
          apply collapse_arg_in_history.
        }
        {
          rewrite elem_of_cons.
          right.
          eapply IHnϕ2.
          { naive_solver. }
          { eassumption. }
          apply collapse_arg_in_history.
        }
      }

      {
        rewrite elem_of_cons.
        classical_right.
        inversion Hsub; subst; try contradiction; clear Hsub.
        eapply IHnϕ.
        { naive_solver. }
        { apply H4. }
        apply collapse_arg_in_history.
      }
      {
        rewrite elem_of_cons.
        classical_right.
        inversion Hsub; subst; try contradiction; clear Hsub.
        eapply IHnϕ.
        { naive_solver. }
        { apply H4. }
        apply collapse_arg_in_history.
      }
    Qed.


    Lemma in_history_invert {Σ : Signature} (state : CollapseState) (nϕ1 nϕ2 : NamedPattern) :
      nϕ2 ∈ cs_history (collapse_aux state nϕ1).1 ->
      (forall nϕ2', alpha_equiv nϕ2 nϕ2' -> is_nsubpattern_of_ind nϕ2' nϕ1 -> False) ->
      nϕ2 ∈ cs_history state.
    Proof.
      remember (nsize' nϕ1) as sz.
      assert (Hsz : nsize' nϕ1 <= sz) by lia.
      clear Heqsz.
      move: nϕ1 nϕ2 Hsz state.
      induction sz; intros nϕ1 nϕ2 Hsz state H Hnsubp;
        destruct nϕ1; simpl in *; try lia;
        simpl in *; unfold lookup_or_leaf,lookup_or_node,lookup_or in *;
        repeat case_match; subst; simpl in *; try assumption;
        rewrite elem_of_cons in H; destruct H as [H|H]; try contradiction; try assumption;
        subst; rewrite list_find_None in H0;
        try solve [exfalso; apply Hnsubp; constructor; auto].
      {
        exfalso. eapply Hnsubp;[|constructor;reflexivity]; constructor; simpl; unfold twice;
        rewrite elem_of_map; exists x;split;[reflexivity|clear;set_solver].
      }
      {
        exfalso. eapply Hnsubp;[|constructor;reflexivity]; constructor; simpl; unfold twice;
        rewrite elem_of_map; exists X;split;[reflexivity|clear;set_solver].
      }
      {
        exfalso.  eapply Hnsubp;[|constructor;reflexivity]; constructor.
      }
      {
        exfalso.
        eapply Hnsubp;[|apply nsub_eq; reflexivity].
        constructor.
        {
          eapply alpha'_mono.
          3: { apply collapse_aux_alpha'. }
          { set_solver. }
          { set_solver. }
        }
        {
          eapply alpha'_mono.
          3: { apply collapse_aux_alpha'. }
          { set_solver. }
          { set_solver. }
        }
      }
      {
        eapply IHsz.
        2: eapply IHsz.
        3: apply H.
        1,2: lia.
        {
          intros nϕ2' Halpha Hcontra.
          eapply Hnsubp.
          { apply Halpha. }
          apply nsub_app_r.
          apply Hcontra.
        }
        {
          intros nϕ2' Halpha Hcontra.
          eapply Hnsubp.
          { apply Halpha. }
          apply nsub_app_l.
          apply Hcontra.
        }
      }
      {
        exfalso.  eapply Hnsubp;[|constructor;reflexivity]; constructor.
      }
      {
        exfalso.
        eapply Hnsubp;[|apply nsub_eq; reflexivity].
        constructor.
        {
          eapply alpha'_mono.
          3: { apply collapse_aux_alpha'. }
          { set_solver. }
          { set_solver. }
        }
        {
          eapply alpha'_mono.
          3: { apply collapse_aux_alpha'. }
          { set_solver. }
          { set_solver. }
        }
      }
      {
        eapply IHsz.
        2: eapply IHsz.
        3: apply H.
        1,2: lia.
        {
          intros nϕ2' Halpha Hcontra.
          eapply Hnsubp.
          { apply Halpha. }
          apply nsub_imp_r.
          apply Hcontra.
        }
        {
          intros nϕ2' Halpha Hcontra.
          eapply Hnsubp.
          { apply Halpha. }
          apply nsub_imp_l.
          apply Hcontra.
        }
      }
      {
        exfalso.
        eapply Hnsubp;[|apply nsub_eq; reflexivity].
        constructor.
        eapply alpha'_mono.
        3: { apply collapse_aux_alpha'. }
        { 
          simpl.
          rewrite elem_of_subseteq.
          intros [x1 x2] Hx1x2.
          rewrite elem_of_map in Hx1x2.
          destruct Hx1x2 as [x' [Hx' Hx1x1]].
          inversion Hx'; clear Hx'; subst.
          rewrite elem_of_union.
          classical_left.
          rewrite elem_of_singleton in H.
          rewrite elem_of_filter.
          split.
          { unfold unrelated, related. simpl. naive_solver. }
          rewrite elem_of_map.
          exists x'. split;[reflexivity|].
          set_solver.
        }
        {
          set_solver.
        }
      }
      {
        eapply IHsz.
        2: apply H.
        { lia. }
        repeat intro.
        eapply Hnsubp.
        { apply H1. }
        apply nsub_exists.
        exact H2.
      }
      {

        exfalso.
        eapply Hnsubp;[|apply nsub_eq; reflexivity].
        constructor.
        eapply alpha'_mono.
        3: { apply collapse_aux_alpha'. }
        {
          set_solver.
        }
        { 
          simpl.
          rewrite elem_of_subseteq.
          intros [x1 x2] Hx1x2.
          rewrite elem_of_map in Hx1x2.
          destruct Hx1x2 as [x' [Hx' Hx1x1]].
          inversion Hx'; clear Hx'; subst.
          rewrite elem_of_union.
          classical_left.
          rewrite elem_of_singleton in H.
          rewrite elem_of_filter.
          split.
          { unfold unrelated, related. simpl. naive_solver. }
          rewrite elem_of_map.
          exists x'. split;[reflexivity|].
          set_solver.
        }
      }
      {

        eapply IHsz.
        2: apply H.
        { lia. }
        repeat intro.
        eapply Hnsubp.
        { apply H1. }
        apply nsub_mu.
        exact H2.
      }
    Qed.

    Lemma is_nsubpattern_of_ind_trans {Σ : Signature} (a b c : NamedPattern) :
      is_nsubpattern_of_ind a b ->
      is_nsubpattern_of_ind b c ->
      is_nsubpattern_of_ind a c.
    Proof.
      intros H1 H2.
      move: a H1.
      induction H2; intros a H1; subst; try assumption; try (constructor; naive_solver).
    Qed.

    Definition alpha_normalized {Σ : Signature} (nϕ : NamedPattern) : Prop :=
      forall nϕ1 nϕ2,
        is_nsubpattern_of_ind nϕ1 nϕ ->
        is_nsubpattern_of_ind nϕ2 nϕ ->
        alpha_equiv nϕ1 nϕ2 ->
        nϕ1 = nϕ2
    .

    Definition state_alpha_normalized {Σ : Signature} (state : CollapseState) : Prop :=
      Forall alpha_normalized (cs_history state)
    .


  Program Definition pb_update_iter
  {A : Type}
  {_eqd : EqDecision A}
  {_cnt : Countable A}
  (pb : PartialBijection A)
  (updates : list (prod A A))
  : PartialBijection A :=
    foldr
      (fun (p : (prod A A)) (b : PartialBijection A) => pb_update b p.1 p.2)
      pb updates
  .


  Lemma pb_update_iter_mono 
  {A : Type}
  {_eqd : EqDecision A}
  {_cnt : Countable A}
  (pb1 pb2 : PartialBijection A)
  (u : list (prod A A))
  : pbr pb1 ⊆ pbr pb2 ->
    pbr (pb_update_iter pb1 u) ⊆ pbr (pb_update_iter pb2 u)
  .
  Proof.
    move: pb1 pb2.
    induction u; intros pb1 pb2 H.
    {
      simpl. exact H.
    }
    {
      simpl.
      rewrite elem_of_subseteq.
      intros [x y].
      rewrite 2!elem_of_union.
      rewrite elem_of_singleton.
      rewrite 2!elem_of_filter.
      naive_solver.
    }
  Qed.


  Lemma elem_of_pb_update_iter
  {A : Type}
  {_eqd : EqDecision A}
  {_cnt : Countable A}
  (pb : PartialBijection A)
  (x y : A)
  (u : list (prod A A))
  :
    ((x, y) ∈ pbr (pb_update_iter pb u)) <->
    (((x,y) ∈ pbr pb /\ (x ∉ map fst u) /\ (y ∉ map snd u))
    \/ (exists (i : nat), (u !! i = Some (x, y)) /\
        (
        forall (j : nat),  j < i ->
          forall (x' y' : A), u !! j = Some (x', y') -> x <> x' /\ y <> y'))
    )
  .
  Proof.
    move: pb x y.
    induction u; intros pb x y; simpl in *.
    {
      set_solver.
    }
    {
      specialize (IHu pb x y).
      destruct a as [x' y']. simpl.
      rewrite elem_of_union.
      unfold unrelated,related.
      rewrite elem_of_filter.
      rewrite IHu. clear IHu.
      simpl.
      rewrite elem_of_singleton.
      rewrite 2!elem_of_cons.
      destruct pb. simpl in *.
      split.
      {
        intros [H|H].
        {
          destruct H as [H1 H2].
          destruct H2 as [[H21 [H22 H23]]|H2].
          {
            left. naive_solver.
          }
          {
            destruct H2 as [i [Hi1 Hi2]].
            right.
            exists (S i).
            simpl.
            split;[assumption|].
            intros j Hj x'0 y'0 Hx'0y'0.
            destruct j; simpl in *.
            {
              naive_solver.
            }
            {
              assert (Hji : j < i) by lia.
              specialize (Hi2 j Hji).
              apply Hi2.
              assumption.
            }
          }
        }
        {
          inversion H; clear H; subst.
          destruct (decide ((x', y') ∈ pbr0 ∧ ¬ (x' = x' ∨ x' ∈ map fst u) ∧ ¬ (y' = y' ∨ y' ∈ map snd u))).
          { left; assumption. }
          right.
          apply not_and_or in n.
          exists 0.
          split;[reflexivity|].
          intros j HContra.
          lia.
        }
      }
      {
        intros [H|H].
        {
          naive_solver.
        }
        {
          destruct H as [i [Hi1 Hi2]].
          destruct i; simpl in *.
          {
            inversion Hi1.
            subst. clear Hi1.
            right. reflexivity.
          }
          {

            pose proof (Hi2' := Hi2 0 ltac:(lia) x' y' ltac:(reflexivity)).
            destruct Hi2' as [Hi21 Hi22].
            left.
            split;[naive_solver|].
            destruct (decide ((x, y) ∈ pbr0 ∧ (x ∉ map fst u) ∧ y ∉ map snd u)).
            { left. assumption. }
            right.
            apply not_and_or in n.
            exists i. split;[assumption|].
            intros j Hji x'0 y'0 Huj.
            apply (Hi2 (S j)).
            { lia. }
            simpl. assumption.
          }
        }
      }
    }
  Qed.

    Lemma pb_update_shadow_subseteq
    {A : Type}
    {_eqd : EqDecision A}
    {_cnt : Countable A}
    (pb : PartialBijection A)
    (x y y' : A)
    : pbr (pb_update (pb_update pb x y) x y') ⊆ pbr (pb_update pb x y').
    Proof.
      rewrite elem_of_subseteq.
      setoid_rewrite elem_of_union.
      setoid_rewrite elem_of_filter.
      setoid_rewrite elem_of_singleton.
      unfold unrelated,related. simpl.
      set_solver.
    Qed.

    Lemma pb_update_shadow_subseteq_2
    {A : Type}
    {_eqd : EqDecision A}
    {_cnt : Countable A}
    (pb : PartialBijection A)
    (x x' y : A)
    : pbr (pb_update (pb_update pb x y) x' y) ⊆ pbr (pb_update pb x' y).
    Proof.
      rewrite elem_of_subseteq.
      setoid_rewrite elem_of_union.
      setoid_rewrite elem_of_filter.
      setoid_rewrite elem_of_singleton.
      unfold unrelated,related. simpl.
      set_solver.
    Qed.

    Lemma pb_update_shadow_subseteq_2_iter
    {A : Type}
    {_eqd : EqDecision A}
    {_cnt : Countable A}
    (pb : PartialBijection A)
    (Res : list (prod A A))
    (x x' y : A)
    : pbr (pb_update (pb_update_iter (pb_update pb x y) Res) x' y)
    ⊆ pbr (pb_update (pb_update_iter pb Res) x' y).
    Proof.
      move: x x' y pb.
      induction Res; intros x x' y pb.
      {
        apply pb_update_shadow_subseteq_2.
      }
      {
        simpl in *.
        destruct a as [u v].
        simpl.
        rewrite elem_of_subseteq.
        intros [a b] H.
        rewrite elem_of_union.
        rewrite elem_of_singleton.
        rewrite elem_of_union in H.
        rewrite elem_of_singleton in H.
        destruct H as [H|H].
        2: {
          inversion H; clear H; subst.
          right. reflexivity.
        }
        left.
        rewrite elem_of_filter in H.
        destruct H as [H1 H2].
        rewrite elem_of_filter.
        split;[assumption|].
        unfold unrelated,related in H1. simpl in H1.
        apply not_or_and in H1.
        destruct H1 as [Hx' Hy].
        rewrite elem_of_union in H2.
        rewrite elem_of_singleton in H2.
        rewrite elem_of_union.
        rewrite elem_of_singleton.

        destruct H2 as [H2|H2].
        {
          pose proof (IH1 := IHRes x u y).
          setoid_rewrite elem_of_subseteq in IH1.
          setoid_rewrite elem_of_union in IH1.
          specialize (IH1 pb (a,b)).
          feed specialize IH1.
          {
            left.
            rewrite elem_of_filter in H2.
            destruct H2 as [H21 H22].
            rewrite elem_of_filter.
            split.
            {
              unfold unrelated,related.
              unfold unrelated,related in H21.
              simpl in *.
              tauto.
            }
            exact H22.
          }
          destruct IH1 as [IH1|IH1].
          2: {
            rewrite elem_of_singleton in IH1. inversion IH1. subst. contradiction.
          }
          left.
          rewrite elem_of_filter in IH1.
          rewrite elem_of_filter.
          unfold unrelated,related in IH1.
          simpl in IH1.
          destruct IH1 as [IH11 IH12].
          unfold unrelated,related.
          simpl.
          rewrite elem_of_filter in H2.
          destruct H2 as [H21 H22].
          unfold unrelated,related in H21.
          simpl in H21.
          split.
          { tauto. }
          apply IH12.
        }
        {
          inversion H2. clear H2. subst.
          right. reflexivity.
        }
      }
    Qed.

    Lemma pb_update_shadow_subseteq_iter
    {A : Type}
    {_eqd : EqDecision A}
    {_cnt : Countable A}
    (pb : PartialBijection A)
    (Res : list (prod A A))
    (x y y' : A)
    : pbr (pb_update (pb_update_iter (pb_update pb x y) Res) x y')
    ⊆ pbr (pb_update (pb_update_iter pb Res) x y').
    Proof.
      move: x y y' pb.
      induction Res; intros x y y' pb.
      {
        apply pb_update_shadow_subseteq.
      }
      {
        simpl in *.
        destruct a as [u v].
        simpl.
        rewrite elem_of_subseteq.
        intros [a b] H.
        rewrite elem_of_union.
        rewrite elem_of_singleton.
        rewrite elem_of_union in H.
        rewrite elem_of_singleton in H.
        destruct H as [H|H].
        2: {
          inversion H; clear H; subst.
          right. reflexivity.
        }
        left.
        rewrite elem_of_filter in H.
        destruct H as [H1 H2].
        rewrite elem_of_filter.
        split;[assumption|].
        unfold unrelated,related in H1. simpl in H1.
        apply not_or_and in H1.
        destruct H1 as [Hx' Hy].
        rewrite elem_of_union in H2.
        rewrite elem_of_singleton in H2.
        rewrite elem_of_union.
        rewrite elem_of_singleton.

        destruct H2 as [H2|H2].
        {
          pose proof (IH1 := IHRes x y v).
          setoid_rewrite elem_of_subseteq in IH1.
          setoid_rewrite elem_of_union in IH1.
          specialize (IH1 pb (a,b)).
          feed specialize IH1.
          {
            left.
            rewrite elem_of_filter in H2.
            destruct H2 as [H21 H22].
            rewrite elem_of_filter.
            split.
            {
              unfold unrelated,related.
              unfold unrelated,related in H21.
              simpl in *.
              tauto.
            }
            exact H22.
          }
          destruct IH1 as [IH1|IH1].
          2: {
            rewrite elem_of_singleton in IH1. inversion IH1. subst. contradiction.
          }
          left.
          rewrite elem_of_filter in IH1.
          rewrite elem_of_filter.
          unfold unrelated,related in IH1.
          simpl in IH1.
          destruct IH1 as [IH11 IH12].
          unfold unrelated,related.
          simpl.
          rewrite elem_of_filter in H2.
          destruct H2 as [H21 H22].
          unfold unrelated,related in H21.
          simpl in H21.
          split.
          { tauto. }
          apply IH12.
        }
        {
          inversion H2. clear H2. subst.
          right. reflexivity.
        }
      }
    Qed.

    

    Lemma alpha_equiv'_diagonal' {Σ : Signature}
      (D1 : gset evar) (D1' : gset svar)
      (D2 : gset evar) (D2' : gset svar)
      (a b : NamedPattern)
      (R : list (prod evar evar))
      (R' : list (prod svar svar))
      :
      (set_map (@twice evar) (named_free_evars a ∪ named_free_evars b))
        ⊆ ((set_map (@twice evar) D2) ∪ (@list_to_set (prod evar evar) (gset (prod evar evar)) _ _ _ R)) ->
      (set_map (@twice svar) (named_free_svars a ∪ named_free_svars b))
        ⊆ ((set_map (@twice svar) D2') ∪ (@list_to_set (prod svar svar) (gset (prod svar svar)) _ _ _  R')) ->
      alpha_equiv' (pb_update_iter (diagonal D1) R) (pb_update_iter (diagonal D1') R') a b ->
      alpha_equiv' (pb_update_iter (diagonal D2) R) (pb_update_iter (diagonal D2') R') a b
    .
    Proof.
      intros Hev2 Hsv2 H.
      
      remember (pb_update_iter (diagonal D1) R) as R1.
      remember (pb_update_iter (diagonal D1') R') as R1'.
      assert (HR1 : pbr R1 ⊆ pbr (pb_update_iter (diagonal D1) R)) by set_solver.
      assert (HR1' : pbr R1' ⊆ pbr (pb_update_iter (diagonal D1') R')) by set_solver.
      clear HeqR1 HeqR1'.

      remember (diagonal D2) as R2.
      remember (diagonal D2') as R2'.
      assert (HR2 : pbr (diagonal D2) ⊆ pbr R2) by set_solver.
      assert (HR2' : pbr (diagonal D2') ⊆ pbr R2') by set_solver.
      clear HeqR2 HeqR2'.

      move: D1 D1' R R' HR1 HR1' D2 D2' Hev2 Hsv2 R2 R2' HR2 HR2'.
      induction H;
        intros D1 D1' Res Res' HR1 HR1' D2 D2' Hev2 Hsv2 R2 R2' HR2 HR2';
        simpl in *.
      {
        constructor.
        assert (H1 : (x, y) ∈ pbr (pb_update_iter (diagonal D1) Res)).
        {
          clear -pf HR1.
          set_solver.
        }
        
        rewrite elem_of_pb_update_iter in H1.

        rewrite elem_of_pb_update_iter.
        destruct H1 as [[H1 [H2 H3]]|H1].
        {
          left.
          repeat split; try assumption.
          unfold diagonal in H1. simpl in H1.
          rewrite elem_of_map in H1.
          destruct H1 as [e [He1 He2]].
          unfold twice in He1. inversion He1. subst.
          eapply elem_of_weaken;[|apply HR2]. clear HR2.
          rewrite elem_of_map. exists e.
          split;[reflexivity|].
          clear -Hev2 H2 H3.
          rewrite union_idemp_L in Hev2.
          unfold twice in Hev2.
          rewrite set_map_singleton_L in Hev2.
          rewrite elem_of_subseteq in Hev2.
          specialize (Hev2 (e, e) ltac:(set_solver)).
          rewrite elem_of_union in Hev2.
          destruct Hev2 as [Hev2|Hev2].
          { set_solver. }
          exfalso.
          rewrite elem_of_list_to_set in Hev2.
          clear -H2 Hev2.
          (* There should be a lemma for this *)
          induction Res; simpl; set_solver.
        }
        {
          destruct H1 as [i [Hresi H1]].
          right.
          exists i.
          split;[assumption|].
          naive_solver.
        }
      }
      {
        constructor.
        assert (H1 : (X, Y) ∈ pbr (pb_update_iter (diagonal D1') Res')).
        {
          clear -pf HR1'.
          set_solver.
        }
        
        rewrite elem_of_pb_update_iter in H1.

        rewrite elem_of_pb_update_iter.
        destruct H1 as [[H1 [H2 H3]]|H1].
        {
          left.
          repeat split; try assumption.
          unfold diagonal in H1. simpl in H1.
          rewrite elem_of_map in H1.
          destruct H1 as [e [He1 He2]].
          unfold twice in He1. inversion He1. subst.
          eapply elem_of_weaken;[|apply HR2']. clear HR2'.
          rewrite elem_of_map. exists e.
          split;[reflexivity|].
          clear -Hsv2 H2 H3.
          rewrite union_idemp_L in Hsv2.
          unfold twice in Hsv2.
          rewrite set_map_singleton_L in Hsv2.
          rewrite elem_of_subseteq in Hsv2.
          specialize (Hsv2 (e, e) ltac:(set_solver)).
          rewrite elem_of_union in Hsv2.
          destruct Hsv2 as [Hsv2|Hsv2].
          { set_solver. }
          exfalso.
          rewrite elem_of_list_to_set in Hsv2.
          clear -H2 Hsv2.
          (* There should be a lemma for this *)
          induction Res'; simpl; set_solver.
        }
        {
          destruct H1 as [i [Hresi H1]].
          right.
          exists i.
          split;[assumption|].
          naive_solver.
        }
      }
      {
        constructor.
        {
          specialize (IHalpha_equiv'1 D1 D1' Res Res' HR1 HR1' D2 D2').
          apply IHalpha_equiv'1.
          { set_solver. }
          { set_solver. }
          { assumption. }
          { assumption. }
        }
        {
          specialize (IHalpha_equiv'2 D1 D1' Res Res' HR1 HR1' D2 D2').
          apply IHalpha_equiv'2.
          { set_solver. }
          { set_solver. }
          { assumption. }
          { assumption. }
        }
      }
      {
        constructor.
        {
          specialize (IHalpha_equiv'1 D1 D1' Res Res' HR1 HR1' D2 D2').
          apply IHalpha_equiv'1.
          { set_solver. }
          { set_solver. }
          { assumption. }
          { assumption. }
        }
        {
          specialize (IHalpha_equiv'2 D1 D1' Res Res' HR1 HR1' D2 D2').
          apply IHalpha_equiv'2.
          { set_solver. }
          { set_solver. }
          { assumption. }
          { assumption. }
        }
      }
      { constructor. }
      { constructor. }
      {
        constructor.

      
        pose proof (IH := IHalpha_equiv' D1 D1' ((x,y)::Res) Res').
        feed specialize IH.
        {
          rewrite elem_of_subseteq.
          intros x0 Hx0.
          destruct x0 as [e1 e2]. simpl in *.
          rewrite elem_of_union in Hx0.
          simpl.
          rewrite elem_of_union.
          destruct Hx0 as [Hx0 | Hx0].
          {
            left.
            (* This follows from the monotonicity of filter,
               but there is no such lemma in stdpp and i am not interested
               in writing one now
              *)
            rewrite elem_of_filter in Hx0.
            rewrite elem_of_filter.
            destruct Hx0 as [Hx01 Hx02].
            split;[assumption|].
            eapply elem_of_weaken in Hx02;[|apply HR1].
            exact Hx02.
          }
          {
            right.
            assumption.
          }
        }
        { assumption. }
        specialize (IH (D2 ∪ {[x;y]} ) D2').
        feed specialize IH.
        { simpl.


          rewrite !set_map_union_L.
          rewrite elem_of_subseteq.
          intros [e1 e2] He1e2.
          assert (e1 = e2).
          {
            rewrite elem_of_union in He1e2.
            destruct He1e2 as [He1e2|He1e2];rewrite elem_of_map in He1e2;
              destruct He1e2 as [x'' [H1x'' H2x'']];
              unfold twice in H1x''; inversion H1x''; subst;
              reflexivity.
          }
          subst.
          (* Essentially, this is our goal: *)
          assert (Halmost: e2 = x \/ e2 = y \/ (e2,e2) ∈ Res \/ e2 ∈ D2).
          {

            destruct (decide (e2 = x)).
            { tauto. }
            destruct (decide (e2 = y)).
            { tauto. }
            right. right.
            rewrite elem_of_subseteq in Hev2.
            specialize (Hev2 (e2, e2)).
            feed specialize Hev2.
            {
              rewrite elem_of_union in He1e2.
              destruct He1e2 as [Htu|Htu];
                rewrite elem_of_map in Htu;
                destruct Htu as [e2' [He2' Htu]];
                inversion He2'; clear He2';
                subst e2'.
              {
                rewrite elem_of_map.
                exists e2. split;[reflexivity|].
                rewrite elem_of_union. left.
                rewrite elem_of_difference.
                split;[assumption|].
                rewrite elem_of_singleton.
                congruence.
              }
              {
                rewrite elem_of_map.
                exists e2. split;[reflexivity|].
                rewrite elem_of_union. right.
                rewrite elem_of_difference.
                split;[assumption|].
                rewrite elem_of_singleton.
                congruence.
              }
            }
            rewrite elem_of_union in Hev2.
            rewrite elem_of_map in Hev2.
            destruct Hev2 as [[x'' [Hev21 Hev22]]|Hev2].
            {
              inversion Hev21. clear Hev21. subst.
              right. assumption.
            }
            {
              rewrite elem_of_list_to_set in Hev2.
              left. assumption.
            }
          }
          clear -Halmost.
          unfold twice.
          rewrite !(elem_of_union,elem_of_map,elem_of_singleton,elem_of_list_to_set).
          setoid_rewrite elem_of_singleton.
          naive_solver.
        }
        {
          assumption.
        }
        
        destruct (decide ((x,x) ∈ pbr R2)), (decide ((y,y) ∈ pbr R2)).
        {
          pose proof (IH1 := IH R2 R2').
          feed specialize IH1.
          { set_solver. }
          { apply HR2'. }
          simpl in IH1.
          apply IH1.
        }
        {
          pose proof (IH1 := IH (pb_update R2 y y) R2').
          feed specialize IH1.
          { clear IHalpha_equiv' IH IH1.
            rewrite elem_of_subseteq.
            intros [x' x''] Hx'.
            rewrite elem_of_map in Hx'.
            destruct Hx' as [x00 [Hx00 Hx000]].
            inversion Hx00. clear Hx00. subst.
            rewrite elem_of_union in Hx000.
            destruct Hx000.
            {
              unfold pb_update. simpl.
              rewrite elem_of_union.
              destruct (decide (x00 = y)).
              {
                subst. right. clear. set_solver.
              }
              {
                left. rewrite elem_of_filter.
                unfold unrelated,related. simpl.
                split;[naive_solver|].
                clear -HR2 H0.
                set_solver.
              }
            }
            {
              rewrite elem_of_union in H0.
              rewrite !elem_of_singleton in H0.
              destruct H0; subst.
              { clear -e n. unfold pb_update. simpl.
                rewrite elem_of_union. 
                rewrite elem_of_filter.
                unfold unrelated,related. simpl.
                set_solver.
              }
              {
                clear -e n. unfold pb_update. simpl.
                rewrite elem_of_union. 
                rewrite elem_of_filter.
                set_solver.
              }
            }
          }
          { apply HR2'. }
          simpl in IH1.

          pose proof (Htmp' := @pb_update_shadow_subseteq_2_iter _ _ _ R2 Res y x y).
          eapply alpha'_mono in IH1.
          3: apply reflexivity.
          2: apply Htmp'.
          apply IH1.
        }
        {
          pose proof (IH1 := IH (pb_update R2 x x) R2').
          feed specialize IH1.
          { clear IHalpha_equiv' IH IH1.
            rewrite elem_of_subseteq.
            intros [x' x''] Hx'.
            rewrite elem_of_map in Hx'.
            destruct Hx' as [x00 [Hx00 Hx000]].
            inversion Hx00. clear Hx00. subst.
            rewrite elem_of_union in Hx000.
            destruct Hx000.
            {
              unfold pb_update. simpl.
              rewrite elem_of_union.
              destruct (decide (x00 = x)).
              {
                subst. right. clear. set_solver.
              }
              {
                left. rewrite elem_of_filter.
                unfold unrelated,related. simpl.
                split;[naive_solver|].
                clear -HR2 H0.
                set_solver.
              }
            }
            {
              rewrite elem_of_union in H0.
              rewrite !elem_of_singleton in H0.
              destruct H0; subst.
              { clear -e n. unfold pb_update. simpl.
                rewrite elem_of_union. 
                rewrite elem_of_filter.
                unfold unrelated,related. simpl.
                set_solver.
              }
              {
                clear -e n. unfold pb_update. simpl.
                rewrite elem_of_union. 
                rewrite elem_of_filter.
                unfold unrelated,related. simpl.
                set_solver.
              }
            }
          }
          { apply HR2'. }
          simpl in IH1.

          pose proof (Htmp' := @pb_update_shadow_subseteq_iter _ _ _ R2 Res x x y).
          eapply alpha'_mono in IH1.
          3: apply reflexivity.
          2: apply Htmp'.
          apply IH1.
        }
        {
          pose proof (IH1 := IH (pb_update (pb_update R2 x x) y y) R2').
          feed specialize IH1.
          { clear IHalpha_equiv' IH IH1.
            rewrite elem_of_subseteq.
            intros [x' x''] Hx'.
            rewrite elem_of_map in Hx'.
            destruct Hx' as [x00 [Hx00 Hx000]].
            inversion Hx00. clear Hx00. subst.
            rewrite elem_of_union in Hx000.
            destruct Hx000 as [Hx000|Hx000].
            {
              unfold pb_update. simpl.
              rewrite elem_of_union.
              destruct (decide (x00 = y)).
              {
                subst. right. clear. set_solver.
              }
              {
                left. rewrite elem_of_filter.
                unfold unrelated,related. simpl.
                split;[naive_solver|].
                rewrite elem_of_union.
                destruct (decide (x00 = x)).
                {
                  subst. right. clear. set_solver.
                }
                left.
                rewrite elem_of_filter.
                simpl.
                split;[naive_solver|].
                clear -HR2 Hx000.
                set_solver.
              }
            }
            {
              rewrite elem_of_union in Hx000.
              rewrite !elem_of_singleton in Hx000.
              destruct Hx000; subst.
              {
                unfold pb_update. simpl.
                rewrite elem_of_union. 
                rewrite elem_of_filter.
                unfold unrelated,related. simpl.
                destruct (decide (x = y)).
                {
                  subst. right. clear. set_solver.
                }
                {
                  left.
                  split;[naive_solver|].
                  rewrite elem_of_union.
                  right. clear. set_solver.
                }
              }
              {
                unfold pb_update. simpl.
                rewrite elem_of_union. 
                rewrite elem_of_filter.
                right.
                clear. set_solver.
              }
            }
          }
          { apply HR2'. }
          simpl in IH1.

          pose proof (Htmp' := @pb_update_shadow_subseteq_2_iter _ _ _ (pb_update R2 x x) Res y x y).
          eapply alpha'_mono in IH1.
          3: apply reflexivity.
          2: apply Htmp'.
          clear Htmp'.
          pose proof (Htmp' := @pb_update_shadow_subseteq_iter _ _ _ R2 Res x x y).
          eapply alpha'_mono in IH1.
          3: apply reflexivity.
          2: apply Htmp'.
          clear Htmp'.
          apply IH1.
        }
      }
      constructor.
      pose proof (IH := IHalpha_equiv' D1 D1' Res ((X,Y)::Res')).
      feed specialize IH.
      { assumption. }
      {
        rewrite elem_of_subseteq.
        intros x0 Hx0.
        destruct x0 as [e1 e2]. simpl in *.
        rewrite elem_of_union in Hx0.
        simpl.
        rewrite elem_of_union.
        destruct Hx0 as [Hx0 | Hx0].
        {
          left.
          (* This follows from the monotonicity of filter,
             but there is no such lemma in stdpp and i am not interested
             in writing one now
            *)
          rewrite elem_of_filter in Hx0.
          rewrite elem_of_filter.
          destruct Hx0 as [Hx01 Hx02].
          split;[assumption|].
          eapply elem_of_weaken in Hx02;[|apply HR1'].
          exact Hx02.
        }
        {
          right.
          assumption.
        }
      }
      
      specialize (IH D2 (D2' ∪ {[X;Y]} )).
      feed specialize IH.
      { assumption. }
      { simpl.


        rewrite !set_map_union_L.
        rewrite elem_of_subseteq.
        intros [e1 e2] He1e2.
        assert (e1 = e2).
        {
          rewrite elem_of_union in He1e2.
          destruct He1e2 as [He1e2|He1e2];rewrite elem_of_map in He1e2;
            destruct He1e2 as [x'' [H1x'' H2x'']];
            unfold twice in H1x''; inversion H1x''; subst;
            reflexivity.
        }
        subst.
        (* Essentially, this is our goal: *)
        assert (Halmost: e2 = X \/ e2 = Y \/ (e2,e2) ∈ Res' \/ e2 ∈ D2').
        {

          destruct (decide (e2 = X)).
          { tauto. }
          destruct (decide (e2 = Y)).
          { tauto. }
          right. right.
          rewrite elem_of_subseteq in Hev2.
          specialize (Hsv2 (e2, e2)).
          feed specialize Hsv2.
          {
            rewrite elem_of_union in He1e2.
            destruct He1e2 as [Htu|Htu];
              rewrite elem_of_map in Htu;
              destruct Htu as [e2' [He2' Htu]];
              inversion He2'; clear He2';
              subst e2'.
            {
              rewrite elem_of_map.
              exists e2. split;[reflexivity|].
              rewrite elem_of_union. left.
              rewrite elem_of_difference.
              split;[assumption|].
              rewrite elem_of_singleton.
              congruence.
            }
            {
              rewrite elem_of_map.
              exists e2. split;[reflexivity|].
              rewrite elem_of_union. right.
              rewrite elem_of_difference.
              split;[assumption|].
              rewrite elem_of_singleton.
              congruence.
            }
          }
          rewrite elem_of_union in Hsv2.
          rewrite elem_of_map in Hsv2.
          destruct Hsv2 as [[x'' [Hsv21 Hsv22]]|Hsv2].
          {
            inversion Hsv21. clear Hsv21. subst.
            right. assumption.
          }
          {
            rewrite elem_of_list_to_set in Hsv2.
            left. assumption.
          }
        }
        clear -Halmost.
        unfold twice.
        rewrite !(elem_of_union,elem_of_map,elem_of_singleton,elem_of_list_to_set).
        setoid_rewrite elem_of_singleton.
        naive_solver.
      }
      
      destruct (decide ((X,X) ∈ pbr R2')), (decide ((Y,Y) ∈ pbr R2')).
      {
        pose proof (IH1 := IH R2 R2').
        feed specialize IH1.
        { apply HR2. }
        { set_solver. }
        simpl in IH1.
        apply IH1.
      }
      {
        pose proof (IH1 := IH R2 (pb_update R2' Y Y)).
        feed specialize IH1.
        { apply HR2. }
        { clear IHalpha_equiv' IH IH1.
          rewrite elem_of_subseteq.
          intros [x' x''] Hx'.
          rewrite elem_of_map in Hx'.
          destruct Hx' as [x00 [Hx00 Hx000]].
          inversion Hx00. clear Hx00. subst.
          rewrite elem_of_union in Hx000.
          destruct Hx000.
          {
            unfold pb_update. simpl.
            rewrite elem_of_union.
            destruct (decide (x00 = Y)).
            {
              subst. right. clear. set_solver.
            }
            {
              left. rewrite elem_of_filter.
              unfold unrelated,related. simpl.
              split;[naive_solver|].
              clear -HR2' H0.
              set_solver.
            }
          }
          {
            rewrite elem_of_union in H0.
            rewrite !elem_of_singleton in H0.
            destruct H0; subst.
            { clear -e n. unfold pb_update. simpl.
              rewrite elem_of_union. 
              rewrite elem_of_filter.
              unfold unrelated,related. simpl.
              set_solver.
            }
            {
              clear -e n. unfold pb_update. simpl.
              rewrite elem_of_union. 
              rewrite elem_of_filter.
              set_solver.
            }
          }
        }
        simpl in IH1.

        pose proof (Htmp' := @pb_update_shadow_subseteq_2_iter _ _ _ R2' Res' Y X Y).
        eapply alpha'_mono in IH1.
        2: apply reflexivity.
        2: apply Htmp'.
        apply IH1.
      }
      {
        pose proof (IH1 := IH R2 (pb_update R2' X X)).
        feed specialize IH1.
        { apply HR2. }
        { clear IHalpha_equiv' IH IH1.
          rewrite elem_of_subseteq.
          intros [x' x''] Hx'.
          rewrite elem_of_map in Hx'.
          destruct Hx' as [x00 [Hx00 Hx000]].
          inversion Hx00. clear Hx00. subst.
          rewrite elem_of_union in Hx000.
          destruct Hx000.
          {
            unfold pb_update. simpl.
            rewrite elem_of_union.
            destruct (decide (x00 = X)).
            {
              subst. right. clear. set_solver.
            }
            {
              left. rewrite elem_of_filter.
              unfold unrelated,related. simpl.
              split;[naive_solver|].
              clear -HR2' H0.
              set_solver.
            }
          }
          {
            rewrite elem_of_union in H0.
            rewrite !elem_of_singleton in H0.
            destruct H0; subst.
            { clear -e n. unfold pb_update. simpl.
              rewrite elem_of_union. 
              rewrite elem_of_filter.
              unfold unrelated,related. simpl.
              set_solver.
            }
            {
              clear -e n. unfold pb_update. simpl.
              rewrite elem_of_union. 
              rewrite elem_of_filter.
              unfold unrelated,related. simpl.
              set_solver.
            }
          }
        }
        simpl in IH1.

        pose proof (Htmp' := @pb_update_shadow_subseteq_iter _ _ _ R2' Res' X X Y).
        eapply alpha'_mono in IH1.
        2: apply reflexivity.
        2: apply Htmp'.
        apply IH1.
      }
      {
        pose proof (IH1 := IH R2 (pb_update (pb_update R2' X X) Y Y)).
        feed specialize IH1.
        { apply HR2. }
        { clear IHalpha_equiv' IH IH1.
          rewrite elem_of_subseteq.
          intros [x' x''] Hx'.
          rewrite elem_of_map in Hx'.
          destruct Hx' as [x00 [Hx00 Hx000]].
          inversion Hx00. clear Hx00. subst.
          rewrite elem_of_union in Hx000.
          destruct Hx000 as [Hx000|Hx000].
          {
            unfold pb_update. simpl.
            rewrite elem_of_union.
            destruct (decide (x00 = Y)).
            {
              subst. right. clear. set_solver.
            }
            {
              left. rewrite elem_of_filter.
              unfold unrelated,related. simpl.
              split;[naive_solver|].
              rewrite elem_of_union.
              destruct (decide (x00 = X)).
              {
                subst. right. clear. set_solver.
              }
              left.
              rewrite elem_of_filter.
              simpl.
              split;[naive_solver|].
              clear -HR2' Hx000.
              set_solver.
            }
          }
          {
            rewrite elem_of_union in Hx000.
            rewrite !elem_of_singleton in Hx000.
            destruct Hx000; subst.
            {
              unfold pb_update. simpl.
              rewrite elem_of_union. 
              rewrite elem_of_filter.
              unfold unrelated,related. simpl.
              destruct (decide (X = Y)).
              {
                subst. right. clear. set_solver.
              }
              {
                left.
                split;[naive_solver|].
                rewrite elem_of_union.
                right. clear. set_solver.
              }
            }
            {
              unfold pb_update. simpl.
              rewrite elem_of_union. 
              rewrite elem_of_filter.
              right.
              clear. set_solver.
            }
          }
        }
        
        simpl in IH1.

        pose proof (Htmp' := @pb_update_shadow_subseteq_2_iter _ _ _ (pb_update R2' X X) Res' Y X Y).
        eapply alpha'_mono in IH1.
        2: apply reflexivity.
        2: apply Htmp'.
        clear Htmp'.
        pose proof (Htmp' := @pb_update_shadow_subseteq_iter _ _ _ R2' Res' X X Y).
        eapply alpha'_mono in IH1.
        2: apply reflexivity.
        2: apply Htmp'.
        clear Htmp'.
        apply IH1.
      }
    Qed.

    Lemma alpha_equiv'_diagonal {Σ : Signature}
      (D1 : gset evar) (D1' : gset svar)
      (D2 : gset evar) (D2' : gset svar)
      (a b : NamedPattern)
      :
      (named_free_evars a ∪ named_free_evars b) ⊆ D2 ->
      (named_free_svars a ∪ named_free_svars b) ⊆ D2' ->
      alpha_equiv' (diagonal D1) (diagonal D1') a b ->
      alpha_equiv' (diagonal D2) (diagonal D2') a b
    .
    Proof.
      intros H1 H2.
      pose proof (Htmp := alpha_equiv'_diagonal' D1 D1' D2 D2' a b [] []).
      simpl in Htmp.
      apply Htmp.
      {
        rewrite union_empty_r_L.
        eapply set_map_mono.
        2: apply H1.
        constructor.
      }
      {
        rewrite union_empty_r_L.
        eapply set_map_mono.
        2: apply H2.
        constructor.
      }
    Qed.

   
    Ltac simpl_free :=
          repeat (
            repeat match goal with
            | [ H : context [named_free_evars (collapse_aux ?st ?phi).2 ] |- _]
              => rewrite (alpha_equiv_impl_same_evars (collapse_aux st phi).2 phi) in H;
                 [apply collapse_aux_alpha'|]
            | [ H : context [named_free_svars (collapse_aux ?st ?phi).2 ] |- _]
                 => rewrite (alpha_equiv_impl_same_svars (collapse_aux st phi).2 phi) in H;
                    [apply collapse_aux_alpha'|]
            | [ |- context [named_free_evars (collapse_aux ?st ?phi).2 ]]
              => rewrite (alpha_equiv_impl_same_evars (collapse_aux st phi).2 phi);
                 [apply collapse_aux_alpha'|]
            | [ |- context [named_free_svars (collapse_aux ?st ?phi).2 ]]
                 => rewrite (alpha_equiv_impl_same_svars (collapse_aux st phi).2 phi);
                    [apply collapse_aux_alpha'|]
            end
          )
        .
    #[local]
    Hint Constructors is_nsubpattern_of_ind : core.

    Lemma collapse_aux_case_pattern_in_history
      {Σ : Signature} (state : CollapseState) (nϕ nϕ' : NamedPattern) (idx : nat) :
      list_find (alpha_equiv nϕ) (cs_history state) = Some (idx, nϕ') ->
      collapse_aux state nϕ = (state, nϕ').
    Proof.
      intros H.
      destruct nϕ; simpl;
        unfold lookup_or_leaf,lookup_or_node,lookup_or;
        simpl;
        rewrite H;
        reflexivity.
    Qed.

    Lemma alpha_equiv_have_same_size
      {Σ : Signature}
      (a b : NamedPattern) :
      alpha_equiv a b ->
      nsize' a = nsize' b.
    Proof.
      intros H.
      induction H; simpl; lia.
    Qed.

    Lemma subpatterns_have_leq_size
      {Σ : Signature}
      (a b : NamedPattern) :
      is_nsubpattern_of_ind a b ->
      nsize' a <= nsize' b.
    Proof.
      intros Hsub.
      induction Hsub; subst; try contradiction; simpl in *; try lia.
    Qed.

    Fixpoint subdepth {Σ : Signature} (a b : NamedPattern)
      (sub : is_nsubpattern_of_ind a b) : nat
      :=
      match sub with
      | @nsub_eq _ _ _  _=> 0
      | @nsub_app_l _ _ _ _ sub' => S (subdepth _ _ sub')
      | @nsub_app_r _ _ _ _ sub' => S (subdepth _ _ sub')
      | @nsub_imp_l _ _ _ _ sub' => S (subdepth _ _ sub')
      | @nsub_imp_r _ _ _ _ sub' => S (subdepth _ _ sub')
      | @nsub_exists _ _ _ _ sub' => S (subdepth _ _ sub')
      | @nsub_mu _ _ _ _ sub' => S (subdepth _ _ sub')
      end.

    Lemma proper_subpatterns_have_different_size'
      {Σ : Signature}
      (a b : NamedPattern)
      (sub : is_nsubpattern_of_ind a b) :
      nsize' b - nsize' a >= subdepth _ _ sub.
    Proof.
      induction sub.
      { simpl. subst. lia. }
      { simpl.
        pose proof (H2 := subpatterns_have_leq_size _ _ sub).
        lia.
      }
      {
        simpl.
        pose proof (H2 := subpatterns_have_leq_size _ _ sub).
        lia.
      }
      {
        simpl.
        pose proof (H2 := subpatterns_have_leq_size _ _ sub).
        lia.
      }
      {
        simpl.
        pose proof (H2 := subpatterns_have_leq_size _ _ sub).
        lia.
      }
      {
        simpl.
        pose proof (H2 := subpatterns_have_leq_size _ _ sub).
        lia.
      }
      {
        simpl.
        pose proof (H2 := subpatterns_have_leq_size _ _ sub).
        lia.
      }
    Qed.

    Lemma proper_subpatterns_have_different_size
      {Σ : Signature}
      (a b : NamedPattern) :
      is_nsubpattern_of_ind a b ->
      a <> b ->
      nsize' a < nsize' b.
    Proof.
      intros Hsub Hneq.
      pose proof (Hleq := proper_subpatterns_have_different_size' _ _ Hsub).
      induction Hsub; simpl in *; subst; try contradiction; simpl in *;
      try lia.
    Qed.

    Lemma alpha_equiv_and_sub_impl_equal
      {Σ : Signature}
      (a b : NamedPattern) :
      alpha_equiv a b ->
      is_nsubpattern_of_ind a b ->
      a = b.
    Proof.
      intros Halpha Hsub.
      pose proof (Hss := alpha_equiv_have_same_size _ _ Halpha).
      pose proof (Hleq := proper_subpatterns_have_different_size' _ _ Hsub).
      rewrite Hss in Hleq.
      assert (Hsub0 : subdepth a b Hsub = 0) by lia.
      clear -Hsub0 Hsub.
      induction Hsub; simpl in *; try lia.
      subst. reflexivity.
    Qed.


    Lemma diagonal_union
      {A : Type} {_eqd : EqDecision A} {_cnt : Countable A}
      (S T : gset A) :
      pbr (diagonal (S ∪ T)) = pbr (diagonal S) ∪ pbr (diagonal T).
    Proof.
      unfold diagonal. simpl.
      rewrite set_map_union_L.
      reflexivity.
    Qed.

    Lemma alpha'_pbr {Σ : Signature} R1 R1' R2 R2' a b:
      pbr R1 = pbr R2 ->
      pbr R1' = pbr R2' ->
      alpha_equiv' R1 R1' a b ->
      alpha_equiv' R2 R2' a b.
    Proof.
      intros H1 H2 Hae.
      move: R2 R2' H1 H2.
      induction Hae; intros R2 R2' H1 H2; constructor; simpl in *.
      { set_solver. }
      { set_solver. }
      { naive_solver. }
      { naive_solver. }
      { naive_solver. }
      { naive_solver. }
      {
        apply IHHae;[|assumption].
        rewrite H1.
        unfold pb_update.
        simpl.
        reflexivity.
      }
      {
        apply IHHae;[assumption|].
        rewrite H2.
        unfold pb_update.
        simpl.
        reflexivity.
      }
    Qed.


    Lemma pb_compose_diagonal
      {A : Type} {_eqd : EqDecision A} {_cnt : Countable A}
      (S T : gset A) :
      exists (ST : gset A),
        pb_compose (diagonal S) (diagonal T) = (diagonal ST).
    Proof.
      exists (S ∩ T).
      apply pb_eq_dep.
      apply leibniz_equiv.
      induction S using set_ind_L; simpl in *.
      {
        rewrite set_map_empty.
        rewrite elements_empty.
        simpl.
        rewrite intersection_empty_l_L.
        rewrite set_map_empty.
        reflexivity.
      }
      {
        rewrite set_map_union_L.
        rewrite [set_map twice {[x]}]set_map_singleton_L.
        rewrite [twice x]/twice.
        rewrite set_equiv_subseteq.
        rewrite 2!elem_of_subseteq.
        split; intros [u v] Huv.
        {
          rewrite elem_of_list_to_set in Huv.
          rewrite elem_of_list_to_set.
          rewrite list_of_pairs_compose_correct in Huv.
          destruct Huv as [b [Hb1 Hb2]].
          rewrite elem_of_elements in Hb1.
          rewrite elem_of_elements in Hb2.
          rewrite elem_of_map in Hb2.
          destruct Hb2 as [x' [Hx'1 Hx'2]].
          inversion Hx'1. clear Hx'1. subst.
          rewrite elem_of_union in Hb1.
          destruct Hb1 as [Hb1|Hb1].
          {
            rewrite elem_of_singleton in Hb1.
            inversion Hb1. clear Hb1. subst.
            unfold fmap.
            rewrite elem_of_list_fmap.
            exists x.
            split;[reflexivity|].
            rewrite elem_of_elements.
            set_solver.
          }
          {
            rewrite elem_of_map in Hb1.
            destruct Hb1 as [x'' [Hx'' Hx''2]].
            inversion Hx''. clear Hx''. subst.
            unfold fmap.
            rewrite elem_of_list_fmap.
            exists x''.
            split;[reflexivity|].
            rewrite elem_of_elements.
            set_solver.
          }
        }
        {
          rewrite elem_of_map in Huv.
          destruct Huv as [x0 [Hx01 Hx02]].
          inversion Hx01. clear Hx01. subst.
          rewrite elem_of_list_to_set.
          rewrite list_of_pairs_compose_correct.
          rewrite elem_of_intersection in Hx02.
          destruct Hx02 as [H1 H2].
          rewrite elem_of_union in H1.
          setoid_rewrite elem_of_elements.
          destruct H1 as [H1|H1].
          {
            rewrite elem_of_singleton in H1. subst.
            exists x.
            rewrite elem_of_union.
            split.
            {
              set_solver.
            }
            {
              set_solver.
            }
          }
          {
            set_solver.
          }
        }
      }
    Qed.

    Lemma alpha_equiv_trans {Σ : Signature} a b c:
      alpha_equiv a b ->
      alpha_equiv b c ->
      alpha_equiv a c.
    Proof.
      intros H1 H2.
      pose proof (compose_alpha' _ _ _ _ _ _ _ H1 H2).
      unfold alpha_equiv.
      pose proof (He := @pb_compose_diagonal evar _ _ (named_free_evars a ∪ named_free_evars b) (named_free_evars b ∪ named_free_evars c)).
      pose proof (Hs := @pb_compose_diagonal svar _ _ (named_free_svars a ∪ named_free_svars b) (named_free_svars b ∪ named_free_svars c)).
      destruct He as [se Hse].
      destruct Hs as [ss Hss].
      rewrite Hse in H.
      rewrite Hss in H.
      eapply alpha_equiv'_diagonal.
      3: apply H.
      { apply reflexivity. }{ apply reflexivity. }
    Qed.

    Definition no_alpha_duplicates {Σ : Signature} (state : CollapseState) : Prop
    := forall (idx1 idx2 : nat) (nϕ1 nϕ2 : NamedPattern),
      (cs_history state) !! idx1 = Some nϕ1 ->
      (cs_history state) !! idx2 = Some nϕ2 ->
      alpha_equiv nϕ1 nϕ2 ->
      idx1 = idx2
    .

    Definition history_has_only_alpha_subpatterns_of
      {Σ : Signature}
      (nϕ : NamedPattern)
      (state : CollapseState)
      := Forall (fun p => exists (p' : NamedPattern) (pf : is_nsubpattern_of_ind p' nϕ), alpha_equiv p p') (cs_history state)
    .
    
    (*
      Well, this would not be true if we required only exact subpatterns.
      Consider the pattern [∃x.x -> ∃y.y].
      Then the procedure adds [∃x.x -> ∃x.x]
      into the history, which is not a subpattern.
    *)
    Lemma collapse_aux_preserves_hhoso
      {Σ : Signature}
      (Φ : NamedPattern)
      (nϕ : NamedPattern)
      (state : CollapseState)
      :
      is_nsubpattern_of_ind nϕ Φ ->
      history_has_only_alpha_subpatterns_of Φ state ->
      history_has_only_alpha_subpatterns_of Φ (collapse_aux state nϕ).1
    .
    Proof.
      move: state.
      induction nϕ; intros state Hsub Honly; simpl;
        unfold lookup_or_leaf,lookup_or_node,lookup_or; simpl in *;
        repeat case_match; subst; simpl in *; try assumption.
      {
        apply Forall_cons;split;try assumption.
        exists (npatt_evar x).
        unshelve (eexists).
        { assumption. }
        { apply alpha_equiv_refl. }
      }
      {
        apply Forall_cons;split;try assumption.
        exists (npatt_svar X).
        unshelve (eexists).
        { assumption. }
        { apply alpha_equiv_refl. }
      }
      {
        apply Forall_cons;split;try assumption.
        exists (npatt_sym sigma).
        unshelve (eexists).
        { assumption. }
        { apply alpha_equiv_refl. }
      }
      {
        unfold history_has_only_alpha_subpatterns_of in *.
        setoid_rewrite Forall_forall in IHnϕ1.
        setoid_rewrite Forall_forall in IHnϕ2.
        pose proof (IH1 := IHnϕ1 state).
        feed specialize IH1.
        {
          eapply is_nsubpattern_of_ind_trans;[|apply Hsub].
          apply nsub_app_l. apply nsub_eq. reflexivity.
        }
        {
          rewrite Forall_forall in Honly.
          naive_solver.
        }
        pose proof (IH1' := IH1 (collapse_aux state nϕ1).2).
        feed specialize IH1'.
        {
          apply collapse_arg_in_history.
        }
        destruct IH1' as [p1 [Hp1sub Hp'a]].

        pose proof (IH2 := IHnϕ2 (collapse_aux state nϕ1).1).
        feed specialize IH2.
        {
          eapply is_nsubpattern_of_ind_trans;[|apply Hsub].
          apply nsub_app_r. apply nsub_eq. reflexivity.
        }
        {
          apply IH1.
        }
        pose proof (IH2' := IH2 (collapse_aux (collapse_aux state nϕ1).1 nϕ2).2).
        feed specialize IH2'.
        {
          apply collapse_arg_in_history.
        }
        destruct IH2' as [q [Hqsub Hqa]].

        apply Forall_cons;split.
        {
          exists (npatt_app nϕ1 nϕ2).
          unshelve (eexists).
          { apply Hsub. }
          constructor.
          {
            simpl.
            eapply alpha_equiv'_diagonal.
            1,2: set_solver.
            apply collapse_aux_alpha'.
          }
          {
            simpl.
            eapply alpha_equiv'_diagonal.
            1,2: set_solver.
            apply collapse_aux_alpha'.
          }
        }
        {
          rewrite Forall_forall in Honly.
          rewrite Forall_forall.
          naive_solver.
        }
      }
      
      {
        apply Forall_cons;split;try assumption.
        exists (npatt_bott).
        unshelve (eexists).
        { assumption. }
        { apply alpha_equiv_refl. }
      }
      {
        unfold history_has_only_alpha_subpatterns_of in *.
        setoid_rewrite Forall_forall in IHnϕ1.
        setoid_rewrite Forall_forall in IHnϕ2.
        pose proof (IH1 := IHnϕ1 state).
        feed specialize IH1.
        {
          eapply is_nsubpattern_of_ind_trans;[|apply Hsub].
          apply nsub_imp_l. apply nsub_eq. reflexivity.
        }
        {
          rewrite Forall_forall in Honly.
          naive_solver.
        }
        pose proof (IH1' := IH1 (collapse_aux state nϕ1).2).
        feed specialize IH1'.
        {
          apply collapse_arg_in_history.
        }
        destruct IH1' as [p1 [Hp1sub Hp'a]].

        pose proof (IH2 := IHnϕ2 (collapse_aux state nϕ1).1).
        feed specialize IH2.
        {
          eapply is_nsubpattern_of_ind_trans;[|apply Hsub].
          apply nsub_imp_r. apply nsub_eq. reflexivity.
        }
        {
          apply IH1.
        }
        pose proof (IH2' := IH2 (collapse_aux (collapse_aux state nϕ1).1 nϕ2).2).
        feed specialize IH2'.
        {
          apply collapse_arg_in_history.
        }
        destruct IH2' as [q [Hqsub Hqa]].

        apply Forall_cons;split.
        {
          exists (npatt_imp nϕ1 nϕ2).
          unshelve (eexists).
          { apply Hsub. }
          constructor.
          {
            simpl.
            eapply alpha_equiv'_diagonal.
            1,2: set_solver.
            apply collapse_aux_alpha'.
          }
          {
            simpl.
            eapply alpha_equiv'_diagonal.
            1,2: set_solver.
            apply collapse_aux_alpha'.
          }
        }
        {
          rewrite Forall_forall in Honly.
          rewrite Forall_forall.
          naive_solver.
        }
      }
      {
        unfold history_has_only_alpha_subpatterns_of in *.
        setoid_rewrite Forall_forall in IHnϕ.
        pose proof (IH := IHnϕ state).
        feed specialize IH.
        {
          eapply is_nsubpattern_of_ind_trans;[|apply Hsub].
          apply nsub_exists. apply nsub_eq. reflexivity.
        }
        {
          rewrite Forall_forall in Honly.
          naive_solver.
        }

        pose proof (IH' := IH (collapse_aux state nϕ).2).
        feed specialize IH'.
        {
          apply collapse_arg_in_history.
        }
        destruct IH' as [p1 [Hp1sub Hp'a]].

        assert (Henϕp1 : alpha_equiv nϕ p1).
        {
          eapply alpha_equiv_trans.
          2: apply Hp'a.
          apply alpha_equiv_sym.
          apply collapse_aux_alpha'.
        }

        assert (Heexnϕp1 : alpha_equiv (npatt_exists x (collapse_aux state nϕ).2) (npatt_exists x nϕ)).
        {
          constructor.
          eapply alpha'_mono.
          3: eapply alpha_equiv_trans.
          4: apply alpha_equiv_sym; apply Henϕp1.
          3: eapply alpha_equiv_trans.
          3: apply collapse_aux_alpha'.
          3: apply Henϕp1.
          2: simpl; apply reflexivity.
          {
            simpl. clear. unfold unrelated,related.
            rewrite elem_of_subseteq.
            intros [e1 e2] H.
            rewrite elem_of_map in H.
            destruct H as [x' [H1x' H2x']].
            inversion H1x'. subst. clear H1x'.
            rewrite elem_of_union.
            destruct (decide (x' = x)).
            { set_solver. }
            left.
            rewrite elem_of_filter. simpl.
            split;[naive_solver|].
            rewrite elem_of_map.
            exists x'.
            split;[reflexivity|].
            set_solver.
          }
        }

        apply Forall_cons;split.
        {
          exists (npatt_exists x nϕ).
          unshelve (eexists).
          { apply Hsub. }
          apply Heexnϕp1.
        }
        {
          rewrite Forall_forall in Honly.
          rewrite Forall_forall.
          naive_solver.
        }
      }
      {
        unfold history_has_only_alpha_subpatterns_of in *.
        setoid_rewrite Forall_forall in IHnϕ.
        pose proof (IH := IHnϕ state).
        feed specialize IH.
        {
          eapply is_nsubpattern_of_ind_trans;[|apply Hsub].
          apply nsub_mu. apply nsub_eq. reflexivity.
        }
        {
          rewrite Forall_forall in Honly.
          naive_solver.
        }

        pose proof (IH' := IH (collapse_aux state nϕ).2).
        feed specialize IH'.
        {
          apply collapse_arg_in_history.
        }
        destruct IH' as [p1 [Hp1sub Hp'a]].

        assert (Henϕp1 : alpha_equiv nϕ p1).
        {
          eapply alpha_equiv_trans.
          2: apply Hp'a.
          apply alpha_equiv_sym.
          apply collapse_aux_alpha'.
        }

        assert (Heexnϕp1 : alpha_equiv (npatt_mu X (collapse_aux state nϕ).2) (npatt_mu X nϕ)).
        {
          constructor.
          eapply alpha'_mono.
          3: eapply alpha_equiv_trans.
          4: apply alpha_equiv_sym; apply Henϕp1.
          3: eapply alpha_equiv_trans.
          3: apply collapse_aux_alpha'.
          3: apply Henϕp1.
          1: simpl; apply reflexivity.
          {
            simpl. clear. unfold unrelated,related.
            rewrite elem_of_subseteq.
            intros [e1 e2] H.
            rewrite elem_of_map in H.
            destruct H as [x' [H1x' H2x']].
            inversion H1x'. subst. clear H1x'.
            rewrite elem_of_union.
            destruct (decide (x' = X)).
            { set_solver. }
            left.
            rewrite elem_of_filter. simpl.
            split;[naive_solver|].
            rewrite elem_of_map.
            exists x'.
            split;[reflexivity|].
            set_solver.
          }
        }

        apply Forall_cons;split.
        {
          exists (npatt_mu X nϕ).
          unshelve (eexists).
          { apply Hsub. }
          apply Heexnϕp1.
        }
        {
          rewrite Forall_forall in Honly.
          rewrite Forall_forall.
          naive_solver.
        }
      }
    Qed.

    Fixpoint normalize
      {Σ : Signature}
      (evs : EVarSet) (svs : SVarSet)
      (nϕ : NamedPattern) : NamedPattern
    :=
    match nϕ with
    | npatt_bott => npatt_bott
    | npatt_sym s => npatt_sym s
    | npatt_evar x => npatt_evar x
    | npatt_svar X => npatt_svar X
    | npatt_imp nϕ1 nϕ2
      => npatt_imp (normalize evs svs nϕ1) (normalize evs svs nϕ2)
    | npatt_app nϕ1 nϕ2
      => npatt_app (normalize evs svs nϕ1) (normalize evs svs nϕ2)
    | npatt_exists x nϕ'
      =>
      let nϕ'' := normalize evs svs nϕ' in
      let newx := evar_fresh_s (evs ∪ named_evars nϕ'') in
      npatt_exists newx (rename_free_evar nϕ'' x newx)
    | npatt_mu X nϕ'
      =>
      let nϕ'' := normalize evs svs nϕ' in
      let newX := svar_fresh_s (svs ∪ named_svars nϕ'') in
      npatt_mu newX (rename_free_svar nϕ'' X newX)
    end.

    Inductive myeq'
    {Σ : Signature}
    (R : PartialBijection evar)
    (R' : PartialBijection svar)
    : relation NamedPattern
    :=
    | me_evar (x y : evar) (pf : (x, y) ∈ (pbr R))
      : myeq' R R' (npatt_evar x) (npatt_evar y)
    | me_svar (X Y : svar) (pf : (X, Y) ∈ (pbr R'))
      : myeq' R R' (npatt_svar X) (npatt_svar Y)
    | me_app
      (t t' u u' : NamedPattern)
      (tEt' : myeq' R R' t t')
      (uEu' : myeq' R R' u u')
      : myeq' R R' (npatt_app t u) (npatt_app t' u')
    | me_imp
      (t t' u u' : NamedPattern)
      (tEt' : myeq' R R' t t')
      (uEu' : myeq' R R' u u')
      : myeq' R R' (npatt_imp t u) (npatt_imp t' u')
    | me_bott : myeq' R R' npatt_bott npatt_bott
    | me_sym (s : symbols) : myeq' R R' (npatt_sym s) (npatt_sym s) 
    | me_ex (x y : evar) (t u : NamedPattern)
      (tEu : myeq' R R' t u) (xRy : (x, y) ∈ (pbr R))
      : myeq' R R'
        (npatt_exists x t)
        (npatt_exists y u)
    | me_mu (X Y : svar) (t u : NamedPattern)
      (tEu : myeq' R R' t u) (XRY : (X, Y) ∈ (pbr R'))
      : myeq' R R'
        (npatt_mu X t)
        (npatt_mu Y u)
  .

  Lemma myeq'_eq {Σ : Signature} (p q : NamedPattern) R R':
    myeq' (diagonal R) (diagonal R') p q ->
    p = q
  .
  Proof.
    intros H.
    induction H; try solve [subst; reflexivity].
    {
      unfold diagonal in pf. simpl in pf.
      rewrite elem_of_map in pf.
      destruct pf as [x0 [H1x0 H2x0]].
      inversion H1x0. subst. clear H1x0.
      reflexivity.
    }
    {
      unfold diagonal in pf. simpl in pf.
      rewrite elem_of_map in pf.
      destruct pf as [X0 [H1X0 H2X0]].
      inversion H1X0. subst. clear H1X0.
      reflexivity.
    }
    {
      unfold diagonal in xRy. simpl in xRy.
      rewrite elem_of_map in xRy.
      destruct xRy as [X0 [H1X0 H2X0]].
      inversion H1X0. subst. clear H1X0.
      reflexivity.
    }
    {
      unfold diagonal in XRY. simpl in XRY.
      rewrite elem_of_map in XRY.
      destruct XRY as [X0 [H1X0 H2X0]].
      inversion H1X0. subst. clear H1X0.
      reflexivity.
    }
  Qed.


    
  Fixpoint maxEdepth {Σ : Signature} (nϕ : NamedPattern) : nat
  :=
  match nϕ with
    | npatt_bott => 0
    | npatt_sym _ => 0
    | npatt_evar _ => 0
    | npatt_svar _ => 0
    | npatt_imp nϕ1 nϕ2
      => Nat.max (maxEdepth nϕ1) (maxEdepth nϕ2)
    | npatt_app nϕ1 nϕ2
      => Nat.max (maxEdepth nϕ1) (maxEdepth nϕ2)
    | npatt_exists _ nϕ'
      => S (maxEdepth nϕ')
    | npatt_mu X nϕ'
      => maxEdepth nϕ'
    end.

    Fixpoint maxSdepth {Σ : Signature} (nϕ : NamedPattern) : nat
    :=
    match nϕ with
      | npatt_bott => 0
      | npatt_sym _ => 0
      | npatt_evar _ => 0
      | npatt_svar _ => 0
      | npatt_imp nϕ1 nϕ2
        => Nat.max (maxSdepth nϕ1) (maxSdepth nϕ2)
      | npatt_app nϕ1 nϕ2
        => Nat.max (maxSdepth nϕ1) (maxSdepth nϕ2)
      | npatt_exists _ nϕ'
        => (maxSdepth nϕ')
      | npatt_mu X nϕ'
        => S (maxSdepth nϕ')
      end.
    
    Fixpoint evar_shadowing_happens {Σ : Signature} (evs : EVarSet) (nϕ : NamedPattern)
    : Prop
    :=
    match nϕ with
    | npatt_bott => False
    | npatt_sym _ => False
    | npatt_evar _ => False
    | npatt_svar _ => False
    | npatt_imp p q
      => evar_shadowing_happens evs p \/ evar_shadowing_happens evs q
    | npatt_app p q
      => evar_shadowing_happens evs p \/ evar_shadowing_happens evs q
    | npatt_exists x p => x ∈ evs \/ evar_shadowing_happens (evs ∪ {[x]}) p
    | npatt_mu _ p => evar_shadowing_happens evs p
    end.

    Fixpoint svar_shadowing_happens {Σ : Signature} (svs : SVarSet) (nϕ : NamedPattern)
    : Prop
    :=
    match nϕ with
    | npatt_bott => False
    | npatt_sym _ => False
    | npatt_evar _ => False
    | npatt_svar _ => False
    | npatt_imp p q
      => svar_shadowing_happens svs p \/ svar_shadowing_happens svs q
    | npatt_app p q
      => svar_shadowing_happens svs p \/ svar_shadowing_happens svs q
    | npatt_exists _ p => svar_shadowing_happens svs p
    | npatt_mu X p => X ∈ svs \/ svar_shadowing_happens svs p
    end.

  Fixpoint normalize2
    {Σ : Signature}
    (evs : list evar) (defe : evar)
    (svs : list svar) (defs : svar)
    (nϕ : NamedPattern)
  :=
  let go := normalize2 evs defe svs defs in
  match nϕ with
    | npatt_bott => npatt_bott
    | npatt_sym s => npatt_sym s
    | npatt_evar x => npatt_evar x
    | npatt_svar X => npatt_svar X
    | npatt_imp nϕ1 nϕ2
      => npatt_imp (go nϕ1) (go nϕ2)
    | npatt_app nϕ1 nϕ2
      => npatt_app (go nϕ1) (go nϕ2)
    | npatt_exists x nϕ'
      =>
      let nϕ'' := go nϕ' in
      let newx := nth (maxEdepth nϕ'') evs defe in
      npatt_exists newx (rename_free_evar nϕ'' x newx)
    | npatt_mu X nϕ'
      =>
      let nϕ'' := go nϕ' in
      let newX := nth (maxSdepth nϕ'') svs defs in
      npatt_mu newX (rename_free_svar nϕ'' X newX)
    end.

    Lemma alpha_equiv_app {Σ : Signature} (a b c d : NamedPattern) :
      alpha_equiv a b ->
      alpha_equiv c d ->
      alpha_equiv (npatt_app a c) (npatt_app b d)
    .
    Proof.
      intros H1 H2.
      constructor.
      {
        eapply alpha_equiv'_diagonal.
        3: apply H1.
        1,2: set_solver.
      }
      {
        eapply alpha_equiv'_diagonal.
        3: apply H2.
        1,2: set_solver.
      }
    Qed.

  Lemma alpha_equiv_imp {Σ : Signature} (a b c d : NamedPattern) :
    alpha_equiv a b ->
    alpha_equiv c d ->
    alpha_equiv (npatt_imp a c) (npatt_imp b d)
  .
  Proof.
    intros H1 H2.
    constructor.
    {
      eapply alpha_equiv'_diagonal.
      3: apply H1.
      1,2: set_solver.
    }
    {
      eapply alpha_equiv'_diagonal.
      3: apply H2.
      1,2: set_solver.
    }
  Qed.

  Lemma maxEdepth_ae {Σ : Signature} (nϕ1 nϕ2 : NamedPattern) R R':
    alpha_equiv' R R' nϕ1 nϕ2 ->
    maxEdepth nϕ1 = maxEdepth nϕ2
  .
  Proof.
    intros H.
    induction H; simpl in *; lia.
  Qed.

  Lemma maxSdepth_ae {Σ : Signature} (nϕ1 nϕ2 : NamedPattern) R R':
  alpha_equiv' R R' nϕ1 nϕ2 ->
  maxSdepth nϕ1 = maxSdepth nϕ2
  .
  Proof.
    intros H.
    induction H; simpl in *; lia.
  Qed.

  Lemma maxEdepth_rename_fe {Σ : Signature} nϕ x y:
    maxEdepth (rename_free_evar nϕ x y) = maxEdepth nϕ
  .
  Proof.
    induction nϕ; simpl; repeat case_match; simpl in *;
      solve[reflexivity|lia].
  Qed.

  Lemma maxSdepth_rename_fs {Σ : Signature} nϕ x y:
    maxSdepth (rename_free_svar nϕ x y) = maxSdepth nϕ
  .
  Proof.
    induction nϕ; simpl; repeat case_match; simpl in *;
      solve[reflexivity|lia].
  Qed.

  Lemma maxSdepth_rename_fe {Σ : Signature} nϕ x y:
    maxSdepth (rename_free_evar nϕ x y) = maxSdepth nϕ
  .
  Proof.
    induction nϕ; simpl; repeat case_match; simpl in *;
     solve[reflexivity|lia].
  Qed.

  Lemma maxEdepth_rename_fs {Σ : Signature} nϕ x y:
    maxEdepth (rename_free_svar nϕ x y) = maxEdepth nϕ
  .
  Proof.
    induction nϕ; simpl; repeat case_match; simpl in *;
     solve[reflexivity|lia].
  Qed.

  Lemma maxEdepth_normalize2
    {Σ : Signature} evs svs de ds nϕ
    :
    maxEdepth (normalize2 evs de svs ds nϕ) = maxEdepth nϕ
  with
    maxSdepth_normalize2
    {Σ : Signature} evs svs de ds nϕ
    :
    maxSdepth (normalize2 evs de svs ds nϕ) = maxSdepth nϕ
  .
  Proof.
    {
      induction nϕ; simpl; try reflexivity; try lia.
      {
        rewrite IHnϕ.
        rewrite maxEdepth_rename_fe.
        rewrite IHnϕ.
        reflexivity.
      }
      {
        rewrite maxSdepth_normalize2.
        rewrite maxEdepth_rename_fs.
        rewrite IHnϕ.
        reflexivity.
      }
    }
    {
      induction nϕ; simpl; try reflexivity; try lia.
      {
        rewrite maxEdepth_normalize2.
        rewrite maxSdepth_rename_fe.
        rewrite IHnϕ.
        reflexivity.
      }
      {
        rewrite IHnϕ.
        rewrite maxSdepth_rename_fs.
        rewrite IHnϕ.
        reflexivity.
      }
    }
  Qed.

  Lemma bound_evars_rename_free_evar
    {Σ : Signature}
    x y nϕ:
    bound_evars (rename_free_evar nϕ x y) = bound_evars nϕ
  .
  Proof.
    induction nϕ; simpl; try set_solver.
    {
      destruct (decide (x = x0)); reflexivity.
    }
    {
      destruct (decide (x = x0)).
      {
        subst. simpl. reflexivity.
      }
      {
        simpl. rewrite IHnϕ. reflexivity.
      }
    }
  Qed.

  (* If used properly, normalize2 will not use use evars from the far end of the list *)

  Lemma bound_evars_normalize2_monotone 
  {Σ : Signature}
  (evs : list evar) (defe : evar)
  (svs : list svar) (defs : svar)
  (nϕ1 nϕ2 : NamedPattern)
  :
  maxEdepth nϕ2 <= length evs ->
  maxEdepth nϕ1 <= maxEdepth nϕ2 ->
  bound_evars (normalize2 evs defe svs defs nϕ1)
  ⊆ bound_evars (normalize2 evs defe svs defs nϕ2)
  .
  Proof.
    induction nϕ1; simpl in *; intros Hevs Hdepth; try set_solver.
    {
      destruct (decide (maxEdepth nϕ1_1 <= maxEdepth nϕ1_2)).
      {
        rewrite PeanoNat.Nat.max_r in Hdepth;[assumption|].
        specialize (IHnϕ1_1 ltac:(lia) ltac:(lia)).
        set_solver.
      }
      {
        assert (maxEdepth nϕ1_2 <= maxEdepth nϕ1_1) by lia.
        rewrite PeanoNat.Nat.max_l in Hdepth;[assumption|].
        specialize (IHnϕ1_2 ltac:(lia) ltac:(lia)).
        set_solver.
      }
    }
    {
      destruct (decide (maxEdepth nϕ1_1 <= maxEdepth nϕ1_2)).
      {
        rewrite PeanoNat.Nat.max_r in Hdepth;[assumption|].
        specialize (IHnϕ1_1 ltac:(lia) ltac:(lia)).
        set_solver.
      }
      {
        assert (maxEdepth nϕ1_2 <= maxEdepth nϕ1_1) by lia.
        rewrite PeanoNat.Nat.max_l in Hdepth;[assumption|].
        specialize (IHnϕ1_2 ltac:(lia) ltac:(lia)).
        set_solver.
      }
    }
    {
      specialize (IHnϕ1 ltac:(lia) ltac:(lia)).
      rewrite maxEdepth_normalize2.
    }
  Qed.

  Lemma normalize2_uses_only_some_evars 
  {Σ : Signature}
  (evs : list evar) (defe : evar)
  (svs : list svar) (defs : svar)
  (nϕ : NamedPattern)
  :
    maxEdepth nϕ <= length evs ->
    bound_evars (normalize2 evs defe svs defs nϕ) ⊆ list_to_set (take (maxEdepth nϕ) evs)
  .
  Proof.
    induction nϕ; simpl in *; try apply reflexivity.
    {
      destruct (decide (maxEdepth nϕ1 <= maxEdepth nϕ2)).
      {
        rewrite PeanoNat.Nat.max_r;[assumption|].
      }
      
      apply Nat.max_case.
      {

      }
    }
  Qed.

  (*
     When there can be some shadowing?
     1. two quantifiers in the formula, too short list
        evs := []; nϕ := exists x. exists y. ⊥
     2. repeated named variables in the list
        evs := ["x";"y";"x"]; nϕ := exists x. exists y. exists z. ⊥
  *)

  Lemma normalize2_no_shadowing
  {Σ : Signature}
  (evs : list evar) (defe : evar)
  (svs : list svar) (defs : svar)
  (evsB : EVarSet )
  (nϕ : NamedPattern)
  :
    NoDup evs ->
    maxEdepth nϕ <= length evs ->
    evsB ## list_to_set evs ->
    ~ evar_shadowing_happens evsB (normalize2 evs defe svs defs nϕ)
  .
  Proof.
    move: evs evsB.
    induction nϕ; simpl; intros evs evsB HNDe HmE HB; try tauto.
    {
      specialize (IHnϕ1 evs evsB HNDe ltac:(lia) HB).
      specialize (IHnϕ2 evs evsB HNDe ltac:(lia) HB).
      tauto.
    }
    {
      specialize (IHnϕ1 evs evsB HNDe ltac:(lia) HB).
      specialize (IHnϕ2 evs evsB HNDe ltac:(lia) HB).
      tauto.
    }
    {
      rewrite maxEdepth_normalize2.
      intros HContra.
      destruct HContra as [HContra|HContra].
      {
        pose proof (nth_elem_of evs ((maxEdepth nϕ)) defe HmE).
        set_solver.
      }
      {
        pose proof (IH := IHnϕ evs (evsB ∪ {[nth (maxEdepth nϕ) evs defe]}) HNDe).
        feed specialize IH.
        {
          lia.
        }
        {
          cut ((nth (maxEdepth nϕ) evs defe) ∉ evs).
          {
            set_solver.
          }
          rewrite nth_overflow.
        }
      }
      specialize (IHnϕ ltac:(lia)).
      cut (~ (nth (maxEdepth (normalize2 evs defe svs defs nϕ)) evs defe)
      ∈ @list_to_set _ EVarSet _ _ _ evs).
      {
        intros H. left.
        tauto.
    }
  Qed.

(* (x, y) ∈ pbr_update R x y 
   t ≡ ∃ x. t'
   u ≡ ∃ y. u'
   ==>
   =R
 *)
  Lemma meq_rename_strips_update
    {Σ : Signature}
    R R' x y z1 z2 t u:
    (z1, z2) ∈ pbr R ->
    myeq' (pb_update R x y) R' t u ->
    myeq' R R' (rename_free_evar t x z1) (rename_free_evar u y z2)
  .
  Proof.
    remember (pb_update R x y) as Ru.
    assert (HxyRu : (x,y) ∈ pbr Ru).
    {
      subst Ru. unfold pb_update. simpl.
      rewrite elem_of_union.
      rewrite elem_of_filter.
      right. rewrite elem_of_singleton. reflexivity.
    }
    (*
    assert (HRRu : (filter (unrelated (x, y)) (pbr R)) ⊆ pbr Ru).
    {
      subst Ru. unfold pb_update. simpl.
      clear. set_solver.
    }*)
    assert (HRuR : forall (x' y' : evar), unrelated (x, y) (x',y') ->
        (x',y') ∈ pbr Ru -> (x',y') ∈ pbr R).
    {
      subst Ru. unfold pb_update. simpl.
      intros x' y' Hx'y' H.
      rewrite elem_of_union in H.
      rewrite elem_of_filter in H.
      destruct H as [[H1 H2]|H].
      { exact H2. }
      unfold unrelated,related in Hx'y'.
      simpl in *. set_solver.
    }
    clear HeqRu.
    intros HR H.
    move: x y z1 z2 R HR HRuR HxyRu.
    induction H; intros x' y' z1 z2 R HR HRuR Hx'y'Ru.
    {
      simpl in *.
      repeat case_match; subst; constructor; try set_solver.
      {
        exfalso.
        destruct Ru. simpl in *. naive_solver.
      }
      {
        exfalso.
        destruct Ru. simpl in *. naive_solver.
      }
      unfold unrelated,related in HRuR. simpl in HRuR.
      set_solver.
    }
    {
      simpl in *.
      constructor.
      auto with nocore.
    }
    {
      simpl in *.
      constructor; auto with nocore.
    }
    {
      simpl in *.
      constructor; auto with nocore.
    }
    {
      simpl in *.
      constructor.
    }
    {
      simpl in *.
      constructor.
    }
    {
      simpl in *.
      repeat case_match; subst; try solve [constructor; assumption].
      3 : {
        exfalso.
        assert (x' = x) by (
        destruct Ru; simpl in *; naive_solver).
        subst. contradiction.
      }
      2 : {
        exfalso.
        assert (y' = y) by (
        destruct Ru; simpl in *; naive_solver).
        subst. contradiction.
      }
      2: {
        constructor.
        { auto with nocore. }
        { apply HRuR.
          { unfold unrelated, related. naive_solver. }
          { assumption. }
        }
      }
      {
        pose proof (IH := IHmyeq' x y z1 z2 _ HR).
        feed specialize IH.
        { tauto. }
        { exact Hx'y'Ru. }


        pose proof (IHmyeq' x y x y Ru xRy).
        feed specialize H2.
        {
          intros. assumption.
        }
        {
          assumption.
        }

        constructor.
        2: {
          assumption.
        }
      }
    }
  Qed.

  
  Lemma normalize2_good {Σ : Signature} (nϕ1 nϕ2 : NamedPattern) evs defe svs defs R R':
  maxEdepth nϕ1 <= length evs ->
  maxSdepth nϕ1 <= length svs ->
  maxEdepth nϕ2 <= length evs ->
  maxSdepth nϕ2 <= length svs ->
  alpha_equiv' R R' nϕ1 nϕ2 ->
  myeq' R R' (normalize2 evs defe svs defs nϕ1) (normalize2 evs defe svs defs nϕ2)
  .
  Proof.
    intros E1 S1 E2 S2 H.
    induction H; simpl in *.
    7: { 
      feed specialize IHalpha_equiv'.
      { lia. }  
      { lia. }
      { lia. }
      { lia. }
      constructor.
      {
        rewrite !maxEdepth_normalize2.
        erewrite maxEdepth_ae;[|apply H].
        remember ((normalize2 evs defe svs defs t)) as t'.
        remember ((normalize2 evs defe svs defs u)) as u'.
        remember (nth (maxEdepth u) evs defe) as n.
        
      }
    rewrite IHalpha_equiv'. 1,2,3,4: lia. f_equal. }
  Qed.

  Lemma helper {Σ : Signature} nϕ x y:
    alpha_equiv (npatt_exists y (rename_free_evar nϕ x y))
    (npatt_exists x nϕ)

    Lemma normalize2_sound {Σ : Signature} (nϕ : NamedPattern) evs defe svs defs:
      maxEdepth nϕ <= length evs ->
      maxSdepth nϕ <= length svs ->
      alpha_equiv (normalize2 evs defe svs defs nϕ) nϕ
    .
    Proof.
      induction nϕ; simpl; intros HE HS.
      {
        apply alpha_equiv_refl.
      }
      {
        apply alpha_equiv_refl.
      }
      {
        apply alpha_equiv_refl.
      }
      {
        specialize (IHnϕ1 ltac:(lia) ltac:(lia)).
        specialize (IHnϕ2 ltac:(lia) ltac:(lia)).
        eapply alpha_equiv_app; eassumption.
      }
      {
        apply alpha_equiv_refl.
      }
      {
        specialize (IHnϕ1 ltac:(lia) ltac:(lia)).
        specialize (IHnϕ2 ltac:(lia) ltac:(lia)).
        eapply alpha_equiv_imp; eassumption.
      }
      {
        specialize (IHnϕ ltac:(lia) ltac:(lia)).
        remember (normalize2 evs defe svs defs nϕ) as nϕ_2.
        remember (nth (maxEdepth nϕ_2) evs defe) as x_2.
        constructor.
      }
    Qed.

  Module TEST.

  Inductive Symbol := a | b | c .


  #[local]
  Instance Symbol_eqdec : EqDecision Symbol.
  Proof.
    intros s1 s2. unfold Decision. decide equality.
  Defined.

  #[local]
  Instance symbols_countable : Countable Symbol.
  Proof.
    eapply finite_countable.
    Unshelve.
    destruct Symbol_eqdec with (x:=a) (y:=b), Symbol_eqdec with (x:=a) (y:=c).
    - econstructor.
      + apply NoDup_cons_2 with (x:=a) (l:=[]).
        apply not_elem_of_nil.
        constructor.
      + intros. destruct x.
        apply elem_of_list_here.
        rewrite e. apply elem_of_list_here.
        rewrite e0. apply elem_of_list_here.
    - econstructor.
      + apply NoDup_cons_2 with (x:=a) (l:=[c]).
        apply not_elem_of_cons. split. auto. apply not_elem_of_nil.
        constructor. apply not_elem_of_nil.
        constructor.
      + intros. destruct x.
        apply elem_of_list_here.
        rewrite e. apply elem_of_list_here.
        apply elem_of_list_further. apply elem_of_list_here.
    - econstructor.
      + apply NoDup_cons_2 with (x:=a) (l:=[b]).
        apply not_elem_of_cons. split. auto. apply not_elem_of_nil.
        constructor. apply not_elem_of_nil.
        constructor.
      + intros. destruct x.
        apply elem_of_list_here.
        apply elem_of_list_further. apply elem_of_list_here.
        rewrite e. apply elem_of_list_here.
    - econstructor.
      + apply NoDup_cons_2 with (x:=a) (l:=[b; c]).
        apply not_elem_of_cons. split. auto.
        apply not_elem_of_cons. split. auto. apply not_elem_of_nil.
        constructor. apply not_elem_of_cons. split. auto. apply not_elem_of_nil.
        constructor. apply not_elem_of_nil.
        constructor.
      + intros. destruct x.
        apply elem_of_list_here.
        apply elem_of_list_further. apply elem_of_list_here.
        apply elem_of_list_further. apply elem_of_list_further. apply elem_of_list_here.
  Qed.


  #[local]
  Instance Σ : Signature :=
    {| variables := StringMLVariables ;
       symbols := Symbol ;
    |}.

    Definition ex1 : NamedPattern := (npatt_exists "x" (npatt_evar "x")).
    Goal normalize2 [] "defE" [] "defS" ex1
      = npatt_exists "defE" (npatt_evar "defE").
    Proof. reflexivity. Qed.

    Goal normalize2 ["y"] "defE" [] "defS" ex1
      = npatt_exists "y" (npatt_evar "y").
    Proof. reflexivity. Qed.

    Definition ex2 : NamedPattern := npatt_imp (npatt_exists "x" (npatt_evar "x"))
                                               (npatt_exists "y" (npatt_evar "y"))
    .

    Goal normalize2 ["z"] "defE" [] "defS" ex2
    = npatt_imp (npatt_exists "z" (npatt_evar "z"))
                (npatt_exists "z" (npatt_evar "z")).
        Proof. reflexivity. Qed.

    Definition ex3 : NamedPattern :=
      npatt_imp (npatt_exists "x" (npatt_exists "x" (npatt_evar "x")))
                (npatt_exists "y" (npatt_evar "y"))
    .

    Goal normalize2 ["z";"w"] "defE" [] "defS" ex3
    = npatt_imp (npatt_exists "w" (npatt_exists "z" (npatt_evar "z")))
                (npatt_exists "z" (npatt_evar "z")).
        Proof. simpl. reflexivity. Qed.
  End TEST.


  Lemma normalize_same_evar
    {Σ : Signature}
    (t u : NamedPattern)
    R R' evs svs:
    named_evars t ⊆ evs ->
    named_evars u ⊆ evs ->
    alpha_equiv' R R' t u ->
    evs ∪ named_evars (normalize evs svs t) = evs ∪ named_evars (normalize evs svs u)
  .
  Proof.
    intros Ht Hu Ha.
    move: Ht Hu.
    induction Ha; intros Ht Hu; simpl in *.
    {
      set_solver.
    }
    { clear. set_solver. }
    {
      feed specialize IHHa1.
      { set_solver. }
      { set_solver. }
      feed specialize IHHa2.
      { set_solver. }
      { set_solver. }
      set_solver.
    }
    {
      feed specialize IHHa1.
      { set_solver. }
      { set_solver. }
      feed specialize IHHa2.
      { set_solver. }
      { set_solver. }
      set_solver.
    }
    {
      clear. set_solver.
    }
    {
      clear. set_solver.
    }
    {
      feed specialize IHHa.
      { set_solver. } 
      { set_solver. }
      rewrite IHHa.
      (* TODO need a lemma characterizing named_evars of rename_free_evar*)
      (*set_solver.*)
    }
  Qed.


  Lemma normalize_correct' {Σ : Signature}
    (p q : NamedPattern) R R' evs svs:
    named_evars p ⊆ evs ->
    named_evars q ⊆ evs ->
    named_svars p ⊆ svs ->
    named_svars q ⊆ svs ->
    alpha_equiv' R R' p q ->
    myeq' R R' (normalize evs svs p) (normalize evs svs q)
  .
  Proof.
    intros nep neq nsp nsq H.
    move: nep neq nsp nsq.
    induction H; intros nep neq nsp nsq; simpl in *.
    {
      constructor. assumption.
    }
    {
      constructor. assumption.
    }
    {
      constructor.
      {
        apply IHalpha_equiv'1; clear IHalpha_equiv'1 IHalpha_equiv'2; set_solver.
      }
      {
        apply IHalpha_equiv'2; clear IHalpha_equiv'1 IHalpha_equiv'2; set_solver.
      }
    }
    {
      constructor.
      {
        apply IHalpha_equiv'1; clear IHalpha_equiv'1 IHalpha_equiv'2; set_solver.
      }
      {
        apply IHalpha_equiv'2; clear IHalpha_equiv'1 IHalpha_equiv'2; set_solver.
      }
    }
    {
      constructor.
    }
    {
      constructor.
    }
    {
      feed specialize IHalpha_equiv'.
      { clear IHalpha_equiv'; set_solver. }
      { clear IHalpha_equiv'; set_solver. }
      { clear IHalpha_equiv'; set_solver. }
      { clear IHalpha_equiv'; set_solver. }
      constructor.
    }
  Qed.

(*
    (* This is not true, since there may be two alpha-equivalent subpatterns of nϕ
       and the first will get into the prefix before the second is evaluated...
       *)
    Lemma collapse_aux_exists_prefix
      {Σ : Signature}
      (state : CollapseState)
      (nϕ Φ : NamedPattern) :
      is_nsubpattern_of_ind nϕ Φ ->
      history_has_only_alpha_subpatterns_of Φ state ->
      exists (prefix : list NamedPattern) (nψ : NamedPattern),
        Forall (fun p => exists (p' : NamedPattern) (pf : is_nsubpattern_of_ind p' nϕ), (alpha_equiv p p')) prefix /\
        collapse_aux state nϕ = ({| cs_history := prefix ++ (cs_history state) |}, nψ)
        /\ (
          (forall nϕ' nϕ'', alpha_equiv nϕ' nϕ'' -> is_nsubpattern_of_ind nϕ'' nϕ -> nϕ' ∉ cs_history state) ->
          nψ = nϕ /\ head prefix = Some nϕ
        ).
    Proof.
      move: state.
      induction nϕ; intros state HsubΦ Hhhoas.
      {
        destruct (list_find (alpha_equiv (npatt_evar x)) (cs_history state)) eqn:Hfind.
        {
          destruct p as [idx nψ].
          rewrite list_find_Some in Hfind.
          destruct Hfind as [Hfind1 [Hfind2 Hfind3]].
          exists [], nψ.
          split.
          {
            apply Forall_nil. exact I.
          }
          {
            split.
            {
              simpl. unfold lookup_or_leaf,lookup_or_node,lookup_or.
              repeat case_match.
              {
                subst.
                rewrite list_find_Some in H.
                destruct H as [Hfind21 [Hfind22 Hfind23]].
                f_equal.
                {
                  destruct state.
                  reflexivity.
                }
                {
                  destruct (decide (n = idx)).
                  {
                    subst.
                    congruence.
                  }
                  {
                    destruct (decide (n < idx)).
                    {
                      specialize (Hfind3 _ _ Hfind21 l).
                      contradiction.
                    }
                    {
                      specialize (Hfind23 _ _ Hfind1 ltac:(lia)).
                      contradiction.
                    }
                  }
                }
              }
              {
                exfalso.
                rewrite list_find_None in H.
                rewrite Forall_forall in H.
                specialize (H nψ).
                feed specialize H.
                {
                  rewrite elem_of_list_lookup.
                  exists idx. apply Hfind1.
                }
                { apply Hfind2. }
                exact H.
              }
            }
            {
              intros H.
              exfalso.
              eapply H.
              { apply alpha_equiv_sym in Hfind2. apply Hfind2. }
              { apply nsub_eq. reflexivity. }
              { rewrite elem_of_list_lookup. exists idx. apply Hfind1. }
            }
          }
        }
        {
          rewrite list_find_None in Hfind.
          exists [npatt_evar x], (npatt_evar x).
          split.
          {
            apply Forall_cons. split.
            2: { apply Forall_nil. exact I. }
            exists (npatt_evar x).
            constructor.
            {
              apply nsub_eq. reflexivity.
            }
            { apply alpha_equiv_refl. }
          }
          {
            split.
            {
              simpl. unfold lookup_or_leaf,lookup_or_node,lookup_or.
              repeat case_match.
              {
                subst.
                exfalso.
                rewrite -list_find_None in Hfind.
                rewrite Hfind in H.
                inversion H.
              }
              {
                simpl. reflexivity.
              }
            }
            {
              intros H.
              split;[reflexivity|].
              reflexivity.
            }
          }
        }
      }
      {
        destruct (list_find (alpha_equiv (npatt_svar X)) (cs_history state)) eqn:Hfind.
        {
          destruct p as [idx nψ].
          rewrite list_find_Some in Hfind.
          destruct Hfind as [Hfind1 [Hfind2 Hfind3]].
          exists [], nψ.
          split.
          {
            apply Forall_nil. exact I.
          }
          {
            split.
            {
              simpl. unfold lookup_or_leaf,lookup_or_node,lookup_or.
              repeat case_match.
              {
                subst.
                rewrite list_find_Some in H.
                destruct H as [Hfind21 [Hfind22 Hfind23]].
                f_equal.
                {
                  destruct state.
                  reflexivity.
                }
                {
                  destruct (decide (n = idx)).
                  {
                    subst.
                    congruence.
                  }
                  {
                    destruct (decide (n < idx)).
                    {
                      specialize (Hfind3 _ _ Hfind21 l).
                      contradiction.
                    }
                    {
                      specialize (Hfind23 _ _ Hfind1 ltac:(lia)).
                      contradiction.
                    }
                  }
                }
              }
              {
                exfalso.
                rewrite list_find_None in H.
                rewrite Forall_forall in H.
                specialize (H nψ).
                feed specialize H.
                {
                  rewrite elem_of_list_lookup.
                  exists idx. apply Hfind1.
                }
                { apply Hfind2. }
                exact H.
              }
            }
            {
              intros H.
              exfalso.
              eapply H.
              { apply alpha_equiv_sym in Hfind2. apply Hfind2. }
              { apply nsub_eq. reflexivity. }
              { rewrite elem_of_list_lookup. exists idx. apply Hfind1. }
            }
          }
        }
        {
          rewrite list_find_None in Hfind.
          exists [npatt_svar X], (npatt_svar X).
          split.
          {
            apply Forall_cons. split.
            2: { apply Forall_nil. exact I. }
            exists (npatt_svar X).
            constructor.
            {
              apply nsub_eq. reflexivity.
            }
            { apply alpha_equiv_refl. }
          }
          {
            split.
            {
              simpl. unfold lookup_or_leaf,lookup_or_node,lookup_or.
              repeat case_match.
              {
                subst.
                exfalso.
                rewrite -list_find_None in Hfind.
                rewrite Hfind in H.
                inversion H.
              }
              {
                simpl. reflexivity.
              }
            }
            {
              intros H.
              split;[reflexivity|].
              reflexivity.
            }
          }
        }
      }
      {
        destruct (list_find (alpha_equiv (npatt_sym sigma)) (cs_history state)) eqn:Hfind.
        {
          destruct p as [idx nψ].
          rewrite list_find_Some in Hfind.
          destruct Hfind as [Hfind1 [Hfind2 Hfind3]].
          exists [], nψ.
          split.
          {
            apply Forall_nil. exact I.
          }
          {
            split.
            {
              simpl. unfold lookup_or_leaf,lookup_or_node,lookup_or.
              repeat case_match.
              {
                subst.
                rewrite list_find_Some in H.
                destruct H as [Hfind21 [Hfind22 Hfind23]].
                f_equal.
                {
                  destruct state.
                  reflexivity.
                }
                {
                  destruct (decide (n = idx)).
                  {
                    subst.
                    congruence.
                  }
                  {
                    destruct (decide (n < idx)).
                    {
                      specialize (Hfind3 _ _ Hfind21 l).
                      contradiction.
                    }
                    {
                      specialize (Hfind23 _ _ Hfind1 ltac:(lia)).
                      contradiction.
                    }
                  }
                }
              }
              {
                exfalso.
                rewrite list_find_None in H.
                rewrite Forall_forall in H.
                specialize (H nψ).
                feed specialize H.
                {
                  rewrite elem_of_list_lookup.
                  exists idx. apply Hfind1.
                }
                { apply Hfind2. }
                exact H.
              }
            }
            {
              intros H.
              exfalso.
              eapply H.
              { apply alpha_equiv_sym in Hfind2. apply Hfind2. }
              { apply nsub_eq. reflexivity. }
              { rewrite elem_of_list_lookup. exists idx. apply Hfind1. }
            }
          }
        }
        {
          rewrite list_find_None in Hfind.
          exists [npatt_sym sigma], (npatt_sym sigma).
          split.
          {
            apply Forall_cons. split.
            2: { apply Forall_nil. exact I. }
            exists (npatt_sym sigma).
            constructor.
            {
              apply nsub_eq. reflexivity.
            }
            { apply alpha_equiv_refl. }
          }
          {
            split.
            {
              simpl. unfold lookup_or_leaf,lookup_or_node,lookup_or.
              repeat case_match.
              {
                subst.
                exfalso.
                rewrite -list_find_None in Hfind.
                rewrite Hfind in H.
                inversion H.
              }
              {
                simpl. reflexivity.
              }
            }
            {
              intros H.
              split;[reflexivity|].
              reflexivity.
            }
          }
        }
      }
      {
        destruct (list_find (alpha_equiv (npatt_app nϕ1 nϕ2)) (cs_history state)) eqn:Hfind.
        {
          destruct p as [idx nψ].
          exists [], nψ.
          split.
          {
            apply Forall_nil. exact I.
          }
          split.
          {
            simpl. unfold lookup_or_node,lookup_or.
            repeat case_match.
            {
              inversion Hfind. clear Hfind. subst.
              destruct state. reflexivity.
            }
            {
              inversion Hfind.
            }
          }
          {
            intros H.
            exfalso.
            rewrite list_find_Some in Hfind.
            destruct Hfind as [Hfind1 [Hfind2 Hfind3]].
            eapply H.
            { apply alpha_equiv_sym in Hfind2. apply Hfind2. }
            { apply nsub_eq. reflexivity. }
            {
              rewrite elem_of_list_lookup.
              exists idx. apply Hfind1.
            }
          }
        }
        {
          specialize (IHnϕ1 state).
          feed specialize IHnϕ1.
          {
            eapply is_nsubpattern_of_ind_trans.
            2: { apply HsubΦ. }
            { apply nsub_app_l. apply nsub_eq. reflexivity. }
          }
          { apply Hhhoas. }
          destruct IHnϕ1 as [prefix1 [nψ1 [Hrec11 [Hrec12 Hrec13]]]].
          specialize (IHnϕ2 (collapse_aux state nϕ1).1).
          feed specialize IHnϕ2.
          {
            eapply is_nsubpattern_of_ind_trans.
            2: { apply HsubΦ. }
            { apply nsub_app_r. apply nsub_eq. reflexivity. }
          }
          {
            apply collapse_aux_preserves_hhoso; try assumption.
            eapply is_nsubpattern_of_ind_trans.
            2: { apply HsubΦ. }
            { apply nsub_app_l. apply nsub_eq. reflexivity. }
          }
          destruct IHnϕ2 as [prefix2 [nψ2 [Hrec21 [Hrec22 Hrec23]]]].
          pose proof (Ha1 := collapse_aux_alpha' state nϕ1).
          pose proof (Ha2 := collapse_aux_alpha' (collapse_aux state nϕ1).1 nϕ2).
          rewrite Hrec12 in Ha1. simpl in Ha1.
          rewrite Hrec22 in Ha2. simpl in Ha2.
          exists ((npatt_app nψ1 nψ2)::prefix2 ++ prefix1).
          exists (npatt_app nψ1 nψ2).
          split.
          {
            rewrite Forall_cons.
            rewrite Forall_app.
            split.
            {
              exists (npatt_app nϕ1 nϕ2).
              constructor.
              {
                apply nsub_eq. reflexivity.
              }
              {
                (* TODO extract a lemma *)
                constructor.
                {
                  eapply alpha_equiv'_diagonal.
                  3: apply Ha1.
                  1,2: clear; set_solver.
                }
                {
                  eapply alpha_equiv'_diagonal.
                  3: apply Ha2.
                  1,2: clear; set_solver.
                }
              }
            }
            split.
            {
              rewrite Forall_forall.
              rewrite Forall_forall in Hrec21.
              intros np Hnp.
              specialize (Hrec21 np Hnp).
              destruct Hrec21 as [np' [Hsub Hae]].
              exists np'.
              constructor;[|assumption].
              apply nsub_app_r.
              apply Hsub.
            }
            {
              rewrite Forall_forall.
              rewrite Forall_forall in Hrec11.
              intros np Hnp.
              specialize (Hrec11 np Hnp).
              destruct Hrec11 as [np' [Hsub Hae]].
              exists np'.
              constructor;[|assumption].
              apply nsub_app_l.
              apply Hsub.
            }
          }
          split.
          {
            simpl. rewrite Hrec12. simpl.
            rewrite Hrec12 in Hrec22. simpl in Hrec22.
            rewrite Hrec22. simpl.
            unfold lookup_or_node,lookup_or.
            repeat case_match.
            {
              inversion Hfind.
            }
            simpl.
            f_equal.
            destruct state. simpl in *.
            rewrite app_assoc.
            reflexivity.
          }
          {
            intros H.
            feed specialize Hrec13.
            {
              intros nϕ' nϕ'' Hae Hsub Hcontra.
              specialize (H nϕ' nϕ'' Hae).
              feed specialize H.
              {
                apply nsub_app_l. exact Hsub.
              }
              { exact Hcontra. }
              exact H.
            }
            feed specialize Hrec23.
            {
              intros nϕ' nϕ'' Hae Hsub Hcontra.
              rewrite Hrec12 in Hcontra. simpl in Hcontra.
              rewrite elem_of_app in Hcontra.
              destruct Hcontra as [Hcontra|Hcontra].
              2: {
                specialize (H nϕ' nϕ'' Hae).
                feed specialize H.
                { apply nsub_app_r. exact Hsub. }
                { exact Hcontra. }
                exact H.
              }
              {
                
              }
            }
            split.
            {}
          }
        }
      }
    Qed.

*)
(* This is not true either.
   Let state = []
   and nϕ = ((∃ x. x) -> (exists y . y))
   Then ((∃ x. x) -> (exists x. x)) is added to the history.

*)
(*
    Lemma collapse_aux_only_adds_subpatterns
      {Σ : Signature}
      (state : CollapseState)
      (nϕ : NamedPattern) :
    forall nψ,
      (is_nsubpattern_of_ind nψ nϕ -> False) ->
      nψ ∈ cs_history (collapse_aux state nϕ).1 ->
      nψ ∈ cs_history state.
    Proof.
      move: state.
      induction nϕ; intros state nψ Hnotsub Hin;
        simpl in *; unfold lookup_or_leaf,lookup_or_node,lookup_or in *;
        simpl in *; repeat case_match; subst; simpl in *; try assumption;
        rewrite elem_of_cons in Hin; destruct Hin as [Hin|Hin]; try assumption;
        subst.
      { exfalso. apply Hnotsub. constructor. reflexivity. }
      { exfalso. apply Hnotsub. constructor. reflexivity. }
      { exfalso. apply Hnotsub. constructor. reflexivity. }
      { 
        destruct (decide (npatt_app (collapse_aux state nϕ1).2
            (collapse_aux (collapse_aux state nϕ1).1 nϕ2).2
          ∈ cs_history (collapse_aux state nϕ1).1)).
        {
          apply IHnϕ1.
          {
            intros HContra.
            apply subpatterns_have_leq_size in HContra.
            simpl in HContra.
            erewrite alpha_equiv_have_same_size in HContra.
            2: { apply collapse_aux_alpha'. }
            erewrite (alpha_equiv_have_same_size (collapse_aux (collapse_aux state nϕ1).1 nϕ2).2 nϕ2) in HContra.
            2: { apply collapse_aux_alpha'. }
            lia.
          }
          {
            assumption.
          }
        }
        {
          destruct (decide (npatt_app (collapse_aux state nϕ1).2
              (collapse_aux (collapse_aux state nϕ1).1 nϕ2).2
              ∈ cs_history (collapse_aux state nϕ2).1)).
          {
            apply IHnϕ2.
            {
              intros HContra.
              apply subpatterns_have_leq_size in HContra.
              simpl in HContra.
              erewrite alpha_equiv_have_same_size in HContra.
              2: { apply collapse_aux_alpha'. }
              erewrite (alpha_equiv_have_same_size (collapse_aux (collapse_aux state nϕ1).1 nϕ2).2 nϕ2) in HContra.
              2: { apply collapse_aux_alpha'. }
              lia.
            }
            {
              assumption.
            }
          }
          {
            exfalso.
            apply Hnotsub.
            constructor.
            f_equal.
            Search collapse_aux.
          }
        }

        destruct (list_find (alpha_equiv nϕ1) (cs_history state)) eqn:Hfind1.
        {
          destruct p as [idx np].
          erewrite (collapse_aux_case_pattern_in_history state) in Hnotsub;
            [|apply Hfind1].
          simpl in Hnotsub.
          erewrite (collapse_aux_case_pattern_in_history state);
            [|apply Hfind1].
          simpl.

          destruct (list_find (alpha_equiv nϕ2) (cs_history state)) eqn:Hfind2.
          {
            destruct p as [idx' np'].
            erewrite (collapse_aux_case_pattern_in_history state) in Hnotsub;
              [|apply Hfind2].
            simpl in Hnotsub.
            erewrite (collapse_aux_case_pattern_in_history state);
              [|apply Hfind2].
            simpl.

            specialize (IHnϕ1 state (npatt_app np np')).
            apply IHnϕ1.
            {
              intros HContra.
              admit.
            }
          }
        }
        destruct (decide (is_nsubpattern_of_ind ))
        exfalso. apply Hnotsub. constructor. reflexivity. }
      {

      }
      { exfalso. apply Hnotsub. constructor. reflexivity. }
    Qed.
    *)

    Lemma collapse_aux_no_alpha_duplicates {Σ : Signature}
      (state : CollapseState)
      (nϕ : NamedPattern) :
      no_alpha_duplicates state ->
      no_alpha_duplicates (collapse_aux state nϕ).1
    .
    Proof.
      move: state.
      induction nϕ; intros state H; simpl;
        unfold lookup_or_leaf,lookup_or_node,lookup_or; simpl in *;
        repeat case_match; subst; simpl in *;
        try assumption.
      {
        rewrite list_find_None in H0.
        rewrite Forall_forall in H0.
        unfold no_alpha_duplicates.
        simpl.
        intros idx1 idx2 nϕ1 nϕ2 Hidx1 Hidx2 Hae.
        destruct idx1,idx2; simpl in *.
        { reflexivity. }
        {
          exfalso.
          inversion Hidx1. subst.
          eapply H0.
          2: apply Hae.
          rewrite elem_of_list_lookup.
          exists idx2. apply Hidx2.
        }
        {
          exfalso.
          inversion Hidx2. subst.
          eapply H0.
          2: apply alpha_equiv_sym; apply Hae.
          rewrite elem_of_list_lookup.
          exists idx1. apply Hidx1.
        }
        { naive_solver. }
      }
      {
        rewrite list_find_None in H0.
        rewrite Forall_forall in H0.
        unfold no_alpha_duplicates.
        simpl.
        intros idx1 idx2 nϕ1 nϕ2 Hidx1 Hidx2 Hae.
        destruct idx1,idx2; simpl in *.
        { reflexivity. }
        {
          exfalso.
          inversion Hidx1. subst.
          eapply H0.
          2: apply Hae.
          rewrite elem_of_list_lookup.
          exists idx2. apply Hidx2.
        }
        {
          exfalso.
          inversion Hidx2. subst.
          eapply H0.
          2: apply alpha_equiv_sym; apply Hae.
          rewrite elem_of_list_lookup.
          exists idx1. apply Hidx1.
        }
        { naive_solver. }
      }
      {
        rewrite list_find_None in H0.
        rewrite Forall_forall in H0.
        unfold no_alpha_duplicates.
        simpl.
        intros idx1 idx2 nϕ1 nϕ2 Hidx1 Hidx2 Hae.
        destruct idx1,idx2; simpl in *.
        { reflexivity. }
        {
          exfalso.
          inversion Hidx1. subst.
          eapply H0.
          2: apply Hae.
          rewrite elem_of_list_lookup.
          exists idx2. apply Hidx2.
        }
        {
          exfalso.
          inversion Hidx2. subst.
          eapply H0.
          2: apply alpha_equiv_sym; apply Hae.
          rewrite elem_of_list_lookup.
          exists idx1. apply Hidx1.
        }
        { naive_solver. }
      }
      {
        specialize (IHnϕ1 state H).
        specialize (IHnϕ2 _ IHnϕ1).
        unfold no_alpha_duplicates.
        intros idx1 idx2 p q Hp Hq Hpq.
        simpl in *.

        destruct idx1,idx2; simpl in *.
        { reflexivity. }
        {
          inversion Hp. subst. clear Hp.
          (* We need to somehow prove that the state after one or two calls
             does not contain a pattern alpha equivalent to the application.  
           *)
          rewrite list_find_None in H0.
          rewrite Forall_forall in H0.
          exfalso.
          assert (alpha_equiv (collapse_aux state nϕ1).2 nϕ1) by (apply collapse_aux_alpha').
          assert (alpha_equiv (collapse_aux (collapse_aux state nϕ1).1 nϕ2).2 nϕ2) by (apply collapse_aux_alpha').

          assert (Hq' : exists i, cs_history (collapse_aux (collapse_aux state nϕ1).1 nϕ2).1 !! i = Some q).
          { exists idx2. apply Hq. }
          rewrite -elem_of_list_lookup in Hq'.
          (*
          Check in_history_invert.
          apply in_history_invert in Hq'.
          *)
          eapply H0.
          2: eapply alpha_equiv_trans.
          3: apply Hpq.
          2: {

            constructor.
            {
              simpl. simpl_free.
              eapply alpha_equiv'_diagonal.
              1,2: simpl_free; set_solver.
              apply alpha_equiv_sym in H1.
              apply H1.
            }
            {
              simpl. simpl_free.
              eapply alpha_equiv'_diagonal.
              1,2: simpl_free; set_solver.
              apply alpha_equiv_sym in H2.
              apply H2.
            }
          }
          rewrite elem_of_list_lookup.
          exists idx
        }
      }
      {
        rewrite list_find_None in H0.
        rewrite Forall_forall in H0.
        unfold no_alpha_duplicates.
        simpl.
        intros idx1 idx2 nϕ1 nϕ2 Hidx1 Hidx2 Hae.
        destruct idx1,idx2; simpl in *.
        { reflexivity. }
        {
          exfalso.
          inversion Hidx1. subst.
          eapply H0.
          2: apply Hae.
          rewrite elem_of_list_lookup.
          exists idx2. apply Hidx2.
        }
        {
          exfalso.
          inversion Hidx2. subst.
          eapply H0.
          2: apply alpha_equiv_sym; apply Hae.
          rewrite elem_of_list_lookup.
          exists idx1. apply Hidx1.
        }
        { naive_solver. }
      }
    Qed.




    Lemma collapse_aux_subpattern_in_history
      {Σ : Signature}
      (state : CollapseState)
      (nϕ nψ : NamedPattern)
      :
      history_subpattern_closed state ->
      is_nsubpattern_of_ind nψ (collapse_aux state nϕ).2 ->
      exists nψ',
        alpha_equiv nψ nψ' /\
        nψ' ∈ cs_history (collapse_aux state nϕ).1
    .
    Proof.
      move: nψ state.
      induction nϕ; intros nψ state Hhc H; simpl in *;
        unfold lookup_or_leaf,lookup_or_node,lookup_or in *;
        simpl in *;
        repeat case_match;
        subst; simpl in *;
        match goal with
        | [H : list_find _ _ = Some _ |- _] => pose proof H as Hsome; apply list_find_Some in H
        | [H : list_find _ _ = None _ |- _] => pose proof H as Hnone; apply list_find_None in H
        | _ => idtac
        end;
        destruct_and?;
        match goal with
        | [H : alpha_equiv _ _ |- _] => inversion H; clear H
        | _ => idtac
        end;
        subst.
      {
        exists nψ;
        split;[apply alpha_equiv_refl|].
        inversion H. clear H. subst.
        rewrite elem_of_list_lookup; eexists; eassumption.
      }
      {
        exists nψ;
        split;[apply alpha_equiv_refl|].
        inversion H. clear H. subst.
        rewrite elem_of_cons;left;reflexivity.
      }
      {
        exists nψ;
        split;[apply alpha_equiv_refl|].
        inversion H. clear H. subst.
        rewrite elem_of_list_lookup; eexists; eassumption.
      }
      {
        exists nψ;
        split;[apply alpha_equiv_refl|].
        inversion H. clear H. subst.
        rewrite elem_of_cons;left;reflexivity.
      }
      {
        exists nψ;
        split;[apply alpha_equiv_refl|].
        inversion H. clear H. subst.
        rewrite elem_of_list_lookup; eexists; eassumption.
      }
      {
        exists nψ;
        split;[apply alpha_equiv_refl|].
        inversion H. clear H. subst.
        rewrite elem_of_cons;left;reflexivity.
      }
      {
        eapply alpha_equiv'_diagonal in tEt'.
        2,3: apply reflexivity.
        eapply alpha_equiv'_diagonal in uEu'.
        2,3: apply reflexivity.
        fold (alpha_equiv nϕ1 t') in tEt'.
        fold (alpha_equiv nϕ2 u') in uEu'.

        inversion H; clear H; subst.
        {
          exists (npatt_app t' u').
          split;[apply alpha_equiv_refl|].
          rewrite elem_of_list_lookup.
          eexists; eassumption.
        }
        {
          
          pose proof (Hhc' := Hhc t' (npatt_app t' u')).
          unfold history_subpattern_closed in Hhc'.
          feed specialize Hhc'.
          { apply nsub_app_l. apply nsub_eq. reflexivity. }
          { rewrite elem_of_list_lookup. eexists. eassumption. }
          pose proof (Hhc'' := Hhc u' (npatt_app t' u')).
          unfold history_subpattern_closed in Hhc''.
          feed specialize Hhc''.
          { apply nsub_app_r. apply nsub_eq. reflexivity. }
          { rewrite elem_of_list_lookup. eexists. eassumption. }
          (* t' is alpha-equivalent to nϕ1, but we are missing the assumption
             that it is the first such thing in the list.
             In fact, with our current list of hypotheses,
             it might not to be the first one.
             Therefore, we find some t'' which is the first pattern
             alpha-equivalent to nϕ1
          *)

          pose proof (Ht'' := list_find_elem_of (alpha_equiv nϕ1) (cs_history state) _ Hhc' tEt').
          unfold is_Some in Ht''.
          destruct Ht'' as [[idx t''] Ht''].
          pose proof (H2t'' := Ht'').
          rewrite list_find_Some in H2t''.
          destruct H2t'' as [Ht''1 [Ht''2 Ht''3]].

          (*
          pose proof (Hu'' := list_find_elem_of (alpha_equiv nϕ2) (cs_history state) _ Hhc'' uEu').
          unfold is_Some in Hu''.
          destruct Hu'' as [[idx'' u''] Hu''].
          pose proof (H2u'' := Hu'').
          rewrite list_find_Some in H2u''.
          destruct H2u'' as [Hu''1 [Hu''2 Hu''3]].
          *)

          assert (t'' = t').
          {

          }

          pose proof (IH1 := IHnϕ1 nψ state Hhc).
          erewrite collapse_aux_case_pattern_in_history in IH1.
          2: { apply Ht''. }
          simpl in IH1.

          rewrite elem_of_list_lookup in Hhc'.
          pose proof (IH1 := IHnϕ1 t'' state Hhc).
          feed specialize IH1.
          { 
            erewrite collapse_aux_case_pattern_in_history.
            2: { apply Ht''. }
            simpl.
            apply nsub_eq.
            reflexivity.
          }
          destruct IH1 as [nψ' [Ht''nψ' Hnψ'hist]].
          erewrite collapse_aux_case_pattern_in_history in Hnψ'hist.
          2: { apply Ht''. }
          simpl in Hnψ'hist.

          exists t''.
          exists nψ'.
          
          exists n.
        }
      }



      intros Hhist.
      remember (collapse_aux state nϕ).2 as nψ'.
      assert (Hsub1 : is_nsubpattern_of_ind nψ' (collapse_aux state nϕ).2).
      { subst. constructor. reflexivity. }
      clear Heqnψ'.

      remember (collapse_aux state nϕ).1 as l.
      assert (Hl :(cs_history (collapse_aux state nϕ).1) ⊆ (cs_history l)).
      {
        subst.
        apply reflexivity.
      }
      clear Heql.

      intros Hsubp.
      move: Hl.
      induction Hsubp; intros Hl.
      {
        subst.
        assert ((collapse_aux state nϕ).2 ∈ (cs_history (collapse_aux state nϕ).1)).
        { apply collapse_arg_in_history. }
        set_solver.
      }
          
    Qed.

    Lemma collapse_aux_preserves_an
    {Σ : Signature} (state : CollapseState) (nϕ : NamedPattern) :
      (*Forall (fun nϕ' => ~ alpha_equiv nϕ nϕ') (cs_history state) -> *)
      state_alpha_normalized state ->
      state_alpha_normalized (collapse_aux state nϕ).1
    .
    Proof.
      move: state.

      remember (nsize' nϕ) as sz.
      assert (Hsz : nsize' nϕ <= sz) by lia.
      clear Heqsz.
      move: nϕ Hsz.
      induction sz; intros nϕ Hsz state (*Hnoth*) Han.
      {
        destruct nϕ; simpl in Hsz; lia.
      }

      destruct nϕ; simpl in *.
      {
        unfold state_alpha_normalized.
        unfold lookup_or_leaf,lookup_or_node,lookup_or. simpl.
        repeat case_match; simpl.
        { assumption. }
        apply Forall_cons.
        split.
        { unfold alpha_normalized.
          intros nϕ1 nϕ2 Hsubp1 Hsubp2 Hae'.
          inversion Hsubp1; inversion Hsubp2; subst.
          reflexivity.
        }
        { apply Han. }
      }
      {
        unfold state_alpha_normalized.
        unfold lookup_or_leaf,lookup_or_node,lookup_or. simpl.
        repeat case_match; simpl.
        { assumption. }
        apply Forall_cons.
        split.
        { unfold alpha_normalized.
          intros nϕ1 nϕ2 Hsubp1 Hsubp2 Hae'.
          inversion Hsubp1; inversion Hsubp2; subst.
          reflexivity.
        }
        { apply Han. }
      }
      {
        unfold state_alpha_normalized.
        unfold lookup_or_leaf,lookup_or_node,lookup_or. simpl.
        repeat case_match; simpl.
        { assumption. }
        apply Forall_cons.
        split.
        { unfold alpha_normalized.
          intros nϕ1 nϕ2 Hsubp1 Hsubp2 Hae'.
          inversion Hsubp1; inversion Hsubp2; subst.
          reflexivity.
        }
        { apply Han. }
      }
      2: {
        unfold state_alpha_normalized.
        unfold lookup_or_leaf,lookup_or_node,lookup_or. simpl.
        repeat case_match; simpl.
        { assumption. }
        apply Forall_cons.
        split.
        { unfold alpha_normalized.
          intros ?? Hsubp1 Hsubp2 Hae'.
          inversion Hsubp1; inversion Hsubp2; subst.
          reflexivity.
        }
        { apply Han. }
      }
      {
        unfold lookup_or_node,lookup_or; simpl.
        repeat case_match; simpl.
        { apply Han. }
        apply Forall_cons.
        split.
        {
          unfold alpha_normalized.
          intros phi1 phi2 Hsub1 Hsub2 Hae.
          {
            
            inversion Hsub1; inversion Hsub2; clear Hsub1 Hsub2; subst; try reflexivity.
            {
              inversion Hae; clear Hae; subst.
              simpl in *.
              simpl_free.
              eapply alpha_equiv'_diagonal in tEt'.
              2,3: apply reflexivity.
              eapply alpha_equiv'_diagonal in uEu'.
              2,3: apply reflexivity.


              destruct ((list_find (fun nϕ' => alpha_equiv nϕ1 nϕ') (cs_history state))) eqn:Hfind1.
              {
                destruct p as [idx1 nϕ'1].
                erewrite collapse_aux_case_pattern_in_history;[|apply Hfind1].
                simpl.
                erewrite collapse_aux_case_pattern_in_history in tEt';[|apply Hfind1].
                simpl in tEt'.
                erewrite collapse_aux_case_pattern_in_history in H5;[|apply Hfind1].
                simpl in H5.
                erewrite (collapse_aux_case_pattern_in_history state) in uEu';[|apply Hfind1].
                simpl in uEu'.

                destruct ((list_find (fun nϕ' => alpha_equiv nϕ2 nϕ') (cs_history state))) eqn:Hfind2.
                {
                  destruct p as [idx2 nϕ'2].
                  erewrite collapse_aux_case_pattern_in_history;[|apply Hfind2].
                  exfalso.
                  simpl.
                  erewrite (collapse_aux_case_pattern_in_history state) in uEu';[|apply Hfind2].
                  simpl in uEu'.
                  fold (alpha_equiv nϕ'1 t') in tEt'.
                  fold (alpha_equiv nϕ'2 u') in uEu'.
                  assert (Ht'sub : is_nsubpattern_of_ind t' nϕ'1).
                  {
                    eapply is_nsubpattern_of_ind_trans.
                    2: apply H5.
                    apply nsub_app_l.
                    apply nsub_eq.
                    reflexivity.
                  }
                  assert (Hu'sub : is_nsubpattern_of_ind u' nϕ'1).
                  {
                    eapply is_nsubpattern_of_ind_trans.
                    2: apply H5.
                    apply nsub_app_r.
                    apply nsub_eq.
                    reflexivity.
                  }
                  apply alpha_equiv_sym in tEt'.
                  pose proof (alpha_equiv_and_sub_impl_equal _ _ tEt' Ht'sub).
                  subst t'.
                  clear tEt'.
                  clear -H5.
                  apply subpatterns_have_leq_size in H5.
                  simpl in H5. lia.
                }
                {
                  exfalso.
                  rewrite list_find_None in Hfind2.
                  rewrite list_find_None in H.
                  fold (alpha_equiv nϕ'1 t') in tEt'.
                  apply alpha_equiv_sym in tEt'.
                  assert (Ht'sub : is_nsubpattern_of_ind t' nϕ'1).
                  {
                    eapply is_nsubpattern_of_ind_trans.
                    2: apply H5.
                    apply nsub_app_l.
                    apply nsub_eq.
                    reflexivity.
                  }
                  pose proof (alpha_equiv_and_sub_impl_equal _ _ tEt' Ht'sub).
                  subst t'.
                  clear Ht'sub tEt'.
                  f_equal.
                  apply subpatterns_have_leq_size in H5.
                  simpl in H5. lia.
                }
              }
              {
                rewrite list_find_None in Hfind1.
                rewrite list_find_None in H.
                clear H. (* duplicate of Hnoth *)

                assert (Ht'sub : is_nsubpattern_of_ind t' (collapse_aux state nϕ1).2).
                {
                    eapply is_nsubpattern_of_ind_trans.
                    2: apply H5.
                    apply nsub_app_l.
                    apply nsub_eq.
                    reflexivity.
                  }
                assert (Hu'sub : is_nsubpattern_of_ind u' (collapse_aux state nϕ1).2).
                {
                  eapply is_nsubpattern_of_ind_trans.
                  2: apply H5.
                  apply nsub_app_r.
                  apply nsub_eq.
                  reflexivity.
                }
                fold (alpha_equiv (collapse_aux (collapse_aux state nϕ1).1 nϕ2).2 u') in uEu'.
                fold (alpha_equiv ((collapse_aux state nϕ1)).2 t') in tEt'.
                apply alpha_equiv_sym in tEt'.
                apply alpha_equiv_sym in uEu'.
                pose proof (alpha_equiv_and_sub_impl_equal _ _ tEt' Ht'sub).
                subst t'.


                apply subpatterns_have_leq_size in H5.
                simpl in H5.
                lia.  
              }
              
            }
            {
              inversion Hae; clear Hae; subst.
              simpl in *.
              simpl_free.
              eapply alpha_equiv'_diagonal in tEt'.
              2,3: apply reflexivity.
              eapply alpha_equiv'_diagonal in uEu'.
              2,3: apply reflexivity.


              destruct ((list_find (fun nϕ' => alpha_equiv nϕ1 nϕ') (cs_history state))) eqn:Hfind1.
              {
                destruct p as [idx1 nϕ'1].
                erewrite collapse_aux_case_pattern_in_history;[|apply Hfind1].
                simpl.
                erewrite collapse_aux_case_pattern_in_history in tEt';[|apply Hfind1].
                simpl in tEt'.
                erewrite (collapse_aux_case_pattern_in_history state) in H5;[|apply Hfind1].
                simpl in H5.
                erewrite (collapse_aux_case_pattern_in_history state) in uEu';[|apply Hfind1].
                simpl in uEu'.

                destruct ((list_find (fun nϕ' => alpha_equiv nϕ2 nϕ') (cs_history state))) eqn:Hfind2.
                {
                  destruct p as [idx2 nϕ'2].
                  erewrite collapse_aux_case_pattern_in_history;[|apply Hfind2].
                  exfalso.
                  simpl.
                  erewrite (collapse_aux_case_pattern_in_history state) in uEu';[|apply Hfind2].
                  simpl in uEu'.
                  fold (alpha_equiv nϕ'1 t') in tEt'.
                  fold (alpha_equiv nϕ'2 u') in uEu'.
                  erewrite (collapse_aux_case_pattern_in_history state) in H5;[|apply Hfind2].
                  simpl in H5.
                  assert (Ht'sub : is_nsubpattern_of_ind t' nϕ'2).
                  {
                    eapply is_nsubpattern_of_ind_trans.
                    2: apply H5.
                    apply nsub_app_l.
                    apply nsub_eq.
                    reflexivity.
                  }
                  assert (Hu'sub : is_nsubpattern_of_ind u' nϕ'2).
                  {
                    eapply is_nsubpattern_of_ind_trans.
                    2: apply H5.
                    apply nsub_app_r.
                    apply nsub_eq.
                    reflexivity.
                  }
                  apply alpha_equiv_sym in uEu'.
                  pose proof (alpha_equiv_and_sub_impl_equal _ _ uEu' Hu'sub).
                  subst u'.
                  clear -H5.
                  apply subpatterns_have_leq_size in H5.
                  simpl in H5. lia.
                }
                {
                  exfalso.
                  rewrite list_find_None in Hfind2.
                  rewrite list_find_None in H.
                  fold (alpha_equiv nϕ'1 t') in tEt'.
                  fold (alpha_equiv (collapse_aux state nϕ2).2 u') in uEu'.
                  apply alpha_equiv_sym in uEu'.
                  assert (Hu'sub : is_nsubpattern_of_ind u' (collapse_aux state nϕ2).2).
                  {
                    eapply is_nsubpattern_of_ind_trans.
                    2: apply H5.
                    apply nsub_app_r.
                    apply nsub_eq.
                    reflexivity.
                  }
                  pose proof (alpha_equiv_and_sub_impl_equal _ _ uEu' Hu'sub).
                  subst u'.
                  apply subpatterns_have_leq_size in H5.
                  simpl in H5. lia.
                }
              }
              {
                exfalso.
                rewrite list_find_None in Hfind1.
                rewrite list_find_None in H.
                clear H. (* duplicate of Hnoth *)

                assert (Ht'sub : is_nsubpattern_of_ind t' (collapse_aux (collapse_aux state nϕ1).1 nϕ2).2).
                {
                    eapply is_nsubpattern_of_ind_trans.
                    2: apply H5.
                    apply nsub_app_l.
                    apply nsub_eq.
                    reflexivity.
                }
                assert (Hu'sub : is_nsubpattern_of_ind u' (collapse_aux (collapse_aux state nϕ1).1 nϕ2).2).
                {
                  eapply is_nsubpattern_of_ind_trans.
                  2: apply H5.
                  apply nsub_app_r.
                  apply nsub_eq.
                  reflexivity.
                }
                fold (alpha_equiv (collapse_aux (collapse_aux state nϕ1).1 nϕ2).2 u') in uEu'.
                fold (alpha_equiv ((collapse_aux state nϕ1)).2 t') in tEt'.
                apply alpha_equiv_sym in tEt'.
                apply alpha_equiv_sym in uEu'.
                pose proof (alpha_equiv_and_sub_impl_equal _ _ uEu' Hu'sub).
                subst u'.
                apply subpatterns_have_leq_size in H5.
                simpl in H5.
                lia.
              }
            }
            {
              inversion Hae; clear Hae; subst.
              simpl in *.
              simpl_free.
              eapply alpha_equiv'_diagonal in tEt'.
              2,3: apply reflexivity.
              eapply alpha_equiv'_diagonal in uEu'.
              2,3: apply reflexivity.


              destruct ((list_find (fun nϕ' => alpha_equiv nϕ1 nϕ') (cs_history state))) eqn:Hfind1.
              {
                destruct p as [idx1 nϕ'1].
                erewrite collapse_aux_case_pattern_in_history;[|apply Hfind1].
                simpl.
                erewrite collapse_aux_case_pattern_in_history in tEt';[|apply Hfind1].
                simpl in tEt'.
                erewrite collapse_aux_case_pattern_in_history in H2;[|apply Hfind1].
                simpl in H2.
                erewrite (collapse_aux_case_pattern_in_history state) in uEu';[|apply Hfind1].
                simpl in uEu'.

                destruct ((list_find (fun nϕ' => alpha_equiv nϕ2 nϕ') (cs_history state))) eqn:Hfind2.
                {
                  destruct p as [idx2 nϕ'2].
                  erewrite collapse_aux_case_pattern_in_history;[|apply Hfind2].
                  exfalso.
                  simpl.
                  erewrite (collapse_aux_case_pattern_in_history state) in uEu';[|apply Hfind2].
                  simpl in uEu'.
                  fold (alpha_equiv t nϕ'1) in tEt'.
                  fold (alpha_equiv u nϕ'2) in uEu'.
                  assert (Ht'sub : is_nsubpattern_of_ind t nϕ'1).
                  {
                    eapply is_nsubpattern_of_ind_trans.
                    2: apply H2.
                    apply nsub_app_l.
                    apply nsub_eq.
                    reflexivity.
                  }
                  assert (Hu'sub : is_nsubpattern_of_ind u nϕ'1).
                  {
                    eapply is_nsubpattern_of_ind_trans.
                    2: apply H2.
                    apply nsub_app_r.
                    apply nsub_eq.
                    reflexivity.
                  }
                  
                  pose proof (alpha_equiv_and_sub_impl_equal _ _ tEt' Ht'sub).
                  subst t.
                  clear -H2.
                  apply subpatterns_have_leq_size in H2.
                  simpl in H2. lia.
                }
                {
                  exfalso.
                  rewrite list_find_None in Hfind2.
                  rewrite list_find_None in H.
                  fold (alpha_equiv t nϕ'1) in tEt'.
                  
                  assert (Ht'sub : is_nsubpattern_of_ind t nϕ'1).
                  {
                    eapply is_nsubpattern_of_ind_trans.
                    2: apply H2.
                    apply nsub_app_l.
                    apply nsub_eq.
                    reflexivity.
                  }
                  
                  pose proof (alpha_equiv_and_sub_impl_equal _ _ tEt' Ht'sub).
                  subst t.
                  apply subpatterns_have_leq_size in H2.
                  simpl in H2. lia.
                }
              }
              {
                rewrite list_find_None in Hfind1.
                rewrite list_find_None in H.
                clear H. (* duplicate of Hnoth *)

                assert (Ht'sub : is_nsubpattern_of_ind t (collapse_aux state nϕ1).2).
                {
                    eapply is_nsubpattern_of_ind_trans.
                    2: apply H2.
                    apply nsub_app_l.
                    apply nsub_eq.
                    reflexivity.
                }
                assert (Hu'sub : is_nsubpattern_of_ind u (collapse_aux state nϕ1).2).
                {
                  eapply is_nsubpattern_of_ind_trans.
                  2: apply H2.
                  apply nsub_app_r.
                  apply nsub_eq.
                  reflexivity.
                }
                fold (alpha_equiv t ((collapse_aux state nϕ1)).2) in tEt'.
                fold (alpha_equiv u (collapse_aux (collapse_aux state nϕ1).1 nϕ2).2) in uEu'.
                
                pose proof (alpha_equiv_and_sub_impl_equal _ _ tEt' Ht'sub).
                subst t.
                apply subpatterns_have_leq_size in H2.
                simpl in H2.
                lia.  
              }
            }
            {
              destruct (list_find (alpha_equiv nϕ1) (cs_history state)) eqn:Hfind.
              {
                destruct p as [idx nϕ1'].
                erewrite collapse_aux_case_pattern_in_history in H2;[|apply Hfind].
                erewrite collapse_aux_case_pattern_in_history in H6;[|apply Hfind].
                simpl in H2. simpl in H6.
                rewrite list_find_Some in Hfind.
                destruct Hfind as [Hfind1 [Hfind2 Hfind3]].
                unfold state_alpha_normalized in Han.
                rewrite Forall_forall in Han.
                specialize (Han nϕ1').
                feed specialize Han.
                { 
                  rewrite elem_of_list_lookup.
                  exists idx. apply Hfind1.
                }
                unfold alpha_normalized in Han.
                apply Han.
                { assumption. }
                { assumption. }
                { apply Hae. }
              }
              {
                rewrite list_find_None in Hfind.
                pose proof (IH := IHsz nϕ1 ltac:(lia) state (*Hfind*) Han).
                simpl in IH.
                unfold state_alpha_normalized in IH.
                rewrite Forall_forall in IH.
                eapply IH.
                { apply collapse_arg_in_history. }
                1-3: assumption.
              }
            }
            {
              pose proof (collapse_arg_in_history state nϕ1).
              pose proof (Ha1 := collapse_aux_alpha' state nϕ1).
              pose proof (Ha2 := collapse_aux_alpha' (collapse_aux state nϕ1).1 nϕ2).
              (*pose proof (IH1 := IHsz nϕ1 ltac:(lia) state Han).*)
              (*Print collapse_aux.*)
              destruct (list_find (alpha_equiv nϕ1) (cs_history state)) eqn:Hfind1.
              {
                destruct p as [idx1 nϕ1'].
                erewrite (collapse_aux_case_pattern_in_history state) in H2;[|apply Hfind1].
                simpl in H2.
                erewrite (collapse_aux_case_pattern_in_history state) in H6;[|apply Hfind1].
                simpl in H6.
                erewrite (collapse_aux_case_pattern_in_history state) in Ha1;[|apply Hfind1].
                simpl in Ha1.
                erewrite (collapse_aux_case_pattern_in_history state) in Ha2;[|apply Hfind1].
                simpl in Ha2.

                destruct (list_find (alpha_equiv nϕ2) (cs_history state)) eqn:Hfind2.
                {
                  destruct p as [idx2 nϕ2'].
                  erewrite (collapse_aux_case_pattern_in_history state)in H6;[|apply Hfind2].
                  simpl in H6.
                  erewrite (collapse_aux_case_pattern_in_history state)in Ha2;[|apply Hfind2].
                  simpl in Ha2.

                  rewrite list_find_Some in Hfind1.
                  rewrite list_find_Some in Hfind2.
                  destruct Hfind1 as [Hfind11 [Hfind12 Hfind13]].
                  destruct Hfind2 as [Hfind21 [Hfind22 Hfind23]].
                  destruct (decide (idx1 = idx2)).
                  {
                    subst.
                    rewrite Hfind11 in Hfind21.
                    inversion Hfind21. clear Hfind21. subst.
                    unfold state_alpha_normalized in Han.
                    rewrite Forall_forall in Han.
                    specialize (Han nϕ2').
                    feed specialize Han.
                    {
                      rewrite elem_of_list_lookup.
                      exists idx2. apply Hfind11.
                    }
                    unfold alpha_normalized in Han.
                    apply Han; assumption.
                  }
                  {
                    destruct (decide (idx1 < idx2)) as [Hlt|Hgeq].
                    {
                      specialize (Hfind23 _ _ Hfind11 Hlt).
                      clear IHsz.
                      exfalso.
                      apply Hfind23. clear Hfind23.
                    }
                  }
                }
              }
            }
          }
        }
      }


      move: state.
      induction nϕ; intros state Hnoh Han; simpl;
        unfold lookup_or_leaf,lookup_or_node,lookup_or;
        repeat case_match; subst; simpl;
        try assumption;
        apply Forall_cons;
        (split;[|try assumption]);
        try solve [(intros nϕ1' nϕ2' H1 H2 Hae; inversion H1; inversion H2; subst; clear H1 H2;
          reflexivity)].
      { 
        intros nϕ1' nϕ2' H1 H2 Hae.
        pose proof (IH1 := IHnϕ1 state).
        feed specialize IH1.
        {

        }
        pose proof (IH1 := IHnϕ1 _ Han).
        pose proof (IH2 := IHnϕ2 _ IH1).
        pose proof (Hin1 := collapse_arg_in_history state nϕ1).
        pose proof (Hincl1 := history_collapse_aux_subset state nϕ1).
        remember ((collapse_aux state nϕ1).1) as state'.
        pose proof (Hin2 := collapse_arg_in_history state' nϕ2).
        pose proof (Hincl2 := history_collapse_aux_subset state' nϕ2).
        remember ((collapse_aux state' nϕ2).1) as state''.
        assert (Hin3 : (collapse_aux state nϕ1).2 ∈ (cs_history state'')).
        {
          set_solver.
        }
        unfold state_alpha_normalized in *.
        rewrite Forall_forall in IH2.
        rewrite Forall_forall in IH1.
        pose proof (IH11 := IH1 _ Hin1).
        pose proof (IH21 := IH2 _ Hin2).
        pose proof (IH31 := IH2 _ Hin3).
        unfold alpha_normalized in *.
        clear IHnϕ1 IHnϕ2 Han H IH1 IH2.

        

        inversion H1; inversion H2; subst; clear H1 H2; simpl in *; try reflexivity;
          inversion Hae; clear Hae; subst; simpl in *; auto; f_equal;
          try (match goal with
          | [ H : is_nsubpattern_of_ind ?a ?b |- ?c = ?d] =>
            assert (is_nsubpattern_of_ind c b) by
            ((eapply is_nsubpattern_of_ind_trans;[|apply H];(eauto)))
          end);
          try (match goal with
          | [ H : is_nsubpattern_of_ind ?a ?b |- ?c = ?d] =>
            assert (is_nsubpattern_of_ind d b) by
            ((eapply is_nsubpattern_of_ind_trans;[|apply H];(eauto)))
          end);
          simpl_free; (*
          (idtac + symmetry in IH31);
          (idtac + symmetry in IH21);
          (idtac + symmetry in IH11); *)
          try solve[(apply IH31 + apply IH21 + apply IH11); try assumption;try solve[apply nsub_eq; reflexivity];
          unfold alpha_equiv;
          simpl_free;
          eapply alpha_equiv'_diagonal;
          [idtac|idtac|(apply tEt' + apply uEu')];
          simpl_free; apply reflexivity]
        .
        {

          destruct (decide (alpha_equiv nϕ1 nϕ2)) as [Hae|Hnae].
          {
            subst.
            apply IH11 in Hae.
            { admit. }
            { constructor. apply collapse_ }
          }
          apply IH11; try assumption;try solve[apply nsub_eq; reflexivity].
          constructor.
          {

          }


          (* This does not look promising either. *)
          apply IH11; try assumption;try solve[apply nsub_eq; reflexivity].
          
          (* This does not look promising *)
          (*
          apply IH21; try assumption;try solve[apply nsub_eq; reflexivity].
          eapply is_nsubpattern_of_ind_trans;[eassumption|].
          {
            clear tEt' uEu' t' u' H6 H IH11 IH21 IH31.
          }*)
          Search collapse_aux.
            apply collapse_arg_in_history.
            unfold alpha_equiv;
            simpl_free;
            eapply alpha_equiv'_diagonal;
            [idtac|idtac|eassumption];
            simpl_free; apply reflexivity.
          { simpl_free. apply reflexivity. }
          { simpl_free. apply reflexivity. }
        }
        { apply IH11; try assumption; try solve[apply nsub_eq; reflexivity].
        }
        apply IH11;first[(apply nsub_eq; reflexivity)|assumption].
        { apply nsub_eq; reflexivity. }
        { assumption. }
        Print is_nsubpattern_of_ind.
          match goal with
          | [ H1 : is_nsubpattern_of_ind _ _,
              H2 : is_nsubpattern_of_ind _ _,
              H : (forall _ _ _ _ _, _)
              |- _]
            => let Hnew := fresh "Hnew" in
            pose proof (Hnew := H _ _ H1 H2)
          end.
          pose proof (Hnew' := IH31 _ _ H H6).
          solve_with_alpha; auto with nocore.
        simpl.
      }
      {
        rewrite list_find_None in H.
        rewrite Forall_forall in H.
        rewrite Forall_forall.
        unfold alpha_normalized.
        intros x Hx nϕa nϕb Hnϕa Hnϕb Hae.
        pose proof (IH1 := IHnϕ1 state Han).
        remember (collapse_aux state nϕ1).1 as state'.
        pose proof (IH2 := IHnϕ2 state' IH1).
        remember (collapse_aux state' nϕ2).1 as state''.
        unfold state_alpha_normalized in IH2.
        rewrite Forall_forall in IH2.
        unfold alpha_normalized in IH2.
        naive_solver.
      }
      { 
        intros nϕ1' nϕ2' H1 H2 Hae.
        pose proof (IH1 := IHnϕ1 _ Han).
        pose proof (IH2 := IHnϕ2 _ IH1).
        pose proof (Hin1 := collapse_arg_in_history state nϕ1).
        pose proof (Hincl1 := history_collapse_aux_subset state nϕ1).
        remember ((collapse_aux state nϕ1).1) as state'.
        pose proof (Hin2 := collapse_arg_in_history state' nϕ2).
        pose proof (Hincl2 := history_collapse_aux_subset state' nϕ2).
        remember ((collapse_aux state' nϕ2).1) as state''.
        assert (Hin3 : (collapse_aux state nϕ1).2 ∈ (cs_history state'')).
        {
          set_solver.
        }
        unfold state_alpha_normalized in *.
        rewrite Forall_forall in IH2.
        rewrite Forall_forall in IH1.
        pose proof (IH11 := IH1 _ Hin1).
        pose proof (IH21 := IH2 _ Hin2).
        pose proof (IH31 := IH2 _ Hin3).
        unfold alpha_normalized in *.
        clear IHnϕ1 IHnϕ2 Han H IH1 IH2.
        inversion H1; inversion H2; subst; clear H1 H2; simpl in *; try reflexivity;
          solve_with_alpha.
      }
      {
        rewrite list_find_None in H.
        rewrite Forall_forall in H.
        rewrite Forall_forall.
        unfold alpha_normalized.
        intros x Hx nϕa nϕb Hnϕa Hnϕb Hae.
        pose proof (IH1 := IHnϕ1 state Han).
        remember (collapse_aux state nϕ1).1 as state'.
        pose proof (IH2 := IHnϕ2 state' IH1).
        remember (collapse_aux state' nϕ2).1 as state''.
        unfold state_alpha_normalized in IH2.
        rewrite Forall_forall in IH2.
        unfold alpha_normalized in IH2.
        naive_solver.
      }
      { 
        intros nϕ1' nϕ2' H1 H2 Hae.
        pose proof (IH := IHnϕ _ Han).
        pose proof (Hin1 := collapse_arg_in_history state nϕ).
        pose proof (Hincl1 := history_collapse_aux_subset state nϕ).
        remember ((collapse_aux state nϕ).1) as state'.
        assert (Hin3 : (collapse_aux state nϕ).2 ∈ (cs_history state')).
        {
          set_solver.
        }
        unfold state_alpha_normalized in *.
        rewrite Forall_forall in IH.
        pose proof (IH' := IH _ Hin1).
        unfold alpha_normalized in *.
        inversion H1; inversion H2; subst; clear H1 H2; simpl in *; try reflexivity;
          solve_with_alpha.
      }
      {
        rewrite list_find_None in H.
        rewrite Forall_forall in H.
        rewrite Forall_forall.
        unfold alpha_normalized.
        intros x' Hx' nϕa nϕb Hnϕa Hnϕb Hae.
        pose proof (IH1 := IHnϕ state Han).
        remember (collapse_aux state nϕ).1 as state'.
        unfold state_alpha_normalized in IH1.
        rewrite Forall_forall in IH1.
        unfold alpha_normalized in IH1.
        naive_solver.
      }
      { 
        intros nϕ1' nϕ2' H1 H2 Hae.
        pose proof (IH := IHnϕ _ Han).
        pose proof (Hin1 := collapse_arg_in_history state nϕ).
        pose proof (Hincl1 := history_collapse_aux_subset state nϕ).
        remember ((collapse_aux state nϕ).1) as state'.
        assert (Hin3 : (collapse_aux state nϕ).2 ∈ (cs_history state')).
        {
          set_solver.
        }
        unfold state_alpha_normalized in *.
        rewrite Forall_forall in IH.
        pose proof (IH' := IH _ Hin1).
        unfold alpha_normalized in *.
        inversion H1; inversion H2; subst; clear H1 H2; simpl in *; try reflexivity;
          solve_with_alpha.
      }
      {
        rewrite list_find_None in H.
        rewrite Forall_forall in H.
        rewrite Forall_forall.
        unfold alpha_normalized.
        intros x' Hx' nϕa nϕb Hnϕa Hnϕb Hae.
        pose proof (IH1 := IHnϕ state Han).
        remember (collapse_aux state nϕ).1 as state'.
        unfold state_alpha_normalized in IH1.
        rewrite Forall_forall in IH1.
        unfold alpha_normalized in IH1.
        naive_solver.
      }
      Unshelve.
    Qed.

    Lemma collapse_aux_preserves_aeihae {Σ : Signature} (state : CollapseState) :
      history_subpattern_closed state ->
      alpha_equiv_in_history_are_equal state ->
      forall nϕ,
        alpha_equiv_in_history_are_equal (collapse_aux state nϕ).1
    .
    Proof.
      intros Hhist H nϕ.
      move: state Hhist H.
      induction nϕ; intros state Hhist H; simpl in *;
        try solve [apply lookup_or_leaf_preserves_aeihae; assumption].
      {

        unfold lookup_or_node,lookup_or. simpl.
        destruct (list_find (alpha_equiv (npatt_app nϕ1 nϕ2)) (cs_history state)) eqn:Heq.
        {
          destruct p as [? nϕ'].
          rewrite list_find_Some in Heq.
          destruct Heq as [H1 [H2 H3]].
          simpl.
          exact H.
        }
        {
          rewrite list_find_None in Heq.
          simpl.
          unfold alpha_equiv_in_history_are_equal. simpl.
          intros phi1 phi2 Hphi1 Hphi2 Halpha.
          rewrite elem_of_cons in Hphi1.
          rewrite elem_of_cons in Hphi2.
          destruct Hphi1 as [Hphi1|Hphi1], Hphi2 as [Hphi2|Hphi2]; subst.
          { reflexivity. }
          {
            pose proof (Hevars := alpha_equiv_impl_same_evars _ _ Halpha).
            pose proof (Hsvars := alpha_equiv_impl_same_svars _ _ Halpha).
            inversion Halpha. subst. simpl in *. clear Halpha.
            remember ((collapse_aux state nϕ1).1) as state'.
            remember ((collapse_aux state nϕ1).2) as nϕ1'.
            remember ((collapse_aux state' nϕ2).1) as state''.
            remember ((collapse_aux state' nϕ2).2) as nϕ2'.

            rewrite -Hevars in tEt'.
            rewrite -Hsvars in tEt'.
            rewrite -Hevars in uEu'.
            rewrite -Hsvars in uEu'.
            rewrite 2!union_idemp_L in tEt'.
            rewrite 2!union_idemp_L in uEu'.

            pose proof (IH1 := IHnϕ1 state Hhist H).
            pose proof (Hhist' := collapse_preserves_sc state nϕ1 Hhist).
            pose proof (IH2 := IHnϕ2 (collapse_aux state nϕ1).1 Hhist' IH1).
            pose proof (Hhist'' := collapse_preserves_sc (collapse_aux state nϕ1).1 nϕ2 Hhist').
            
            unfold alpha_equiv_in_history_are_equal in *.
            assert (Hfe1 : named_free_evars nϕ1' = named_free_evars nϕ1).
            {
              apply alpha_equiv_impl_same_evars.
              subst. apply collapse_aux_alpha'.
            }
            assert (Hfs1 : named_free_svars nϕ1' = named_free_svars nϕ1).
            {
              apply alpha_equiv_impl_same_svars.
              subst. apply collapse_aux_alpha'.
            }
            assert (Hfe2 : named_free_evars nϕ2' = named_free_evars nϕ2).
            {
              apply alpha_equiv_impl_same_evars.
              subst. apply collapse_aux_alpha'.
            }
            assert (Hfs2 : named_free_svars nϕ2' = named_free_svars nϕ2).
            {
              apply alpha_equiv_impl_same_svars.
              subst. apply collapse_aux_alpha'.
            }
            rewrite Hfe1 Hfe2 in tEt'.
            rewrite Hfs1 Hfs2 in uEu'.

            rewrite Heqstate'' in Hphi2.
            pose proof (Hphi2' := in_history_invert _ _ _ Hphi2).
            feed specialize Hphi2'.
            {
              intros p Hp Hcontra.
              rewrite Forall_forall in Heq.
              subst.
              eapply Heq.
              2: constructor.
              2,3: simpl.
              2: {
                constructor.
                { simpl.
                }
              }
              inversion Hp; subst; clear Hp.
              eapply Heq.
            }
            Check in_history_invert.
            
            assert (nϕ1' = t').
            {
              subst.
              eapply IHnϕ1.
              apply IH1.
              { subst; apply collapse_arg_in_history. }
              { Search t'.   }
            }
            Search alpha_equiv'.
            
            
            simpl in Hevars,Hsvars.
            epose proof (Hsame1 := IH1 _ _ _ _ tEt').
            f_equal.
            
            
            apply IH2; try assumption.
            eapply Hhist'';[|apply Hphi2].
          }
           
        }
      }
    Qed.
    
    Print collapse_aux.

  (*
  (* TESTS *)
From MatchingLogic Require Import StringSignature.

Definition Σ : Signature :=
  {|
   |}
#[local]
Example ex_rename {Σ : Signature} :
  rename  = patt_bott.
*)