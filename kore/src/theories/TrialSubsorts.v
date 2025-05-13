From MatchingLogic Require Export stdpp_ext.
From Kore Require Export Semantics.
Import Signature.StringVariables.
Import Kore.Syntax.Notations.

From Coq Require Import ZArith.

Open Scope kore_scope.
Open Scope hlist_scope.
Open Scope string_scope.

Ltac autorewrite_set :=
  repeat (
    rewrite intersection_top_l_L +
    rewrite intersection_top_r_L +
    rewrite union_empty_l_L +
    rewrite union_empty_r_L +
    rewrite propset_difference_neg +
    rewrite propset_union_simpl +
    rewrite propset_intersection_simpl +
    rewrite singleton_subseteq_l
  ).

Ltac basic_simplify_krule :=
  simpl;
  eval_helper;
  repeat rewrite_app_ext;
  autorewrite_set.
Ltac simplify_krule :=
  basic_simplify_krule;
  apply propset_top_elem_of_2;
  intro;
  apply elem_of_PropSet;
  repeat rewrite elem_of_PropSet;
  repeat rewrite singleton_subseteq;
  repeat rewrite singleton_eq.


Ltac abstract_var := 
  match goal with
    | [|- context [evar_valuation ?σ ?s]] =>
      let x := fresh "var" in
      let Hx := fresh "Hvar" in
        remember (evar_valuation σ s) as x eqn:Hx (*;
        clear Hx;
        revert x *)
    end.

Module T.

  (* We have two sorts: natural numbers and bools *)
  Inductive DemoSorts :=
  | SortNat
  | SortBool
  | SortK
  | SortKItem
  | SortList.

  (* We prove decidable equality and finiteness of the type above. *)
  Instance DemoSorts_eq_dec : EqDecision DemoSorts.
  Proof. solve_decision. Defined.
  Program Instance DemoSorts_finite : finite.Finite DemoSorts := {
    enum := [SortNat; SortBool; SortK; SortKItem; SortList];
  }.
  Next Obligation. compute_done. Defined.
  Final Obligation. destruct x; set_solver. Defined.


  Inductive DemoSyms :=
  | SymZero
  | SymSucc
  | SymAdd
  | SymTrue
  | SymFalse
  | SymIsList
  | SymNil
  | SymCons
  | SymInList
  | SymAppend.

  (* We prove decidable equality and finiteness of the type above. *)
  Instance DemoSyms_eq_dec : EqDecision DemoSyms.
  Proof. solve_decision. Defined.
  Program Instance DemoSyms_finite : finite.Finite DemoSyms := {
    enum := [SymZero;SymSucc;SymAdd;SymTrue;
    SymFalse;SymIsList;SymNil;SymCons;SymInList;SymAppend];
  }.
  Next Obligation. compute_done. Defined.
  Final Obligation. destruct x; set_solver. Defined.

  Inductive Demo_subsort : CRelationClasses.crelation DemoSorts :=
  | subsorts_refl s : Demo_subsort s s
  | kitem_is_top s : s ≠ SortK -> Demo_subsort s SortKItem.

  Instance Demo_subsort_PreOrder : CRelationClasses.PreOrder Demo_subsort.
  Proof.
    split.
    cbv. intro. left.
    cbv. intros. inversion H; subst. assumption.
    inversion H0; subst. assumption. assumption.
  Defined.

  Instance Demo_subsort_PartialOrder : CRelationClasses.PartialOrder eq Demo_subsort.
  Proof.
    cbv. intros. split; intros. rewrite H. repeat constructor.
    destruct H. inversion d; subst. reflexivity.
    inversion d0; subst; reflexivity.
  Defined.

  (* In the signature, we need to define the sorts, the variable types,
     and the typing/sorting rules for symbols: *)
  Program Instance DemoSignature : Signature := {|
    sorts := {|
      sort := DemoSorts;
      subsort := Demo_subsort
    |};
    variables := StringVariables;
    symbols := {|
      symbol := DemoSyms;
      arg_sorts :=
        fun σ => match σ with
                 | SymZero => []
                 | SymSucc => [SortNat]
                 | SymAdd => [SortNat; SortNat]
                 | SymTrue => []
                 | SymFalse => []
                 | SymIsList => [SortK]
                 | SymNil => []
                 | SymCons => [SortKItem; SortList]
                 | SymInList => [SortKItem; SortList]
                 | SymAppend => [SortList; SortList]
                 end;
      ret_sort := fun σ => match σ with
                           | SymZero | SymSucc | SymAdd => SortNat
                           | SymTrue | SymFalse => SortBool
                           | SymNil | SymCons | SymAppend => SortList
                           | SymInList | SymIsList => SortBool
                           end;
    |};
  |}.

  Inductive carrier : DemoSorts -> Set :=
  | c_nat (n : nat) : carrier SortNat
  | c_bool (b : bool) : carrier SortBool
  | c_nil : carrier SortList
  | c_cons : carrier SortKItem -> carrier SortList -> carrier SortList
  | c_subsort (s1 s2 : DemoSorts) (P : subsort s1 s2) (x : carrier s1) : carrier s2
  (* This should match the subsort relation *)
  (* | c_kitem {A} : A ≠ SortK -> carrier A -> carrier SortKItem *)
  | c_dotk : carrier SortK.

  (* Check c_nat 1. *)
  (* Check c_nil. *)
  (* Check c_cons (c_kitem (eq_ind SortNat (λ x, if x is SortNat then True else False) I _) (c_nat 1)) c_nil. *)
  (* Check c_cons (c_nat 1) (c_cons (c_bool false) c_nil). *)
  (* Check c_cons (c_nat 1) (c_cons (c_bool false) (c_cons (c_cons (c_nat 1) c_nil) c_nil)). *)

  Lemma neqs_eq {A} {a b : A} (p q : a ≠ b) : p = q.
  Proof.
    apply functional_extensionality. intros. destruct (p x).
  Defined.

  Instance carrier_eqdec A : EqDecision (carrier A).
  Proof.
    (* unfold EqDecision, Decision. *)
    (* intros. *)
    (* dependent induction x; dependent destruction y; auto. *)
    (* destruct (decide (n = n0)) as [-> | ?]; [left; reflexivity | right; congruence]. *)
    (* destruct (decide (b = b0)) as [-> | ?]; [left; reflexivity | right; congruence]. *)
    (* destruct (IHx1 y1) as [-> | ?]; [| right; congruence]. *)
    (* destruct (IHx2 y2) as [-> | ?]; [left; reflexivity | right; congruence]. *)
    (* destruct (decide (A = A0)); [| right; congruence]. *)
    (* destruct (IHx (eq_rect_r carrier y e)). *)
    (* 2: { right. intro. inversion H. inversion_sigma. *)
    (*   apply rew_swap in H2_0. rewrite (Eqdep.EqdepTheory.UIP _ _ _ H2_ e) in H2_0. *)
    (*   apply n1. assumption. *)
    (* } *)
    (* pose proof (neqs_eq n (eq_rect_r (.≠ SortK) n0 e)). *)
    (* left. Search eq_rect. *)
  Admitted.

  Definition DemoModel : @Model DemoSignature.
  Proof.
    unshelve eapply mkModel_singleton.
    - exact carrier.
    - destruct_with_eqn σ; simpl; intros.
      * exact (c_nat 0).
      * dependent induction H. exact (c_nat (S n)).
        inversion P; subst. now apply IHcarrier.
      * dependent induction H. dependent induction H0.
        exact (c_nat (n + n0)).
        inversion P; subst. now apply IHcarrier.
        inversion P; subst. apply IHcarrier. reflexivity. exact H0. (* ? *)
      * exact (c_bool true).
      * exact (c_bool false).
      * exact (c_bool false). (*TODO: I don't understand this still*)
      * exact (c_nil).
      * exact (c_cons H H0).
      * dependent induction H0. exact (c_bool false).
        dependent destruction H.
        dependent destruction H0_.
        destruct (decide (s0 = s1)). 2: exact (IHcarrier2 erefl).
        destruct (decide (eq_rect_r carrier H e = H0_)).
        exact (c_bool true). exact (IHcarrier2 erefl).
        inversion P; subst. now apply IHcarrier.
      * dependent induction H. exact H0. exact (IHcarrier2 erefl H0). (* ? *)
        inversion P; subst. apply IHcarrier. reflexivity. exact H0. (* ? *)
    - destruct s. 1-3,5: repeat constructor. do 2 econstructor; first last; repeat constructor. discriminate.
    - intros. inversion H; subst. assumption. econstructor; eassumption.
  Defined.

  Definition test : @Theory DemoSignature.
  Proof.
    split. intros pat.
    apply Logic.or.
    refine (exists R, pat = existT R _).
    eapply kore_equals. epose (kore_app SymTrue hnil). simpl in p. exact p.
    epose (kore_app SymZero hnil). simpl in p.
    epose (kore_inj _ _ p).
    epose (kore_app SymSucc ⟨ p ⟩). simpl in p1. eapply kore_inj in p1.
    epose (kore_app SymNil hnil). simpl in p2.
    epose (kore_app SymCons ⟨ p0 ; p2 ⟩). simpl in p3.
    epose (kore_app SymCons ⟨ p1 ; p3 ⟩). simpl in p4.
    epose (kore_app SymInList ⟨ p0 ; p4 ⟩). simpl in p5.
    exact p5. Unshelve. 1,3: right; discriminate.
    apply Logic.or.
    refine (exists R, pat = existT R _).
    eapply kore_equals.
    unshelve apply kore_app. exact SymAppend. simpl.
    right. epose (kore_app SymNil hnil). simpl in p. exact p.
    right. apply kore_fevar. exact "x".
    left. simpl. apply kore_fevar. exact "x".
    refine (exists R, pat = existT R _).
    eapply kore_equals.
    unshelve apply kore_app. exact SymAppend. simpl.
    right. apply kore_fevar. exact "x".
    right. epose (kore_app SymNil hnil). simpl in p. exact p.
    left. simpl. apply kore_fevar. exact "x".
  Defined.

  Goal satT test DemoModel.
  Proof.
    unfold satT, satM, test. intros.
    inversion H; destruct H0; subst; simpl.
    simplify_krule. give_up.
    destruct H0; subst; simpl.
    simplify_krule. reflexivity.
    destruct H0; subst; simpl.
    simplify_krule. unfold block, solution_left, eq_rec_r, eq_rect_r, carrier_rec. simpl. give_up.
  Abort.

  (* Program Definition DemoModel : @Model DemoSignature := *)
  (*   mkModel_singleton *)
  (*     carrier *)
  (*     (DemoSyms_rect _ *)
  (*       (c_nat 0) *)
  (*       _ *)
  (*       _ *)
  (*       _ *)
  (*       _ *)
  (*       _ *)
  (*       _ *)
  (*       _ *)
  (*       _ *)
  (*     ) *)
  (*     _ *)
  (*     _. *)
  (* Next Obligation. *)
  (*   simpl. *)
  (*   intro. inversion H. *)
  (*   exact (c_nat (S n)). *)
  (*   inversion P. *)
  (* Defined. *)
  (* Next Obligation. *)
  (*   simpl. *)
  (*   intros. inversion H. inversion H0. *)
  (*   exact (c_nat (n + n0)). *)
  (* Defined. *)
  (* Next Obligation. *)
  (*   simpl. *)
  (*   exact (c_bool true). *)
  (* Defined. *)
  (* Next Obligation. *)
  (*   simpl. *)
  (*   exact (c_bool false). *)
  (* Defined. *)
  (* Next Obligation. *)
  (*   simpl. *)
  (*   Print DemoSyms. *)
  (*   intros. *)
  (*   inversion H. (1* TODO *1) *)
  (* Defined. *)
  (* Next Obligation. *)
  (*   simpl. *)
  (*   exact (c_nil). *)
  (* Defined. *)
  (* Next Obligation. *)
  (*   simpl. *)
  (*   intros. *)
  (*   exact (c_cons H H0). *)
  (* Defined. *)
  (* Next Obligation. *)

