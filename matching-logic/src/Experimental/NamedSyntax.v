From Coq Require Import ssreflect ssrfun ssrbool.

From Coq.Vectors Require Import Vector.

From Equations Require Import Equations.

Require Import String.
From stdpp Require Import
    base
    gmap
    infinite
    natmap
    option
    strings
    stringmap
    sets
    vector
    list
.
From MatchingLogic Require Import
    Signature
    Syntax
    StringSignature
    MLPM
    FreshnessManager
    Utils.stdpp_ext
.
Import MatchingLogic.Syntax.Notations.


(* Fixpoint count_ebinders {Σ : Signature} (ϕ : Pattern) : nat :=
  match ϕ with
  | patt_exists ϕ => S (count_ebinders ϕ)
  | patt_mu ϕ => count_ebinders ϕ
  | patt_imp ϕ1 ϕ2 | patt_app ϕ1 ϕ2 => count_ebinders ϕ1 + count_ebinders ϕ2
  | _ => 0
  end. *)

Fixpoint greatest_dangling_index_helper {Σ : Signature} (ϕ : Pattern) (n : nat) : nat :=
  match ϕ with
  | patt_bound_evar m => max n (S m)
  | patt_imp p1 p2 | patt_app p1 p2 => max (greatest_dangling_index_helper p1 n) (greatest_dangling_index_helper p2 n)
  | patt_exists p => greatest_dangling_index_helper p n - 1
  | patt_mu p => greatest_dangling_index_helper p n
  | _ => 0
  end.

Definition greatest_dangling_index {Σ : Signature} (ϕ : Pattern) : nat :=
  greatest_dangling_index_helper ϕ 0.

Section test.
  Context {Σ : Signature}.
  Compute greatest_dangling_index (ex, b0 $ ex, b1).

  Theorem well_formed_dangling :
    forall ϕ n, well_formed_closed_ex_aux ϕ (greatest_dangling_index_helper ϕ n).
  Proof.
    induction ϕ; intros level; simpl; auto.
    * case_match; auto. lia.
    * apply andb_true_iff; split.
      - eapply well_formed_closed_ex_aux_ind. 2: apply (IHϕ1 level). lia.
      - eapply well_formed_closed_ex_aux_ind. 2: apply (IHϕ2 level). lia.
    * apply andb_true_iff; split.
      - eapply well_formed_closed_ex_aux_ind. 2: apply (IHϕ1 level). lia.
      - eapply well_formed_closed_ex_aux_ind. 2: apply (IHϕ2 level). lia.
    * specialize (IHϕ level). destruct greatest_dangling_index_helper.
      - simpl. wf_auto2.
      - now replace (S (S n - 1)) with (S n) by lia.
  Qed.
End test.

Module test1.
Section NamedPattern.
  (* Context {Symb : MLSymbols}
          {syms : symbols}. *)
  Context {symbs : Set}
          {symbs_eqdec : EqDecision symbs}
          {symbs_countable : Countable symbs}.
  Instance Σ : Signature :=
  {| variables := StringMLVariables ;
    ml_symbols := {|
        symbols := symbs ;
      |}
  |}.
(*
  

*)

  (* Record NamedPattern := {
    enames : list evar;
    snames : list svar;
    pattern : Pattern;
  }. *)

  (* Record NamedPattern2 (edepth : nat) : Set := {
    enames : vec string edepth;
    pattern : Pattern;
    enough_enames :
      edepth >= count_ebinders pattern;
  }. *)


  (* Inductive vector : nat -> Set :=
    | nil : vector 0.

  Notation "'[]' : n 'vektor'" := (nil : vector n).
  Check [] : 0 vektor. *)
(* Print NamedPattern2. *)
  (* 
    Index the type with the variable names:

    type NamedPattern : list evar -> Set :=
      | build_pat (p : Pattern)

    def namedImp (p1 : NamedPattern l1) (p2 : NamedPattern l2) : NamedPattern (l1 ++ l2) :=
      build_pat (patt_imp (proj p1) (proj p2)).
      
  *)

  Record NamedPattern (l : list evar) : Set := to_named {
    pat :> Pattern;
  }.

  Check to_named nil patt_bott.

  (* Primitives *)
  Definition named_var {l : list evar} (x : evar) : NamedPattern l :=
    match index_of x l with  
    | None => to_named l (patt_free_evar x) 
    | Some n => to_named l (patt_bound_evar n)
    end. 
  Definition named_imp {l} (p1 : NamedPattern l) (p2 : NamedPattern l) : NamedPattern l :=
    to_named l (patt_imp p1 p2).
  Definition named_app {l} (p1 : NamedPattern l) (p2 : NamedPattern l) : NamedPattern l :=
    to_named l (patt_app p1 p2).
  Definition named_exists {l} (x : evar) (p : NamedPattern (x::l)) : NamedPattern l :=
    to_named l (patt_exists p).
  Definition named_bot {l} : NamedPattern l := to_named l patt_bott.

  (* notations *)
  (* Opaque pat. (* simplification collapses the named representation! *) *)
  Arguments pat : simpl never. (* <- This is the key *)

  Definition named_not {l} (p : NamedPattern l) : NamedPattern l :=
    named_imp p named_bot.
  Definition named_forall {l} (x : evar) (p : NamedPattern (x::l)) : NamedPattern l :=
    named_not (named_exists x (named_not p)).


  (* Tests: *)
  Definition X := "X"%string.
  Definition Y := "Y"%string.
  Definition Z := "Z"%string.

  Definition mybvar1 := named_var X : NamedPattern [X].
  Definition myfvar1 := named_var X : NamedPattern [].
  Compute mybvar1.


  Definition myexs := named_exists X (named_var X) : NamedPattern [].
  Compute myexs.

  Definition mypat1 := named_imp (named_forall X (named_var X)) (named_exists Y (named_var Y)) : NamedPattern [].
  Compute mypat1. (* Computation obviously unfolds notations. However, it is still a question
                     whether we can map named notations to nameless notations *)

  (* Disadvantage: without the type annotation, Coq will not be able to infer the list of evars *)

  Notation "a $ₙ b" := (named_app a b) (at level 65, right associativity) : ml_scope.
  Notation "'Botₙ'" := named_bot : ml_scope.
  Notation "⊥" := named_bot : ml_scope.
  Notation "a --->ₙ b"  := (named_imp a b) (at level 75, right associativity) : ml_scope.
  Notation "'ex' x , phi" := (named_exists x phi) (at level 80) : ml_scope.
  Notation "x 'ₑᵥ'" := (named_var x) (at level 1, format "x ₑᵥ") : ml_scope.

  Notation "!ₙ p" := (named_not p) (at level 71, right associativity) : ml_scope.
  Notation "'all' x , phi" := (named_forall x phi) (at level 80) : ml_scope.
  (* Definition namedProvable {l} Γ (p : NamedPattern l) i := Γ ⊢i p using i. *)

  (* No additional definition is needed to express named provability: *)
  Goal ∅ ⊢i mypat1 using AnyReasoning.
  Proof.
    intros. unfold mypat1.
    toMLGoal. wf_auto2.
    mlIntro "H". (* <- mlIntro, on the other hand does not! *)
    repeat (unfold pat; simpl). (* explicit unfolding needed to get the LN pattern *)
  Abort.

  Goal ∅ ⊢i mypat1 using AnyReasoning.
  Proof.
    intros. unfold mypat1.
    toMLGoal. wf_auto2.
    mlIntro "H". (* <- mlIntro, on the other hand does not! *)
    assert (x : evar) by exact X.
    mlSpecialize "H" with x. (* <- simplifying this substitution is tricky! Displaying it is also not trivial! *)
    (* unfold pat at 1; cbn. *)
    mlExists x. mlAssumption.
  Qed.

  (* more notations: *)
  Definition named_or {l} (p1 : NamedPattern l) (p2 : NamedPattern l) : NamedPattern l :=
    named_imp (named_not p1) p2.
  Definition named_and {l} (p1 : NamedPattern l) (p2 : NamedPattern l) : NamedPattern l :=
    named_not (named_or (named_not p1) (named_not p2)).

  Notation "p1 'orₙ' p2" := (named_or p1 p2) (at level 73, left associativity) : ml_scope.
  Notation "p1 'andₙ' p2" := (named_and p1 p2) (at level 72, left associativity) : ml_scope.

  Definition named_and_test : NamedPattern [] :=
    X ₑᵥ andₙ Y ₑᵥ --->ₙ Y ₑᵥ andₙ X ₑᵥ.

  Goal ∅ ⊢i named_and_test using AnyReasoning.
  Proof.
    unfold named_and_test. mlIntro "H".
    mlDestructAnd "H" as "H1" "H2".
    mlSplitAnd.
    mlExact "H2".
    mlExact "H1".
  Qed.


  Definition LN_to_N l (p : Pattern) : NamedPattern l :=
    to_named l p.
  Definition default_N p := LN_to_N (evar_fresh_seq (free_evars p) (greatest_dangling_index p)) p.
  (* However, these functions do not give names to the binders *)

  (* Finally, a few examples for metavariables: *)
  Fail Goal forall p1 p2 : Pattern, well_formed p1 -> well_formed p2 ->
    ∅ ⊢i p1 andₙ p2 --->ₙ p2 andₙ p1 using AnyReasoning. (* <- Coq cannot guess the names! *)

  Fail Goal forall p1 p2 : Pattern, well_formed p1 -> well_formed p2 ->
    ∅ ⊢i default_N p1 andₙ default_N p2 --->ₙ default_N p2 andₙ default_N p1 using AnyReasoning. (* The maximum is needed! *)
  
  Goal forall p1 p2 : Pattern, well_formed p1 -> well_formed p2 ->
    ∅ ⊢i LN_to_N [] p1 andₙ LN_to_N [] p2 --->ₙ LN_to_N [] p2 andₙ LN_to_N [] p1 using AnyReasoning. (* Suppose that there are no binders *)
  Proof.
    intros.
    mlIntro "H". simpl.
    mlDestructAnd "H" as "H1" "H2".
    mlSplitAnd.
    mlExact "H2".
    mlExact "H1".
  Qed.

  Lemma test : forall p1 p2 : NamedPattern [], well_formed p1 -> well_formed p2 -> (* well_formednes works due to coercions *)
    ∅ ⊢i p1 andₙ p2 --->ₙ p2 andₙ p1 using AnyReasoning.
  Proof.
    intros.
    mlIntro "H".
    mlDestructAnd "H" as "H1" "H2".
    mlSplitAnd.
    mlExact "H2".
    mlExact "H1".
  Qed.


  Lemma test' : forall p1 p2 p3 : NamedPattern [], 
    well_formed p3 -> well_formed p1 -> well_formed p2 -> (* well_formednes works due to coercions *)
    ∅ ⊢i p1 andₙ p2 andₙ p3 --->ₙ p2 andₙ p1 using AnyReasoning.
  Proof.
    intros.
    mlIntro "H".
    mlDestructAnd "H" as "H1" "H2".
    mlDestructAnd "H1" as "H" "H3".
    mlSplitAnd.
    mlExact "H3".
    mlExact "H".
  Qed.

  Lemma test2 : forall p1 p2 : Pattern, well_formed p1 -> well_formed p2 ->
    ∅ ⊢i p1 and p2 ---> p2 and p1 using AnyReasoning.
  Proof.
    intros.
    pose proof (test (LN_to_N [] p1) (LN_to_N [] p2)). (* This system is backward-compatible, i.e., named
                                                          proofs can be used (with some tricks) as 
                                                          nameless proofs *)
    apply H1.
    1-2: wf_auto2.
  Qed.


  Goal forall p1 p2 : NamedPattern [], well_formed p1 -> well_formed p2 -> (* well_formednes works due to coercions *)
    ∅ ⊢i p1 andₙ p2 --->ₙ p2 andₙ p1 using AnyReasoning.
  Proof.
    intros. now apply test2. (* Nameless proofs are automatically lifted to named proofs *) 
  Qed.

  (* Conclusion:
     - This approach is very similar to Pattern_in_context, but the type describes how the names are used
     - The primitives are constructed by the `to_named` record constructor, but everything else can be derived
     - Having `simpl never` blocks Coq's simplification mechanism to unfold the named patterns to nameless ones
     - With this approach, we can solve all of our problems, moreover it is really simple
       - Current proof mode tactics even preserve the named structure (they do not automatically unfold anything)!
     - Additional advantage: named proofs can also automatically converted to nameless proofs and vica versa
     But:
     - Printing and simplification of substitutions is not solved yet
     - Scope (list of variables) cannot be infered automatically
     - Theorems stated for patterns need some conversion, however, they can be stated as
       named, because named patterns are automatically converted to nameless ones
  *)

End NamedPattern.
End test1.






(***************************************************)
(***************************************************)
(***************************************************)
(***************************************************)



(* I also experiment with built-in well-formedness *)
Module test2.
Section NamedPattern.
  Import List.
  Open Scope list_scope.

  Context {symbs : Set}
          {symbs_eqdec : EqDecision symbs}
          {symbs_countable : Countable symbs}.
  Instance Σ : Signature :=
  {| variables := StringMLVariables ;
    ml_symbols := {|
        symbols := symbs ;
      |}
  |}.

  Record NamedPattern (l : list string) : Set := to_named {
    pat :> Pattern;
    names_enough : length l >= greatest_dangling_index pat
  }.

  (* Primitives *)
  Program Definition named_var {l : list evar} (x : evar) : NamedPattern l :=
    match index_of x l with  
    | None => to_named l (patt_free_evar x) _
    | Some n => to_named l (patt_bound_evar n) _
    end.
  Next Obligation.
  Admitted.
  Next Obligation.
  Admitted.
 
  Program Definition named_imp {l} (p1 : NamedPattern l) (p2 : NamedPattern l) : NamedPattern l :=
    to_named l (patt_imp p1 p2) _.
  Next Obligation.
    intros. cbn. pose proof (names_enough _ p1). pose proof (names_enough _ p2).
    unfold greatest_dangling_index in *. lia.
  Defined.

  Program Definition named_app {l} (p1 : NamedPattern l) (p2 : NamedPattern l) : NamedPattern l :=
    to_named l (patt_app p1 p2) _.
  Next Obligation.
    intros. cbn. pose proof (names_enough _ p1). pose proof (names_enough _ p2).
    unfold greatest_dangling_index in *. lia.
  Defined.

  Program Definition named_exists {l} (x : evar) (p : NamedPattern (x::l)) : NamedPattern l :=
    to_named l (patt_exists p) _.
  Next Obligation.
    intros. cbn.
    pose proof (names_enough _ p). unfold greatest_dangling_index in H. simpl in H. lia.
  Defined.
  
  Program Definition named_bot {l} : NamedPattern l := to_named l patt_bott _.
  Next Obligation.
    intros. cbn. lia.
  Defined.

  (* notations *)
  (* Opaque pat. (* simplification collapses the named representation! *) *)
  Arguments pat : simpl never. (* <- This is the key *)

  Definition named_not {l} (p : NamedPattern l) : NamedPattern l :=
    named_imp p named_bot.
  Definition named_forall {l} (x : evar) (p : NamedPattern (x::l)) : NamedPattern l :=
    named_not (named_exists x (named_not p)).


  (* Tests: *)
  Definition X := "X"%string.
  Definition Y := "Y"%string.
  Definition Z := "Z"%string.

  Definition mybvar1 := named_var X : NamedPattern [X].
  Definition myfvar1 := named_var X : NamedPattern [].
  Compute mybvar1.


  Definition myexs := named_exists X (named_var X) : NamedPattern [].
  Compute myexs.

  Definition mypat1 := named_imp (named_forall X (named_var X)) (named_exists Y (named_var Y)) : NamedPattern [].
  Compute mypat1. (* In this case, we also get a proof of well-formedness *)

  Notation "a $ₙ b" := (named_app a b) (at level 65, right associativity) : ml_scope.
  Notation "'Botₙ'" := named_bot : ml_scope.
  Notation "⊥" := named_bot : ml_scope.
  Notation "a --->ₙ b"  := (named_imp a b) (at level 75, right associativity) : ml_scope.
  Notation "'ex' x , phi" := (named_exists x phi) (at level 80) : ml_scope.
  Notation "x 'ₑᵥ'" := (named_var x) (at level 1, format "x ₑᵥ") : ml_scope.

  Notation "!ₙ p" := (named_not p) (at level 71, right associativity) : ml_scope.
  Notation "'all' x , phi" := (named_forall x phi) (at level 80) : ml_scope.

  (* everything works for this approach too: *)
  Goal ∅ ⊢i mypat1 using AnyReasoning.
  Proof.
    intros. unfold mypat1.
    toMLGoal. wf_auto2.
    mlIntro "H".
    unfold pat. simpl.
  Abort.

  Goal ∅ ⊢i mypat1 using AnyReasoning.
  Proof.
    intros. unfold mypat1.
    toMLGoal. wf_auto2.
    mlIntro "H". (* <- mlIntro, on the other hand does not! *)
    assert (x : evar) by admit.
    mlSpecialize "H" with x. (* <- simplifying this substitution is tricky! Displaying it is also not trivial! *)
    mlExists x. mlAssumption.
  Abort.

  (* more notations: *)
  Definition named_or {l} (p1 : NamedPattern l) (p2 : NamedPattern l) : NamedPattern l :=
    named_imp (named_not p1) p2.
  Definition named_and {l} (p1 : NamedPattern l) (p2 : NamedPattern l) : NamedPattern l :=
    named_not (named_or (named_not p1) (named_not p2)).

  Notation "p1 'orₙ' p2" := (named_or p1 p2) (at level 73, left associativity) : ml_scope.
  Notation "p1 'andₙ' p2" := (named_and p1 p2) (at level 72, left associativity) : ml_scope.

  Definition named_and_test : NamedPattern [] :=
    X ₑᵥ andₙ Y ₑᵥ --->ₙ Y ₑᵥ andₙ X ₑᵥ.

  Goal ∅ ⊢i named_and_test using AnyReasoning.
  Proof.
    unfold named_and_test. mlIntro "H".
    mlDestructAnd "H" as "H1" "H2".
    mlSplitAnd.
    mlExact "H2".
    mlExact "H1".
  Qed.


  Definition LN_to_N l (p : Pattern) (prf : length l >= greatest_dangling_index p) : NamedPattern l :=
    to_named l p prf.
  Program Definition default_N p := LN_to_N (evar_fresh_seq (free_evars p) (greatest_dangling_index p)) p _.
  Next Obligation.
    intros. pose proof (evar_fresh_seq_length (free_evars p) (greatest_dangling_index p)).
    rewrite H. lia.
  Defined.


  (* Finally, a few examples for metavariables: *)
  Fail Goal forall p1 p2 : Pattern,
    ∅ ⊢i p1 andₙ p2 --->ₙ p2 andₙ p1 using AnyReasoning. (* <- Coq cannot guess the names! *)

  Fail Goal forall p1 p2 : Pattern,
    ∅ ⊢i default_N p1 andₙ default_N p2 --->ₙ default_N p2 andₙ default_N p1 using AnyReasoning. (* The maximum is needed! *)

  Fail Goal forall p1 p2 : Pattern, well_formed p1 -> well_formed p2 ->
    ∅ ⊢i LN_to_N [] p1 andₙ LN_to_N [] p2 --->ₙ LN_to_N [] p2 andₙ LN_to_N [] p1 using AnyReasoning.
  (* At this point, it becomes increadibly hard to convert nameless patterns to named ones *)

  Lemma test : forall p1 p2 : NamedPattern [],
    well_formed_positive p1 -> well_formed_positive p2 ->
    well_formed_closed_mu_aux p1 0 -> well_formed_closed_mu_aux p2 0 -> 
    ∅ ⊢i p1 andₙ p2 --->ₙ p2 andₙ p1 using AnyReasoning.
  Proof.
    intros.
    (* The only advantage here, is that well-formedness is obtained from NamedPattern: *)
    assert (well_formed p1). { wf_auto2. pose proof (names_enough [] p1) as WF. simpl in WF.
                               replace 0 with (greatest_dangling_index p1) by lia. apply well_formed_dangling. }
    assert (well_formed p2). { wf_auto2. pose proof (names_enough [] p2) as WF. simpl in WF.
                               replace 0 with (greatest_dangling_index p2) by lia. apply well_formed_dangling. }
    (***)
    mlIntro "H".
    mlDestructAnd "H" as "H1" "H2".
    mlSplitAnd.
    mlExact "H2".
    mlExact "H1".
  Qed.

  Lemma test2 : forall p1 p2 : Pattern, well_formed p1 -> well_formed p2 ->
    ∅ ⊢i p1 and p2 ---> p2 and p1 using AnyReasoning.
  Proof.
    intros.
    Fail pose proof (test (LN_to_N [] p1) (LN_to_N [] p2)).
    (* The system is still backward compatible, but it is much harder to use, and prove this theorem *)
    epose (p1' := LN_to_N [] p1 _).
    epose (p2' := LN_to_N [] p2 _).
    Unshelve.
    2: { apply andb_true_iff in H as [_ H]. apply andb_true_iff in H as [_ H]. admit. (* doable with helpers *) }
    2: { apply andb_true_iff in H0 as [_ H0]. apply andb_true_iff in H0 as [_ H0]. admit. (* doable with helpers *) }
    pose proof (test p1' p2'). pose proof H. pose proof H0. Fail apply H1; wf_auto2.
    (* there are a lot of issues in this case. Hypotheses cannot be modified, and tactics fail because of that. *)
  Abort.


  Goal forall p1 p2 : NamedPattern [],
    well_formed_positive p1 -> well_formed_positive p2 ->
    well_formed_closed_mu_aux p1 0 -> well_formed_closed_mu_aux p2 0 -> 
    ∅ ⊢i p1 andₙ p2 --->ₙ p2 andₙ p1 using AnyReasoning.
  Proof.
    intros.
    epose proof (pf_iff_proj1 _ _ _ _ _ _ (patt_and_comm ∅ p1 p2 _ _)).
    use AnyReasoning in H3.
    apply H3.
    (* Nameless proofs are automatically lifted to named proofs *) 
    Unshelve.
    (* however, a number of well-formedness constraints remain to be solved *)
  Qed.

  (* Conclusion:
     - With this approach, we can solve all of our problems, moreover it becomes more complicated than previously
     - Especially, the conversion between the representations is problematic
     - However, solving the well-formedness constraints should be done automatically
  *)

End NamedPattern.
End test1.














(* Other experiments: *)
  (* Inductive NamedPattern4 : list string -> Set :=
  | npatt_bot : NamedPattern4 nil
  | npatt_imp (l1 l2 : list string) (p1: NamedPattern4 l1) (p2: NamedPattern4 l2) : NamedPattern4 (l1 ++ l2)
  | npatt_exs (l : list string) (x : string) (p: NamedPattern4 l) : NamedPattern4 (x::l)
  . *)

  (* This approach is not desirable, since there are two distinct constructors for variables: *)
  Inductive NamedPattern5 : list string -> Pattern -> Set :=
  | npatt_bot : NamedPattern5 l patt_bott
  | npatt_bevar x : index_of x l == Some n -> NamedPattern5 l (patt_bound_evar n)
  | npatt_fevar x : index_of x l == None   -> NamedPattern5 l (patt_free_evar x)
  | npatt_imp l1 l2 p1 p2 : NamedPattern5 l1 p1 -> NamedPattern5 l2 p2 -> NamedPattern5 (l1 ++ l2) (patt_imp p1 p2)
  | npatt_exs x l p : NamedPattern5 (x::l) p -> NamedPattern5 l (patt_exists p).


  Notation "⊥" := npatt_bot.
  Notation "'var' x" := (npatt_evar x) (at level 50).
  Notation "'exs' x , p" := (npatt_exs x _ _ p) (at level 50).
  Notation "p1 ----> p2" := (npatt_imp _ _ _ _ p1 p2) (at level 50).

  Open Scope string_scope.

  Definition mypatt1 := (npatt_exs "X" _ _ (npatt_bot)).
  Definition mypatt2 := exs "X", ⊥.
  Definition mypatt2 := exs "X", ⊥.
  Check mypatt1.
  Check mypatt2.


  Definition n_to_ln {l p} (_ : NamedPattern5 l p) : Pattern := p.

  Compute (n_to_ln mypatt1).

  Require Import MLPM.



(*
  3 task:
  - Pretty-print the named patterns in a readable way (also in MLPM)
  - Locally nameless theorems should be automatically lifted to the level of named patterns
  - Notations should be supported in the named syntax
  - Substitutions?


  - HOAS syntax?
*)


