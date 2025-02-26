
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
    opml_subsort : relation opml_sort;
    opml_subsort_po :: PartialOrder opml_subsort;
}.

Class OPMLVariables {Ss : OPMLSorts} := mkOPMLVariables {
  opml_evar : Set;
  opml_svar : Set;
  opml_evar_eqdec :: EqDecision opml_evar;
  opml_evar_countable :: Countable opml_evar;
  opml_evar_infinite :: Infinite opml_evar;
  opml_svar_eqdec :: EqDecision opml_svar;
  opml_svar_countable :: Countable opml_svar;
  opml_svar_infinite :: Infinite opml_svar;

  evar_sort : opml_evar -> opml_sort;
  svar_sort : opml_svar -> opml_sort;
}.

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

  Search Forall.
  Check Forall_ind.

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
  (p : OPMLPattern) {struct p} : bool :=(* 
Proof.
  revert p esorts ssorts s.
  refine (
  fix well_sorted p esorts ssorts s := *)
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

(* (* If extraction is needed, this could be problematic: *)
Inductive well_sorted :
  OPMLPattern ->
  (nat -> option opml_sort) ->
  (nat -> option opml_sort) ->
  opml_sort -> Prop :=
| sorted_bot esorts ssorts s :
  well_sorted op_bot esorts ssorts s
| sorted_bevar n esorts ssorts s :
  esorts n = Some s ->
  well_sorted (op_bevar n) esorts ssorts s
| sorted_bsvar n esorts ssorts s :
  ssorts n = Some s ->
  well_sorted (op_bsvar n) esorts ssorts s
| sorted_fevar x esorts ssorts s :
  evar_sort x = s ->
  well_sorted (op_fevar x) esorts ssorts s
| sorted_fsvar X esorts ssorts s :
  svar_sort X = s ->
  well_sorted (op_fsvar X) esorts ssorts s
| sorted_imp p1 p2 esorts ssorts s :
  well_sorted p1 esorts ssorts s ->
  well_sorted p2 esorts ssorts s ->
  well_sorted (op_imp p1 p2) esorts ssorts s

| sorted_app σ args esorts ssorts s :
  Forall (fun p => well_sorted (fst p) esorts ssorts (snd p)) (zip args (opml_arg_sorts σ)) ->
  opml_ret_sort σ = s
->
  well_sorted (op_app σ args) esorts ssorts s

| sorted_ex p s0 esorts ssorts s :
  well_sorted p (shift esorts (Some s0)) ssorts s ->
  well_sorted (op_ex s0 p) esorts ssorts s
| sorted_mu p s0 esorts ssorts s :
  well_sorted p esorts (shift ssorts (Some s0)) s ->
  well_sorted (op_mu s0 p) esorts ssorts s
.
 *)
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

(* Definition update {T : Set} (x : nat) (d : T) (f : nat -> T) : nat -> T :=
  fun y =>
    if decide (x = y) then d else f y. *)

Definition default : nat -> option opml_sort := fun _ : nat => None.

Definition is_weaker (f1 f2 : nat -> option opml_sort) : Prop :=
  forall n s, f2 n = Some s -> f1 n = Some s.

Notation "f '≤ₛ' g" := (is_weaker f g) (at level 50).

Lemma default_is_strongest :
  forall f, f ≤ₛ default.
Proof.
  intros f n σ H.
  unfold default in H.
  inversion H.
Qed.

Lemma is_weaker_refl :
  forall f, is_weaker f f.
Proof.
  intros. intro. intros.
  assumption.
Qed.

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
Qed.


Ltac invt H :=
inversion H; subst; clear H.

(* Lemma well_sorted_weaken :
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
    {
      induction args; simpl in *.
      * case_match; by auto.
      * case_match. by auto.
        destruct H. erewrite H.
    }
  * invt Hwf. constructor. eapply IHφ. 3: eassumption.
    by apply is_weaker_shift.
    assumption.
  * invt Hwf. constructor. eapply IHφ. 3: eassumption.
    assumption.
    by apply is_weaker_shift.
Qed.

Lemma well_sorted_bevar_subst :
  forall φ ψ s s' fe fs n,
  well_sorted φ fe fs s ->
  well_sorted ψ default default s' ->
  fe n = Some s' ->
  well_sorted (bevar_subst ψ n φ) fe fs s.
Proof.
  induction φ using OPML_ind; intros; simpl; try by constructor.
  * case_match; simpl; try by constructor.
    - inversion H. subst.
      by constructor.
    - invt H.
      rewrite H1 in H4. invt H4.
      eapply well_sorted_weaken. 3: eassumption.
      apply default_is_strongest.
      apply default_is_strongest.
    - inversion H. subst.
      by constructor.
  * constructor. inversion H; by subst.
  * invt H.
    by constructor.
  * invt H.
    by constructor.
  * inversion H; subst.
    constructor.
    - by eapply IHφ1.
    - by eapply IHφ2.
  * invt H0. constructor. 2: reflexivity.
    {
      remember (opml_arg_sorts σ) as xs.
      clear Heqxs. generalize dependent xs.
      induction H; simpl; intros. by constructor.
      case_match.
      - constructor.
      - invt H5. constructor.
        + simpl. eapply H in H7; eassumption.
        + eapply IHForall. assumption.
    }
  * invt H; subst.
    constructor.
    eapply IHφ. assumption. eassumption.
    by cbn.
  * invt H; subst.
    constructor.
    eapply IHφ. assumption. 2: by cbn.
    assumption.
Defined. *)

End Syntax.

Module Test.

  Inductive sorts := bool | nat.
  Inductive symbols := add | is0 | zero | succ | true | false.

Print OPMLSymbols.
  Program Instance NatSig : OPMLSignature := {|
    opml_sorts := {|
      opml_sort := sorts;
    |};
    opml_variables := {|
      opml_evar := string;
      opml_svar := string;
      evar_sort :=
        fun x =>
          if String.eqb x "x"%string
          then nat
          else if String.eqb x "y"%string
          then nat
          else bool;
      svar_sort :=
        fun x =>
          if String.eqb x "x"%string
          then nat
          else if String.eqb x "y"%string
          then nat
          else bool;
    |};
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
  Next Obligation.
    solve_decision.
  Defined.
  Next Obligation.
  Admitted.
  Next Obligation.
  Admitted.
  Next Obligation.
  Admitted.
  Next Obligation.
    solve_decision.
  Defined.
  Next Obligation.
  Admitted.

  Open Scope string_scope.
  Goal
    well_sorted  default default nat (op_fevar "x").
  Proof.
    by cbn.
  Qed.

  Goal
    well_sorted default default nat (op_ex nat (op_app succ [op_fevar "x"])).
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
        exact ∅.
      * (* op_mu *)
        exact ∅.
    Defined.
  Print opml_eval.

  Definition satM φ s (ws : well_sorted default default s φ) :=
    forall ρ, opml_eval ρ φ ws = ⊤.
  Definition Theory :=
    (* { Γ : propset OPMLPattern & forall φ, φ ∈ Γ -> exists s, well_sorted default default s φ}. *)
    (* propset {φ : OPMLPattern & exists s, well_sorted default default s φ}. *)
    propset OPMLPattern.
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

  Definition NatTheory : Theory :=
  {[
    op_eq bool nat (op_app is0 [op_app zero []]) (op_app true []) (* ;
    op_app is0 [op_app succ [op_ev x]] *)
  ]}.

  Require Import Coq.Program.Equality.

  Goal
    @satT _ NatModel NatTheory.
  Proof.
    unfold satT.
    intros.
    unfold NatTheory in *.
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
  Qed.

End TestSemantics.

