
From MatchingLogic Require Import extralibrary.
From Coq Require Export ssreflect ssrfun ssrbool String.

From Coq.Classes Require Export RelationClasses.

From stdpp Require Export
  base
  list
  countable
  infinite
.

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
(* | op_bsvar (dbi : nat) *)
| op_fevar (x : opml_evar)
(* | op_fsvar (X : opml_svar) *)
| op_imp (φ1 φ2 : OPMLPattern)
| op_app (σ : opml_symbol) (args : list OPMLPattern)
| op_ex (σ : opml_sort) (φ : OPMLPattern)
(* | op_mu (s : opml_sort) (φ : OPMLPattern) *).

Section pat_ind.

  Variables
    (P : OPMLPattern -> Prop).
  Hypotheses
    (P_bot : P op_bot)
    (P_bevar : forall dbi, P (op_bevar dbi))
    (P_fevar : forall x, P (op_fevar x))
    (P_imp : forall φ, P φ -> forall ψ, P ψ -> P (op_imp φ ψ))
    (P_app : forall σ args, Forall P args -> P (op_app σ args))
    (P_ex : forall σ φ, P φ -> P (op_ex σ φ)).

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
     | op_imp φ1 φ2 => P_imp _ (OPML_ind φ1) _ (OPML_ind φ2) 
     | op_app σ args => _
     | op_ex σ φ => P_ex σ _ (OPML_ind φ)
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


Fixpoint well_sorted (p : OPMLPattern)
  (esorts : nat -> opml_sort)
  (ssorts : nat -> opml_sort)
  (s : opml_sort) {struct p} : bool.
Proof.
  revert p esorts ssorts s.
  refine (
  fix well_sorted p esorts ssorts s :=
  match p with
   | op_bot => true
   | op_bevar dbi => decide (esorts dbi = s)
(*    | op_bsvar dbi => decide (ssorts dbi = s) *)
   | op_fevar x => decide (evar_sort x = s)
(*    | op_fsvar X => decide (svar_sort X = s) *)
   | op_imp φ1 φ2 => well_sorted φ1 esorts ssorts s &&
                     well_sorted φ2 esorts ssorts s
   | op_app σ args =>
     (* foldr (fun x acc => well_sorted )
           (decide (opml_ret_sort σ = s))
           args *)
  (*    opml_arg_sorts σ *)
    _
   | op_ex s0 φ => well_sorted φ (shift esorts s0) ssorts s
(*    | op_mu s0 φ => well_sorted φ esorts (shift ssorts s0) s *)
  end).
  exact (forallb (fun '(p, s) => well_sorted p esorts ssorts s)
                (zip args (opml_arg_sorts σ))).
Fail Defined.
Abort.

(* If extraction is needed, this could be problematic: *)
Inductive well_sorted :
  OPMLPattern ->
  (nat -> option opml_sort) ->
  (* (nat -> option opml_sort) -> *)
  opml_sort -> Prop :=
| sorted_bot esorts (* ssorts *) s :
  well_sorted op_bot esorts (* ssorts *) s
| sorted_bevar n esorts (* ssorts *) s :
  esorts n = Some s ->
  well_sorted (op_bevar n) esorts (* ssorts *) s
(* | sorted_bsvar n esorts ssorts s :
  ssorts n = s ->
  well_sorted (op_bsvar n) esorts ssorts s *)
| sorted_fevar x esorts (* ssorts *) s :
  evar_sort x = s ->
  well_sorted (op_fevar x) esorts (* ssorts *) s
(* | sorted_fsvar X esorts ssorts s :
  svar_sort X = s ->
  well_sorted (op_fsvar X) esorts ssorts s *)
| sorted_imp p1 p2 esorts (* ssorts *) s :
  well_sorted p1 esorts (* ssorts *) s ->
  well_sorted p2 esorts (* ssorts *) s ->
  well_sorted (op_imp p1 p2) esorts (* ssorts *) s

| sorted_app σ args esorts (* ssorts *) s :
  Forall (fun p => well_sorted (fst p) esorts (* ssorts *) (snd p)) (zip args (opml_arg_sorts σ)) ->
  opml_ret_sort σ = s
->
  well_sorted (op_app σ args) esorts (* ssorts *) s

| sorted_ex p s0 esorts (* ssorts *) s :
  well_sorted p (shift esorts (Some s0)) (* ssorts *) s ->
  well_sorted (op_ex s0 p) esorts (* ssorts *) s
(* | sorted_mu p s0 esorts ssorts s :
  well_sorted p esorts (shift ssorts s0) s ->
  well_sorted (op_mu s0 p) esorts ssorts s *)
.

Fixpoint free_evar_subst (ps : OPMLPattern) (y : opml_evar)
  (p : OPMLPattern) : OPMLPattern :=
match p with
 | op_fevar x => if decide (x = y) then ps else p
 | op_imp φ1 φ2 => op_imp (free_evar_subst ps y φ1) (free_evar_subst ps y φ2)
 | op_app σ args => op_app σ (map (free_evar_subst ps y) args)
 | op_ex s φ => op_ex s (free_evar_subst ps y φ)
(*  | op_mu s φ => _ *)
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
 | op_app σ args => op_app σ (map (bevar_subst ps x) args)
 | op_ex s φ => op_ex s (bevar_subst ps (S x) φ)
(*  | op_mu s φ => _ *)
 | r => r
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

Lemma well_sorted_weaken :
  forall φ s fe fe',
    is_weaker fe' fe ->
    well_sorted φ fe s ->
    well_sorted φ fe' s.
Proof.
  induction φ using OPML_ind; intros; try by constructor.
  * invt H0.
    apply H in H2.
    by constructor.
  * invt H0.
    by constructor.
  * invt H0.
    constructor.
    - by eapply IHφ1.
    - by eapply IHφ2.
  * invt H1.
    constructor. 2: reflexivity.
    {
      remember (opml_arg_sorts σ) as xs.
      clear Heqxs. generalize dependent xs.
      induction H; simpl; intros. by constructor.
      case_match.
      - constructor.
      - invt H4. constructor.
        + simpl. eapply H in H6. apply H6. assumption.
        + eapply IHForall. assumption.
    }
  * invt H0. constructor. eapply IHφ. 2: eassumption.
    by apply is_weaker_shift.
Qed.

Lemma well_sorted_bevar_subst :
  forall φ ψ s s' fe n,
  well_sorted φ fe s ->
  well_sorted ψ default s' ->
  fe n = Some s' ->
  well_sorted (bevar_subst ψ n φ) fe s.
Proof.
  induction φ using OPML_ind; intros; simpl; try by constructor.
  * case_match; simpl; try by constructor.
    - inversion H. subst.
      by constructor.
    - invt H.
      rewrite H1 in H4. invt H4.
      eapply well_sorted_weaken. 2: eassumption.
      apply default_is_strongest.
    - inversion H. subst.
      by constructor.
  * constructor. inversion H; by subst.
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
  * inversion H; subst.
    constructor.
    eapply IHφ. assumption. eassumption.
    by cbn.
Defined.

End Syntax.

Section Test.

  Inductive sorts := bool | nat.
  Inductive symbols := add | is0 | zero | succ.

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
          end;
      opml_ret_sort :=
        fun x =>
          match x with
          | add => nat
          | is0 => bool
          | zero => nat
          | succ => nat
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
    
  Admitted.
  Next Obligation.
    
  Admitted.

  Open Scope string_scope.
  Goal
    well_sorted (op_fevar "x") (fun _ => nat) (fun _ => nat) nat.
  Proof.
    constructor. by cbn.
  Qed.

  Goal
    well_sorted (op_ex nat (op_app succ [op_fevar "x"]))
      (fun _ => nat) (fun _ => nat) nat.
  Proof.
    repeat constructor.
  Qed.

  Goal
    well_sorted (op_ex nat (op_app is0 [op_bevar 0]))
      (fun _ => nat) (fun _ => nat) bool.
  Proof.
    repeat constructor.
  Qed.
