From MatchingLogic.Experimental Require Export Kore_alternative.

Set Default Proof Mode "Classic".

Section classes.

  Context {Σ : Signature}.

  Fixpoint n_ary (n : nat) (base : Set) : Set :=
  match n with
  | O => base
  | S n' => Pattern -> n_ary n' base
  end.

  Compute n_ary 2 Pattern. (* e.g. patt_and *)
  Compute n_ary 2 bool.    (* e.g. well-formedness of patt_and *)

  Fixpoint n_ary_forall (n : nat)
     (f : Pattern -> bool) : n_ary n bool -> n_ary n Pattern -> Set :=
  match n as n'
  return (n_ary n' bool -> n_ary n' Pattern → Set) with
  | 0 => λ(g : bool)(p : Pattern), f p = g
  | S n' => λ(g : Pattern -> n_ary n' bool)
             (h : Pattern -> n_ary n' Pattern),
               forall p : Pattern,
                 n_ary_forall  n' f (g p) (h p)
  end.

  Eval simpl in n_ary_forall 2 well_formed
   (fun p q => well_formed p && well_formed q) patt_and.

  Class WFconstruct (n : nat) (construct : n_ary n Pattern)
    (f : n_ary n bool) := {
    wf_n_ary :
      n_ary_forall n well_formed f construct;
  }.

  #[global]
  Instance patt_and_wf : WFconstruct 2 patt_and (fun p q => well_formed p && well_formed q).
  Proof.
    constructor. simpl. intros. wf_auto2.
  Defined.

  #[global]
  Instance patt_or_wf : WFconstruct 2 patt_or (fun p q => well_formed p && well_formed q).
  Proof.
    constructor. simpl. intros. wf_auto2.
  Defined.

  #[global]
  Instance patt_ex_wf : WFconstruct 1 patt_exists
    (fun p => well_formed_xy 1 0 p).
  Proof.
    constructor. simpl. intros. wf_auto2.
    cbv. wf_auto2.
  Defined.

  Local Goal
    forall φ ψ ξ,
    well_formed φ ->
    well_formed ψ ->
    well_formed (ex , ξ) ->
    well_formed (φ and ψ) /\
    well_formed (φ or ψ) /\
    well_formed (ex , ξ).
  Proof.
    intros.

    Ltac fun_of x :=
    lazymatch x with
    | ?f ?Σ =>
      lazymatch type of Σ with
      | Signature => x
      | _ => fun_of f
      end
    | _ => fail
    end.

Ltac arity_of x k :=
  match x with
  | ?f ?Σ =>
    match type of Σ with
    | Signature => k
    | _ => arity_of f (S k)
    end
  | _ => idtac "fail"; fail
  end.

    (* lazymatch goal with
    |- is_true (well_formed ?x) =>
      let y := fun_of x in 
      let a := arity_of x O in
      idtac y;
      idtac a
    end. *)

   Ltac trial :=
   match goal with
    |- context C [well_formed ?x] => 
       let f := (fun_of x) in
       let a := (arity_of x O) in
       rewrite (@wf_n_ary a f _ ltac:(typeclasses eauto))
    end.
    trial.
    trial.
    trial.
    
    rewrite (@wf_n_ary _ _ _ ltac:(typeclasses eauto)).
    rewrite (@wf_n_ary _ _ _ ltac:(typeclasses eauto)).
    rewrite H1.
  Qed.


End classes.
