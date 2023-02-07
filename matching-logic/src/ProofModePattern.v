From Coq Require Import ssreflect ssrfun ssrbool.

From Coq.Vectors Require Import Vector.

From Equations Require Import Equations.

From stdpp Require Import
    base
    gmap
    infinite
    natmap
    option
    strings
    vector
.
From MatchingLogic Require Import
    Signature
    Pattern
.

Require Import String.

Equations Derive Signature NoConfusion NoConfusionHom for vec.

Equations? list_map_pfin
    {A B : Type}
    (l : list A)
    (f : forall (x : A) (pf: x ∈ l), B)
    : list B :=
    list_map_pfin [] _ := [] ;
    list_map_pfin (x::xs) f := (f x _)::(list_map_pfin xs (fun x H => f x _)) .
Proof.
    {
        left.
    }
    {
        right. exact H.
    }
Qed.

Lemma list_map_pfin_spec {A B : Type} (f : A -> B) (l : list A) :
    list_map_pfin l (fun (x : A) (_ : x ∈ l) => f x) = List.map f l.
Proof.
  funelim (list_map_pfin l _).
  { reflexivity. }
  {
    simp list_map_pfin. rewrite H. reflexivity.
  }
Qed.

Definition VarName := string.
Definition EVarName := VarName.
Definition SVarName := VarName.


Definition incr_values
    (vm : gmap VarName nat)
    : gmap VarName nat
:= fmap (fun n => S n) vm.


Record PContext := mkPContext {
    pc_evm : gmap EVarName nat ;
    pc_svm : gmap SVarName nat ;
}.

Definition pc_add_ename
    (ctx : PContext)
    (name : EVarName) :=
    mkPContext ((<[name := 0]>(incr_values (pc_evm ctx)))) (pc_svm ctx)
.

Definition pc_add_sname
    (ctx : PContext)
    (name : SVarName) :=
    mkPContext (pc_evm ctx) ((<[name := 0]>(incr_values (pc_svm ctx))))
.

Definition Pattern_in_context
    {Σ : Signature} :=
    PContext -> Pattern
.

(*
 So what notations we want to support?
 ¬ϕ ≡ ϕ ---> ⊥
 ϕ₁ \/ ϕ₂ ≡ ¬ϕ₁ ---> ϕ₂
 ∀ x. ϕ ≡ ¬ ∃ x. ¬ ϕ
 So, a notation is parametric in
 (1) how many patterns it takes as an argument.
 (2) how many element variables it binds
 (3) how many set variables it binds.
*)
Record MLConstruct {Σ : Signature} := {
    (*mlc_level : nat ;*)
    mlc_arity : nat ;
    mlc_ebinder_arity : nat;
    mlc_sbinder_arity : nat;
    mlc_expand :
      list Pattern_in_context -> (* patterns *)
      list EVarName -> (* bound evars*)
      list SVarName -> (* bound svars*)
      option Pattern_in_context ;
    mlc_expand_almost_total :
        forall
            (args : list Pattern_in_context)
            (ebinders : list EVarName)
            (sbinders : list SVarName),
            List.length args = mlc_arity ->
            List.length ebinders = mlc_ebinder_arity ->
            List.length sbinders = mlc_sbinder_arity ->
            exists ϕ_in_context,
                mlc_expand args ebinders sbinders = Some ϕ_in_context  ;
}.

Section sec.
    Context
        {Σ : Signature}
        {string2evar : string -> evar}
        {string2evar_inj : Inj (=) (=) string2evar}
        {string2svar : string -> svar}
        {string2svar_inj : Inj (=) (=) string2svar}
    .
    Program Definition mlc_sym
        (s : symbols)
        : MLConstruct := {|
            mlc_arity := 0 ;
            mlc_ebinder_arity := 0 ;
            mlc_sbinder_arity := 0 ;
            mlc_expand :=
                fun _ =>
                fun _ =>
                fun _ => Some (
                    fun _ =>
                        patt_sym s
                )
        |}
    .
    Next Obligation.
        intros. eexists. reflexivity.
    Qed.

    Program Definition mlc_bott
        : MLConstruct := {|
            mlc_arity := 0 ;
            mlc_ebinder_arity := 0 ;
            mlc_sbinder_arity := 0 ;
            mlc_expand :=
                fun _ =>
                fun _ =>
                fun _ => Some(
                    fun _ =>
                    patt_bott
                )
        |}
    .
    Next Obligation.
        intros. eexists. reflexivity.
    Qed.
    

    Program Definition mlc_evar
        {name : EVarName}
        : MLConstruct := {|
            mlc_arity := 0 ;
            mlc_ebinder_arity := 0 ;
            mlc_sbinder_arity := 0 ;
            mlc_expand :=
                fun _ =>
                fun _ =>
                fun _ => Some (
                    fun ctx =>
                    match (pc_evm ctx) !! name with
                    | Some n => patt_bound_evar n
                    | None => patt_free_evar (string2evar name)
                    end
                )
        |}
    .
    Next Obligation.
        intros. eexists. reflexivity.
    Qed.


    Program Definition mlc_svar
        {name : SVarName}
        : MLConstruct := {|
            mlc_arity := 0 ;
            mlc_ebinder_arity := 0 ;
            mlc_sbinder_arity := 0 ;
            mlc_expand :=
                fun _ =>
                fun _ =>
                fun _ => Some (
                    fun ctx =>
                    match (pc_svm ctx) !! name with
                    | Some n => patt_bound_svar n
                    | None => patt_free_svar (string2svar name)
                    end
                )
        |}
    .
    Next Obligation.
        intros. eexists. reflexivity.
    Qed.


    Program Definition mlc_app
        : MLConstruct := {|
            mlc_arity := 2 ;
            mlc_ebinder_arity := 0 ;
            mlc_sbinder_arity := 0 ;
            mlc_expand :=
                fun ps =>
                fun _ =>
                fun _ => 
                    match ps !! 0 with
                    | None => None
                    | Some ϕ₁ =>
                      match ps !! 1 with
                      | None => None
                      | Some ϕ₂ =>
                        Some (
                            fun ctx =>
                            patt_app (ϕ₁ ctx) (ϕ₂ ctx)
                        )
                      end
                    end
        |}
    .
    Next Obligation.
        intros.
        destruct args as [|a1 args].
        1: { simpl in *; lia. }
        destruct args as [|a2 args].
        1: { simpl in *; lia. }
        eexists. simpl. reflexivity.
    Qed.


    Program Definition mlc_imp
        : MLConstruct := {|
            mlc_arity := 2 ;
            mlc_ebinder_arity := 0 ;
            mlc_sbinder_arity := 0 ;
            mlc_expand :=
                fun ps =>
                fun _ =>
                fun _ => 
                    match ps !! 0 with
                    | None => None
                    | Some ϕ₁ =>
                      match ps !! 1 with
                      | None => None
                      | Some ϕ₂ =>
                        Some (
                            fun ctx =>
                            patt_imp (ϕ₁ ctx) (ϕ₂ ctx)
                        )
                      end
                    end
        |}
    .
    Next Obligation.
        intros.
        destruct args as [|a1 args].
        1: { simpl in *; lia. }
        destruct args as [|a2 args].
        1: { simpl in *; lia. }
        eexists. simpl. reflexivity.
    Qed.

    Program Definition mlc_exists
        : MLConstruct := {|
            mlc_arity := 1 ;
            mlc_ebinder_arity := 1 ;
            mlc_sbinder_arity := 0 ;
            mlc_expand :=
                fun ps =>
                fun evs =>
                fun _ =>
                    match ps !! 0 with
                    | None => None
                    | Some ϕ_in_context =>
                        match evs !! 0 with
                        | None => None
                        | Some name =>
                            Some (
                                fun ctx =>
                                    let ctx' := pc_add_ename ctx name in
                                    let ϕ := ϕ_in_context ctx' in
                                    patt_exists ϕ
                            )
                        end
                    end
        |}
    .
    Next Obligation.
        intros.
        destruct args as [|a1 args].
        { simpl in *; lia. }
        destruct ebinders as [|e1 ebinders].
        { simpl in *; lia. }
        eexists. simpl. reflexivity.
    Qed.

    Program Definition mlc_mu
        : MLConstruct := {|
            mlc_arity := 1 ;
            mlc_ebinder_arity := 0 ;
            mlc_sbinder_arity := 1 ;
            mlc_expand :=
                fun ps =>
                fun _ =>
                fun svs =>
                    match ps !! 0 with
                    | None => None
                    | Some ϕ_in_context =>
                        match svs !! 0 with
                        | None => None
                        | Some name =>
                            Some (
                                fun ctx =>
                                    let ctx' := pc_add_sname ctx name in
                                    let ϕ := ϕ_in_context ctx' in
                                    patt_mu ϕ
                            )
                        end
                    end
        |}
    .
    Next Obligation.
        intros.
        destruct args as [|a1 args].
        { simpl in *; lia. }
        destruct sbinders as [|s1 sbinders].
        { simpl in *; lia. }
        eexists. simpl. reflexivity.
    Qed.

    (*
    Example:
    ∀ x. ∃ y. x ---> y
    ∀ x. ∃ y. x /\ y
    *)

    Inductive PMPattern : Set :=
    | pmpatt_inj (ln : Pattern)
    | pmpatt_construct
        (construct : MLConstruct)
        (args : vec PMPattern (mlc_arity construct))
        (bound_evars : vec EVarName (mlc_ebinder_arity construct))
        (bound_svars : vec SVarName (mlc_sbinder_arity construct))
    .

    (*

    Inductive PMPattern : Set :=
    | pmpatt_inj (ln : Pattern)
    | pmpatt_construct
        (construct : MLConstruct)
        (args : list PMPattern)
        (bound_evars : list EVarName)
        (bound_svars : list SVarName)
        (pfargs : base.length args = mlc_arity construct)
        (pfbe : base.length bound_evars = mlc_ebinder_arity construct)
        (pfbs : base.length bound_svars = mlc_sbinder_arity construct)
    .
    *)


    Equations PMPattern_size
        (ϕ : PMPattern)
        : nat := {
        PMPattern_size (pmpatt_inj _) := 1 ;
        PMPattern_size (pmpatt_construct _ args _ _) :=
            S (@PMPattern_size_vec _ args)
            where PMPattern_size_vec
            {arity : nat}
            (v : vec PMPattern arity)
            : nat := {
                @PMPattern_size_vec _ vnil := 1 ;
                @PMPattern_size_vec _ (vcons x xs) :=
                    (PMPattern_size x + PMPattern_size_vec xs)
            }
        }
    .

    Lemma PMPattern_size_clause_2_PMPattern_size_vec_spec
        a e s a' ar args':
        PMPattern_size_clause_2_PMPattern_size_vec PMPattern_size a e s a' ar args'
        = S (list_sum (fmap (fun p => PMPattern_size p) (vec_to_list args')))
    .
    Proof.
        Check fun_elim.
        induction args'; simpl.
        {
            reflexivity.
        }
        {
            rewrite IHargs'. simpl.
            unfold fmap. lia.
        }
    Qed.

    Equations? PMPattern_to_ln
    (ϕ : PMPattern)
    : Pattern_in_context by wf (PMPattern_size ϕ) lt := {
        PMPattern_to_ln (pmpatt_inj ln) := fun _ => ln ;
        PMPattern_to_ln (pmpatt_construct construct args bevars bsvars)
            with mlc_expand construct (list_map_pfin (vec_to_list args) (fun p pf => @PMPattern_to_ln p)) bevars bsvars => {
            | None := _ ;
            | Some phi := phi
            }
        
    }
    .
    Proof.
        {
            simp PMPattern_size.
            remember (vec_to_list args) as args'.
            apply elem_of_list_lookup_1 in pf.
            destruct pf as [i Hi].
            pose proof (Hargs := take_drop_middle args' i p Hi).
            subst. Set Printing All.
            unfold PMPattern_size_clause_2_PMPattern_size_vec.
            funelim (PMPattern_size_clause_2_PMPattern_size_vec)..
            simp PMPattern_size_clause_2_PMPattern_size_vec.
            simpl. 
            rewrite -Hargs.
            Check @take_drop_middle.
        }
        Search elem_of 
        
        
        Search lookup "mid".
    Qed.

    

    Proof.
        {
            move: construct bevars bsvars args PMPattern_to_ln PMPattern_vec_to_ln pf.
            intros construct.
            remember (mlc_arity construct) as arity in * |-.
            assert (Harity: mlc_arity construct <= arity) by lia.
            clear Heqarity.
            move: Harity.

            induction arity.
            {
                intros. destruct construct.
                simpl in *. subst. simpl in *.
                exfalso.
                destruct mlc_arity0.
                2: {
                    exfalso. lia.
                }
                clear -pf.
                inv_vec args. simpl. set_solver.
            }
            {
                intros HltSarity.
                destruct (decide (mlc_arity construct <= arity)) as [H|H].
                {
                    specialize (IHarity H).
                    intros.
                    auto.
                }
                {
                    assert (HSarity: mlc_arity construct = S arity) by lia.
                    clear H.
                    intros.
                    simp PMPattern_size.
                    remember args as args'.
                    rewrite HSarity in args'.
                    inv_vec args'.
                }

                specialize (IHargs mlc_expand0).

                simpl in *.
            }
            Set Printing Implicit.
            move: x xs pf.
            induction n.
            {
                intros x Hxxsargs pf.
                simpl in *.
                rewrite elem_of_subseteq in pf.
                specialize (pf x ltac:(left)).
            }
            simpl in pf.
            rewrite elem_of_subseteq in pf.
            specialize (pf x ltac:(left)).
            simp PMPattern_size.
        simp PMPattern_size_clause_2_PMPattern_size_vec.
        simp PMPattern_size_vec.
        }
    Qed.

    Equations? PMPattern_to_ln
        {Σ : Signature}
        (ϕ : PMPattern)
        : Pattern_in_context by wf (PMPattern_size ϕ) lt :=
    PMPattern_to_ln (pmpatt_inj ln) := fun _ => ln ;
    PMPattern_to_ln (pmpatt_construct construct args bevars bsvars)
      := let args' := vmap (fun p => @PMPattern_to_ln Σ p) args in
         mlc_expand construct args' bevars bsvars
    .
    Proof.
        simp PMPattern_size.
        clear.
        Set Printing Implicit.
        induction args.
    Qed.


Check sum_list.
Check vec_to_list.
Fixpoint PMPattern_size
    {Σ : Signature}
    (ϕ : PMPattern)
    : nat :=
    match ϕ with
    | pmpatt_evar _ => 1
    | pmpatt_svar _ => 1
    | pmpatt_sym _ => 1
    | pmpatt_bott => 1
    | pmpatt_app ϕ₁ ϕ₂ =>
        1 + (PMPattern_size ϕ₁) + (PMPattern_size ϕ₂)
    | pmpatt_imp ϕ₁ ϕ₂ =>
        1 + (PMPattern_size ϕ₁) + (PMPattern_size ϕ₂)
    | pmpatt_exists _ ϕ' => 1 + (PMPattern_size ϕ')
    | pmpatt_mu _ ϕ' => 1 + (PMPattern_size ϕ')
    | pmpatt_notation _ args _ _ =>
        1 + sum_list (fmap PMPattern_size (vec_to_list args))
    end
.

Equations Derive NoConfusion for PMPattern.
Equations Derive Subterm for PMPattern.

Check PMPattern_subterm.


    Check insert.

    Print PMPattern_direct_subterm.

    Equations? pmp2ln_aux 
        (ϕ : PMPattern)
    : Pattern by wf ϕ (PMPattern_direct_subterm Σ) :=
    pmp2ln_aux (pmpatt_evar x) := patt_bound_evar 0 ;
    pmp2ln_aux _ := patt_bound_evar 0 .


    Equations? pmp2ln_aux 
        (evm : gmap VarName nat)
        (svm : gmap VarName nat)
        (ϕ : PMPattern)
    : Pattern by wf ϕ PMPattern_subterm :=
    pmp2ln_aux evm svm (pmpatt_evar x) :=
        match evm !! x with
        | Some n => patt_bound_evar n
        | None => patt_free_evar (string2evar x)
        end.


    Fixpoint pmp2ln_aux
        (evm : gmap VarName nat)
        (svm : gmap VarName nat)
        (ϕ : PMPattern)
        : Pattern :=
        match ϕ with
        | pmpatt_evar x =>
            match evm !! x with
            | Some n => patt_bound_evar n
            | None => patt_free_evar (string2evar x)
            end
        | pmpatt_svar x =>
            match svm !! x with
            | Some n => patt_bound_svar n
            | None => patt_free_svar (string2svar x)
            end
        | pmpatt_sym s => patt_sym s
        | pmpatt_bott => patt_bott
        | pmpatt_app ϕ₁ ϕ₂ =>
            patt_app
                (pmp2ln_aux evm svm ϕ₁)
                (pmp2ln_aux evm svm ϕ₂)
        | pmpatt_imp ϕ₁ ϕ₂ =>
            patt_imp
                (pmp2ln_aux evm svm ϕ₁)
                (pmp2ln_aux evm svm ϕ₂)
        | pmpatt_exists name ϕ' =>
            patt_exists
                (pmp2ln_aux
                    (<[name := 0]>(incr_values evm))
                    svm ϕ')
        | pmpatt_mu name ϕ' =>
            patt_mu
                (pmp2ln_aux
                    evm
                    (<[name := 0]>(incr_values svm))
                    ϕ')
        | pmpatt_notation notation args bound_evars bound_svars =>
            mlc_expand
                notation
                (vmap (fun ϕ' => pmp2ln_aux evm svm) args)
                bound_evars
                bound_svars
        end
        .
    Admitted.

    Definition pmp2ln
        {Σ : Signature}
        (ϕ : PMPattern)
        : Pattern :=
        pmp2ln_aux ϕ ∅ ∅.


