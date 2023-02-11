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

Lemma length_list_map_pfin
    {A B : Type}
    (l : list A)
    (f : forall (x : A) (pf: x ∈ l), B)
    :
    List.length (list_map_pfin l f) = List.length l
.
Proof.
    induction l.
    {
        simpl. reflexivity.
    }
    {
        simpl. simp list_map_pfin. simpl. rewrite IHl. reflexivity.
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

Record Pattern_in_context
    {Σ : Signature} := mkPIC {
      pic_pic: PContext -> Pattern;
      pic_wf : forall (pc : PContext),
        Pattern.well_formed (pic_pic pc) ;
    }
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
Record MLConstruct
    (mlc_arity : nat)
    (mlc_ebinder_arity : nat)
    (mlc_sbinder_arity : nat)
    {Σ : Signature} := {
    (*mlc_level : nat ;*)

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
    .
    
    Inductive PMPattern : Set :=
    | pmpatt_inj (ln : Pattern) (wfpf : Pattern.well_formed ln)
    | pmpatt_construct
        {a ea sa : nat}
        (construct : MLConstruct a ea sa)
        (args : vec PMPattern a)
        (bound_evars : vec EVarName ea)
        (bound_svars : vec SVarName sa)
    .

    Equations PMPattern_size
        (ϕ : PMPattern)
        : nat := {
        PMPattern_size (pmpatt_inj _ _) := 1 ;
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
        (ar1 ea1 sa1 : nat) (con : MLConstruct ar1 ea1 sa1) a e s ar args':
        @PMPattern_size_clause_2_PMPattern_size_vec PMPattern_size ar1 ea1 sa1 con a e s  ar args'
        = S (list_sum (fmap (fun p => PMPattern_size p) (vec_to_list args')))
    .
    Proof.
        induction args'; simpl.
        {
            reflexivity.
        }
        {
            rewrite IHargs'. simpl.
            unfold fmap. lia.
        }
    Qed.

    Equations eq_apply_4
    {T1 T2 T3 T4 R : Type}
    (f: T1 -> T2 -> T3 -> T4 -> R)
    (arg1 : T1)
    (arg2 : T2)
    (arg3 : T3)
    (arg4 : T4)
    :
    {r : R & r = f arg1 arg2 arg3 arg4} :=
    eq_apply_4 f arg1 arg2 arg3 arg4
      := existT (f arg1 arg2 arg3 arg4) (@eq_refl _ _) .
    
    Definition eq_apply_5
        {T1 T2 T3 T4 T5 R : Type}
        (f: T1 -> T2 -> T3 -> T4 -> T5 -> R)
        (arg1 : T1)
        (arg2 : T2)
        (arg3 : T3)
        (arg4 : T4)
        (arg5 : T5)
        :
        {r : R & r = f arg1 arg2 arg3 arg4 arg5}
    .
    Proof.
        exists (f arg1 arg2 arg3 arg4 arg5).
        reflexivity.
    Defined.


    Definition eq_apply_7
    {T1 T2 T3 T4 T5 T6 T7 R : Type}
    (f: T1 -> T2 -> T3 -> T4 -> T5 -> T6 -> T7 -> R)
    (arg1 : T1)
    (arg2 : T2)
    (arg3 : T3)
    (arg4 : T4)
    (arg5 : T5)
    (arg6 : T6)
    (arg7 : T7)
    :
    {r : R & r = f arg1 arg2 arg3 arg4 arg5 arg6 arg7}
    .
    Proof.
        exists (f arg1 arg2 arg3 arg4 arg5 arg6 arg7).
        reflexivity.
    Defined.

    Program Definition expand_total
        {ar ea sa : nat}
        (construct : @MLConstruct ar ea sa Σ)
        (args : vec PMPattern ar)
        (bevars : vec EVarName ea)
        (bsvars : vec SVarName sa)
        (f : forall (p : PMPattern), p ∈ (vec_to_list args) -> Pattern_in_context)
        : Pattern_in_context :=
        match (eq_apply_4 (mlc_expand ar ea sa) construct (list_map_pfin (vec_to_list args) (fun p => fun pf => f p pf)) bevars bsvars) with
        | existT None Hcontra => @False_rec _ _
        | existT (Some phi) _ => phi
        end.
    Next Obligation.
        intros.
        cbn in Hcontra.
        match type of Hcontra  with
        | _ = mlc_expand _ _ _ _ (list_map_pfin _ ?x) _ _ => remember x as some_lambda
        end.
        clear Heqsome_lambda.
        match type of Hcontra with
        | None = mlc_expand ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?a7 
            =>
            pose proof (Htmp := mlc_expand_almost_total a1 a2 a3 a4 a5 a6 a7)
        end.
        feed specialize Htmp.
        {
            rewrite length_list_map_pfin.
            rewrite vec_to_list_length.
            reflexivity.
        }
        {
            rewrite vec_to_list_length.
            reflexivity.
        }
        {
            rewrite vec_to_list_length.
            reflexivity.
        }
        destruct Htmp as [ϕ_in_context Hϕ_in_context].
        clear Heq_anonymous.
        rewrite Hϕ_in_context in Hcontra.
        inversion Hcontra.
    Qed.


    Equations? PMPattern_to_ln
    (ϕ : PMPattern)
    : Pattern_in_context by wf (PMPattern_size ϕ) lt := {
        PMPattern_to_ln (pmpatt_inj ln _) := mkPIC _ (fun _ => ln ) _;
        PMPattern_to_ln (pmpatt_construct construct args bevars bsvars) :=
            expand_total construct args bevars bsvars (fun p pf => PMPattern_to_ln p)            
    }
    .
   Proof.
        {
            intros. exact wfpf.
        }
        {
            clear PMPattern_to_ln.
            simp PMPattern_size.
            rewrite PMPattern_size_clause_2_PMPattern_size_vec_spec.
            remember (vec_to_list args) as args'.
            apply elem_of_list_lookup_1 in pf.
            destruct pf as [i Hi].
            pose proof (Hargs := take_drop_middle args' i p Hi).
            subst.
            rewrite -Hargs;
            rewrite fmap_app;
            rewrite list_sum_app;
            simpl;
            lia.
        }
    Defined.

    Program Definition mlc_sym
        (s : symbols)
        : MLConstruct 0 0 0 := {|
            mlc_expand :=
                fun _ =>
                fun _ =>
                fun _ => Some (
                    mkPIC _ (
                    fun _ =>
                        patt_sym s
                    ) (
                        fun _ => eq_refl
                    )
                )
        |}
    .
    Next Obligation.
        intros. eexists. reflexivity.
    Qed.

    Program Definition mlc_bott
        : MLConstruct 0 0 0 := {|
            mlc_expand :=
                fun _ =>
                fun _ =>
                fun _ => Some(
                    mkPIC _ (
                    fun _ =>
                    patt_bott
                )  (
                    fun _ => eq_refl
                )
                )
        |}
    .
    Next Obligation.
        intros. eexists. reflexivity.
    Qed.
    

    Program Definition mlc_evar
        (name : EVarName)
        : MLConstruct 0 0 0 := {|
            mlc_expand :=
                fun _ =>
                fun _ =>
                fun _ => Some (mkPIC _ (
                    fun ctx =>
                    match (pc_evm ctx) !! name with
                    | Some n => patt_bound_evar n
                    | None => patt_free_evar (string2evar name)
                    end
                ))
        |}
    .
    Next Obligation.
        intros. eexists. reflexivity.
    Qed.


    Program Definition mlc_svar
        (name : SVarName)
        : MLConstruct 0 0 0:= {|
            mlc_expand :=
                fun _ =>
                fun _ =>
                fun _ => Some (mkPIC _ (
                    fun ctx =>
                    match (pc_svm ctx) !! name with
                    | Some n => patt_bound_svar n
                    | None => patt_free_svar (string2svar name)
                    end
                ))
        |}
    .
    Next Obligation.
        intros. eexists. reflexivity.
    Qed.


    Program Definition mlc_app
        : MLConstruct 2 0 0 := {|
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
                        Some (mkPIC _ (
                            fun ctx => 
                            patt_app (pic_pic ϕ₁ ctx) (pic_pic ϕ₂ ctx)
                            )
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
        : MLConstruct 2 0 0 := {|
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
                        Some ( mkPIC _ (
                            fun ctx =>
                            patt_imp (pic_pic ϕ₁ ctx) (pic_pic ϕ₂ ctx)
                        ))
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
        : MLConstruct 1 1 0 := {|
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
                            Some ( mkPIC _ (
                                fun ctx =>
                                    let ctx' := pc_add_ename ctx name in
                                    let ϕ := pic_pic ϕ_in_context ctx' in
                                    patt_exists ϕ
                            ))
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
        : MLConstruct 1 0 1 := {|
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
                            Some ( mkPIC _ (
                                fun ctx =>
                                    let ctx' := pc_add_sname ctx name in
                                    let ϕ := pic_pic ϕ_in_context ctx' in
                                    patt_mu ϕ
                            ))
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

    Section examples.
        Context
            {s1 : symbols}
        .

        Local Example ex_1 : PMPattern :=
            pmpatt_construct (mlc_sym s1) vnil vnil vnil
        .


        Local Example Ex_2 : PMPattern :=
            pmpatt_construct (mlc_imp)
                [# ex_1; ex_1] vnil vnil.

    End examples.

End sec.