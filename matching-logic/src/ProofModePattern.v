From Coq Require Import ssreflect ssrfun ssrbool.

From Coq.Vectors Require Import Vector.

From Equations Require Import Equations.

From stdpp Require Import
    base
    gmap
    infinite
    list
    natmap
    option
    strings
    sets
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

Definition renaming_function
    (new_key old_key some_key : VarName) : VarName :=
    match (decide (some_key = old_key)) with
    | left _ => new_key
    | right _ => 
        match (decide (some_key = new_key)) with
        | left _ => old_key
        | right _ => some_key
        end 
    end.


#[global]
Instance renaming_function_injective new_name old_name:
    Inj eq eq (renaming_function new_name old_name).
Proof.
    intros x y H.
    unfold renaming_function in H.
    repeat case_match; subst; try congruence.
Qed.

Definition update_key
    (new_key old_key : VarName)
    (m : gmap VarName nat)
    : gmap VarName nat
    := kmap (renaming_function new_key old_key) m
.

Definition update_evm_key
    (new_key old_key : EVarName)
    (pctx : PContext)
    : PContext
    := mkPContext
        (update_key new_key old_key (pc_evm pctx))
        (pc_svm pctx)
.

Definition update_svm_key
    (new_key old_key : SVarName)
    (pctx : PContext)
    : PContext
    := mkPContext
        (pc_evm pctx)
        (update_key new_key old_key (pc_svm pctx))
.

Definition max_value (d : nat) (m : gmap VarName nat) : nat :=
    map_fold (fun k v r => Nat.max v r) d m
.

Lemma max_value_kmap (f : VarName -> VarName) {injF : Inj eq eq f} (d : nat) (m : gmap VarName nat):
    max_value d (kmap f m) = max_value d m
.
Proof.
    unfold max_value.
    induction m using map_ind.
    {
        rewrite kmap_empty. reflexivity.
    }
    {
        rewrite kmap_insert.
        rewrite map_fold_insert.
        {
            intros.
            lia.
        }
        {
            rewrite lookup_kmap.
            exact H.
        }
        rewrite Nat.max_comm.
        rewrite IHm. clear IHm.
        rewrite map_fold_insert.
        {
            intros.
            lia.
        }
        {
            exact H.
        }
        rewrite Nat.max_comm.
        reflexivity.
    }
Qed.

Lemma max_value_in_leq
    (m : gmap VarName nat)
    (d : nat)
    (name : VarName)
    :
    m !! name = Some d ->
    d <= max_value 0 m
.
Proof.
    unfold max_value.
    move: m.
    eapply (map_fold_ind (
        fun resulting_value original_map =>
        original_map !! name = Some d ->
        d <= resulting_value
    ) (fun (_ : VarName) (v r : nat) => v `max` r)).
    {
        intros H.
        rewrite lookup_empty in H. inversion H.
    }
    {
        intros i x m r Hmi IH H.
        rewrite lookup_insert_Some in H.
        destruct H as [[H1 H2]|[H1 H2]].
        {
            subst. lia.
        }
        {
            specialize (IH H2).
            lia.
        }
    }
Qed.

Definition boundary_value (m : gmap VarName nat) : nat :=
    match (decide (m = ∅)) with
    | left _ => 0
    | right _ =>     S (max_value 0 m)
    end
.

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
        let phi := pic_pic pc in
        well_formed_positive phi /\ (* TODO no_negative, no_positive_occurrence*)
        well_formed_closed_ex_aux phi (boundary_value (pc_evm pc)) /\
        well_formed_closed_mu_aux phi (boundary_value (pc_svm pc)) ;
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
            intros.
            pose proof (wfpf' := wfpf).
            unfold well_formed in wfpf'.
            unfold is_true in wfpf'.
            apply andb_prop in wfpf'.
            destruct wfpf' as [wfp wfc].
            unfold well_formed_closed in wfc.
            apply andb_prop in wfc.
            destruct wfc as [wfcs wfce].
            split.
            { apply wfp. }
            split.
            {
                eapply well_formed_closed_ex_aux_ind;[| apply wfce].
                lia.
            }
            {
                eapply well_formed_closed_mu_aux_ind;[| apply wfcs].
                lia.
            }
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
                        fun _ => _
                    )
                )
        |}
    .
    Next Obligation.
        intros. repeat split;reflexivity.
    Qed.
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
                    fun _ => _
                )
                )
        |}
    .
    Next Obligation.
        intros. repeat split;reflexivity.
    Qed.
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
                ) _ )
        |}
    .
    Next Obligation.
        intros. simpl in phi.
        remember (pc_evm pc !! name) as oidx.
        destruct oidx.
        2: {
            repeat split; reflexivity.
        }
        unfold phi. clear phi. simpl.
        repeat split; try reflexivity.
        destruct (decide (d < boundary_value (pc_evm pc))) as [y|n].
        { reflexivity. }
        unfold boundary_value in n.
        exfalso. apply n. clear n.
        destruct (decide (pc_evm pc = ∅)) as [y|n] eqn:Heq.
        {
            exfalso.
            rewrite y in Heqoidx.
            rewrite lookup_empty in Heqoidx.
            inversion Heqoidx.
        }
        rewrite Heq.
        destruct d as [|d].
        { lia. }
        cut (d < max_value 0 (pc_evm pc)).
        {
            intros ?. lia.
        }
        symmetry in Heqoidx.
        apply max_value_in_leq with (name := name).
        apply Heqoidx.
    Qed.
    Next Obligation.
        intros. eexists. reflexivity.
    Qed.

    Lemma wfp_update_evm_key ϕic new_name old_name pc:
        well_formed_positive (pic_pic ϕic pc) = true ->
        well_formed_positive (pic_pic ϕic (update_evm_key new_name old_name pc)) = true.
    Proof.
        intros H.
        destruct ϕic as [pic0 wf0].
        apply wf0.
    Qed.

    Lemma wfp_update_svm_key ϕic new_name old_name pc:
    well_formed_positive (pic_pic ϕic pc) = true ->
    well_formed_positive (pic_pic ϕic (update_svm_key new_name old_name pc)) = true.
    Proof.
        intros H.
        destruct ϕic as [pic0 wf0].
        apply wf0.
    Qed.

    Lemma boundary_value_update_key new_name old_name store:
         boundary_value (update_key new_name old_name store)
         = boundary_value store
    .
    Proof.
        unfold boundary_value.
        destruct (decide (store = ∅)) as [se | sne] eqn:Heq,
                 (decide (update_key new_name old_name store = ∅)) as [nse | nsne] eqn:Hneq.
        {
            reflexivity.
        }
        {
            clear Heq Hneq. subst store.
            exfalso.
            unfold update_key in nsne.
            rewrite kmap_empty in nsne.
            apply nsne. reflexivity.
        }
        {
            exfalso.
            clear Heq Hneq.
            unfold update_key in nse.
            rewrite kmap_empty_iff in nse.
            subst store. apply sne. reflexivity.
        }
        apply f_equal.
        unfold update_key.
        clear Heq Hneq nsne sne.
        induction store using map_ind.
        {
            rewrite kmap_empty. reflexivity.
        }
        {
            unfold max_value.
            rewrite kmap_insert.
            rewrite map_fold_insert.
            {
                intros. lia.
            }
            {
                rewrite lookup_kmap. exact H.
            }
            unfold max_value in IHstore.
            rewrite IHstore. clear IHstore.
            rewrite map_fold_insert.
            { intros. lia. }
            { exact H. }
            reflexivity.
        }
    Qed.


    Lemma wfcex_update_evm_key ϕic new_name old_name pc:
        well_formed_closed_ex_aux (pic_pic ϕic pc) (boundary_value (pc_evm pc)) = true ->
        well_formed_closed_ex_aux
            (pic_pic ϕic (update_evm_key new_name old_name pc))
            (boundary_value (pc_evm pc)) = true
    .
    Proof.
        intros H.
        destruct ϕic as [pic0 wf0]. simpl in *.
        specialize (wf0 ((update_evm_key new_name old_name pc))).
        destruct wf0 as [_ [Hwfcex _]].
        cbn in *.
        rewrite boundary_value_update_key in Hwfcex.
        exact Hwfcex.
    Qed.

    Lemma wfcmu_update_svm_key ϕic new_name old_name pc:
        well_formed_closed_mu_aux (pic_pic ϕic pc) (boundary_value (pc_svm pc)) = true ->
        well_formed_closed_mu_aux
            (pic_pic ϕic (update_svm_key new_name old_name pc))
            (boundary_value (pc_svm pc)) = true
    .
    Proof.
        intros H.
        destruct ϕic as [pic0 wf0]. simpl in *.
        specialize (wf0 ((update_svm_key new_name old_name pc))).
        destruct wf0 as [_ [_ Hwfcmu]].
        cbn in *.
        rewrite boundary_value_update_key in Hwfcmu.
        exact Hwfcmu.
    Qed.

    Program Definition mlc_evar_rename
    (new_name old_name : EVarName)
    : MLConstruct 1 0 0 := {|
        mlc_expand :=
            fun ps _ _ =>
                match ps !! 0 with
                | None => None
                | Some ϕ_in_context =>
                    Some ( mkPIC _ (
                            fun ctx : PContext =>
                                let new_ctx := update_evm_key new_name old_name ctx in
                                pic_pic ϕ_in_context new_ctx
                        ) _ )
                end
    |}
    .
    Next Obligation.
        intros.
        unfold phi. clear phi.
        repeat split.
        {
            apply wfp_update_evm_key.
            apply ϕ_in_context. 
        }
        {
            destruct ϕ_in_context.
            apply wfcex_update_evm_key.
            apply pic_wf0.
        }
        {
            destruct ϕ_in_context.
            simpl in *.
            pose proof (pic_wf1 := pic_wf0).
            specialize (pic_wf1 (update_evm_key new_name old_name pc)).
            destruct pic_wf1 as [Hwfp [Hwfcex Hwfcmu]]. simpl in *.
            apply Hwfcmu.
        }
    Qed.
    Next Obligation.
        intros. simpl.
        destruct args as [|a1 args].
        1: { simpl in *; lia. }
        simpl.
        eexists. reflexivity.
    Qed.

    Program Definition mlc_svar_rename
    (new_name old_name : SVarName)
    : MLConstruct 1 0 0 := {|
        mlc_expand :=
            fun ps _ _ =>
                match ps !! 0 with
                | None => None
                | Some ϕ_in_context =>
                    Some ( mkPIC _ (
                            fun ctx : PContext =>
                                let new_ctx := update_svm_key new_name old_name ctx in
                                pic_pic ϕ_in_context new_ctx
                        ) _ )
                end
    |}
    .
    Next Obligation.
        intros.
        unfold phi. clear phi.
        repeat split.
        {
            apply wfp_update_svm_key.
            apply ϕ_in_context. 
        }
        {
            destruct ϕ_in_context.
            simpl in *.
            pose proof (pic_wf1 := pic_wf0).
            specialize (pic_wf1 (update_svm_key new_name old_name pc)).
            destruct pic_wf1 as [Hwfp [Hwfcex Hwfcmu]]. simpl in *.
            apply Hwfcex.
        }
        {
            destruct ϕ_in_context.
            apply wfcmu_update_svm_key.
            apply pic_wf0.
        }
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
                ) _ )
        |}
    .
    Next Obligation.
        (* This proof is very siimlar to the proof of
           the first obligation of [mlc_evar]
        *)
        intros. simpl in phi.
        remember (pc_svm pc !! name) as oidx.
        destruct oidx.
        2: {
            repeat split; reflexivity.
        }
        unfold phi. clear phi. simpl.
        repeat split; try reflexivity.
        destruct (decide (d < boundary_value (pc_svm pc))) as [y|n].
        { reflexivity. }
        unfold boundary_value in n.
        exfalso. apply n. clear n.
        destruct (decide (pc_svm pc = ∅)) as [y|n] eqn:Heq.
        {
            exfalso.
            rewrite y in Heqoidx.
            rewrite lookup_empty in Heqoidx.
            inversion Heqoidx.
        }
        rewrite Heq.
        destruct d as [|d].
        { lia. }
        cut (d < max_value 0 (pc_svm pc)).
        {
            intros ?. lia.
        }
        symmetry in Heqoidx.
        eapply max_value_in_leq with (name := name).
        apply Heqoidx.
    Qed.
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
                            ) _
                        )
                      end
                    end
        |}
    .
    Next Obligation.
        intros. simpl in *|-.
        destruct ϕ₁ as [fϕ₁ Hϕ₁].
        destruct ϕ₂ as [fϕ₂ Hϕ₂].
        cbn in *.
        pose proof (Hϕ₁pc := Hϕ₁ pc).
        pose proof (Hϕ₂pc := Hϕ₂ pc).
        naive_solver.
    Qed.
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
                        ) _ )
                      end
                    end
        |}
    .
    Next Obligation.
        intros. simpl in *|-.
        destruct ϕ₁ as [fϕ₁ Hϕ₁].
        destruct ϕ₂ as [fϕ₂ Hϕ₂].
        cbn in *.
        pose proof (Hϕ₁pc := Hϕ₁ pc).
        pose proof (Hϕ₂pc := Hϕ₂ pc).
        naive_solver.
    Qed.
    Next Obligation.
        intros.
        destruct args as [|a1 args].
        1: { simpl in *; lia. }
        destruct args as [|a2 args].
        1: { simpl in *; lia. }
        eexists. simpl. reflexivity.
    Qed.

    Lemma S_max_list (l : list nat) :
        S (max_list l) = match l with [] => 1 | _ => max_list (S <$> l) end
    .
    Proof.
        induction l; cbn.
        { reflexivity. }
        destruct l.
        { cbn. rewrite Nat.max_0_r. reflexivity. }
        rewrite Nat.succ_max_distr.
        rewrite IHl.
        reflexivity.
    Qed.

    Lemma map_fold_fmap
        (X : Type)
        (g: VarName -> nat -> X -> X)
        (gcom: forall j1 z1 j2 z2 y, g j1 z1 (g j2 z2 y) = g j2 z2 (g j1 z1 y))
        (f : nat -> nat)
        (m : gmap VarName nat)
        (x : X)
        : map_fold g x (f <$> m) = map_fold (fun vn n x => g vn (f n) x) x m
    .
    Proof.
        induction m using map_ind.
        {
            rewrite fmap_empty. rewrite 2!map_fold_empty. reflexivity.
        }
        {
            rewrite fmap_insert.
            rewrite map_fold_insert.
            {
                intros. apply gcom.
            }
            {
                rewrite lookup_fmap. rewrite H. reflexivity.
            }
            rewrite IHm.
            rewrite map_fold_insert.
            {
                intros. apply gcom.
            }
            { exact H. }
            reflexivity.
        }
    Qed.

    Instance pred_S_cancel : Cancel (=) Nat.pred S.
    Proof.
        intros x. simpl. reflexivity.
    Qed.

    Lemma map_fold_compose
        (X : Type)
        (g: VarName -> nat -> X -> X)
        (f finv : X -> X)
        {f_finv_cancel : Cancel (=) finv f}
        (gcom: forall j1 z1 j2 z2 y, g j1 z1 (g j2 z2 y) = g j2 z2 (g j1 z1 y))
        (fgcom: forall j1 z1 j2 z2 y, f (g j1 z1 ((g j2 z2 y))) = f (g j2 z2 ((g j1 z1 y))))
        (m : gmap VarName nat)
        (x : X)
        : f (map_fold g x m) = map_fold (fun vn n x => f (g vn n (finv x))) (f x) m
    .
    Proof.
        induction m using map_ind.
        {
            rewrite 2!map_fold_empty. reflexivity.
        }
        {
            rewrite map_fold_insert.
            {
                intros. apply gcom.
            }
            {
                exact H.
            }
            rewrite map_fold_insert.
            {
                intros.
                rewrite 2!cancel.
                rewrite fgcom.
                reflexivity.
            }
            { exact H. }
            rewrite -IHm.
            rewrite cancel.
            reflexivity.
        }
    Qed.

    Lemma max_helper_lemma v m:
    v `max` map_fold (λ (_ : VarName) (v0 r : nat), v0 `max` r) 0 m =
    v `max` map_fold (λ (_ : VarName) (v0 r : nat), v0 `max` r) v m.
    Proof.
        induction m using map_ind.
        {
            rewrite 2!map_fold_empty. lia.
        }
        {
            rewrite map_fold_insert.
            { intros. lia. }
            { exact H. }
            rewrite map_fold_insert.
            { intros. lia. }
            { exact H. }
            lia.
        }
    Qed.

    Lemma max_value_in_param
        (m : gmap VarName nat)
        (name : VarName)
        (v : nat)
        :
        m !! name = Some v ->
        max_value 0 m = max_value v m
    .
    Proof.
        move: name v.
        induction m using map_ind; intros name v H'.
        {
            rewrite lookup_empty in H'. inversion H'.
        }
        {
            unfold max_value in *.
            rewrite map_fold_insert.
            {
                intros. lia.
            }
            {
                exact H.
            }
            rewrite map_fold_insert.
            {
                intros. lia.
            }
            {
                exact H.
            }
            rewrite lookup_insert_Some in H'.
            destruct H' as [[H1 H2]|[H1 H2]].
            2: {
                specialize (IHm name v H2).
                rewrite IHm.
                reflexivity.
            }
            {
                subst.
                apply max_helper_lemma.
            }
        }
    Qed.

    Lemma boundary_value_incr_values m name:
        m !! name = None ->
        boundary_value (<[name:=0]>(incr_values m))
        = S (boundary_value m)
    .
    Proof.
        intros H.
        unfold boundary_value.
        repeat case_match; subst.
        {
            exfalso.
            unfold incr_values in e.
            pose proof (Hcontra := e).
            pose proof (Hcontra2 := insert_non_empty (incr_values ∅) name 0).
            contradiction.
        }
        {
            exfalso.
            pose proof (Hcontra := insert_non_empty (incr_values m) name 0).
            contradiction.
        }
        {
            unfold incr_values.
            rewrite fmap_empty.
            unfold max_value.
            rewrite map_fold_insert.
            { intros. lia. }
            { exact H. }
            {
                apply f_equal.
                rewrite map_fold_empty.
                reflexivity.
            }
        }
        apply f_equal.
        clear -H n0.
        
        move: name H n0.
        induction m using map_ind; intros name H' n0.
        { contradiction. }
        {
            specialize (IHm i H).
            destruct (decide (m = ∅)).
            {
                subst.
                clear IHm H n0.
                rewrite lookup_insert_None in H'.
                destruct H' as [_ Hiname].
                unfold incr_values.
                rewrite fmap_insert fmap_empty.
                unfold max_value.
                rewrite map_fold_insert.
                { intros. lia. }
                {
                    rewrite lookup_insert_None.
                    split;[|exact Hiname].
                    apply lookup_empty.
                }
                rewrite map_fold_insert.
                { intros. lia. }
                {
                    apply lookup_empty.
                }
                simpl.
                rewrite map_fold_insert.
                { intros. lia. }
                { apply lookup_empty. }
                rewrite map_fold_empty.
                lia.
            }
            {
                specialize (IHm n).
                unfold incr_values in *.
                rewrite fmap_insert.
                unfold max_value.
                rewrite lookup_insert_None in H'.
                destruct H' as [HmnNone Hiname].
                rewrite map_fold_insert.
                { intros. lia. }
                {
                    rewrite lookup_insert_None.
                    split;[|exact Hiname].
                    rewrite lookup_fmap.
                    rewrite HmnNone.
                    reflexivity.
                }
                simpl.
                rewrite map_fold_insert.
                { intros. lia. }
                {
                    rewrite lookup_fmap.
                    rewrite H.
                    reflexivity.
                }
                rewrite map_fold_insert.
                { intros. lia. }
                {
                    exact H.
                }
                unfold max_value in IHm.
                rewrite map_fold_insert in IHm.
                { intros. lia. }
                {
                    rewrite lookup_fmap.
                    rewrite H. reflexivity.
                }
                simpl in IHm.
                lia.
            }
        }
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
                                fun ctx : PContext =>
                                    let ctx' := pc_add_ename ctx name in
                                    let ϕ := pic_pic ϕ_in_context ctx' in
                                    (* TODO we need to rename [name] into some fresh name in ϕ
                                       if there is already [name] in the context*)
                                    patt_exists ϕ 
                            ) _ )
                        end
                    end
        |}
    .
    Next Obligation.
        intros. simpl in *|-.
        destruct ϕ_in_context as [fϕ Hϕ].
        cbn in *.
        pose proof (Hϕpc := Hϕ (pc_add_ename pc name)).
        clear phi.
        destruct Hϕpc as [H1 [H2 H3]].
        split_and!; try assumption.
        clear H1 H3.
        simpl in *.
        naive_solver.
    Qed.
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
                                fun ctx : PContext =>
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