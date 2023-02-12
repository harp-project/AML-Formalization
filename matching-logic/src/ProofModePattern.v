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

Definition bound_value (m : gmap VarName nat) : nat :=
    S (max_value 0 m)
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
        well_formed_closed_ex_aux phi (bound_value (pc_evm pc)) /\
        well_formed_closed_mu_aux phi (bound_value (pc_svm pc)) ;
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
        destruct (decide (d < bound_value (pc_evm pc))) as [y|n].
        { reflexivity. }
        unfold bound_value in n.
        exfalso. apply n. clear n.
        remember (elements (map_to_set _ _)) as l'.
        destruct d as [|d].
        { lia. }
        cut (d < max_list l').
        {
            intros ?. lia.
        }
        apply max_list_elem_of_le.
        rewrite Heql'. clear Heql'.
        rewrite elem_of_elements.
        rewrite elem_of_map_to_set.
        exists name. exists (S d). rewrite Heqoidx.
        split; reflexivity.
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


    Lemma boud_value_update_key new_name old_name store:
         bound_value (update_key new_name old_name store)
         = bound_value store
    .
    Proof.
        unfold bound_value.
        apply f_equal.
        unfold update_key.
        rewrite max_value_kmap.
        unfold update_key.
        apply leibniz_equiv.
        apply set_equiv_subseteq.
        do 2 rewrite elem_of_subseteq.
        setoid_rewrite elem_of_map_to_set.
        unfold kmap, renaming_function, prod_map. simpl.
        split; intros x [name [i [Hi1 Hi2]]]; subst.
        {
            Search fmap map_to_list.
            Search list_to_map fmap.
            Search lookup list_to_map.
            Set Printing All.
            rewrite lookup_fmap in Hi1.
            unfold prod_map in Hi1.
            apply elem_of_list_lookup_2 in Hi1.
            rewrite -elem_of_list_to_map' in Hi1.
            {
                intros x'.
                Search elem_of prod_map.
                rewrite elem_of_prod_map.
            }
            Search list_to_map lookup.
            simpl in Hi1.
            eexists. exists x.
            split;[|reflexivity].
            p
            [
            rewrite list_to_map_fmap in Hi1.
            Search list_to_map prod_map.
            Search kmap lookup.
        }
        2: {

        }
        Search equiv subseteq.
        unfold map_to_set.
        rewrite equiv_iff_subseteq.
        Search list_to_set equiv.
        Print dom.
        rewrite dom_kmap.
        Search map_to_set kmap.
    Qed.


    Lemma wfc_update_evm_key ϕic new_name old_name pc:
        well_formed_closed_ex_aux (pic_pic ϕic pc) (bound_value (pc_evm pc)) = true ->
        well_formed_closed_ex_aux
            (pic_pic ϕic (update_evm_key new_name old_name pc))
            (bound_value (pc_evm pc)) = true
    .
    Proof.
        intros H.
        destruct ϕic as [pic0 wf0]. simpl in *.
        specialize (wf0 ((update_evm_key new_name old_name pc))).
        destruct wf0 as [_ [Hwfcex _]].
        cbn in *.
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
            apply ϕ_in_context.
        }
        unfold update_evm_key. simpl.
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
        destruct (decide (d < bound_value (pc_svm pc))) as [y|n].
        { reflexivity. }
        unfold bound_value in n.
        exfalso. apply n. clear n.
        remember (elements (map_to_set _ _)) as l'.
        destruct d as [|d].
        { lia. }
        cut (d < max_list l').
        {
            intros ?. lia.
        }
        apply max_list_elem_of_le.
        rewrite Heql'. clear Heql'.
        rewrite elem_of_elements.
        rewrite elem_of_map_to_set.
        exists name. exists (S d). rewrite Heqoidx.
        split; reflexivity.
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

    Lemma bound_value_incr_values pc name:
        bound_value (<[name:=0]>(incr_values (pc_evm pc)))
        = S (bound_value (pc_evm pc))
    .
    Proof.
        unfold bound_value. apply f_equal.
        unfold incr_values.
        destruct pc as [pc_evm0 pc_svm0]. simpl.
        remember (fun _ y => y) as f.
        rewrite map_to_set_insert.
        rewrite S_max_list.
        unfold fmap.
        rewrite -fmap_insert.
        rewrite -list_fmap_insert.
        Search insert fmap.
        remember (elements (map_to_set _ _ _)).
        Search max_list.
    Abort.

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