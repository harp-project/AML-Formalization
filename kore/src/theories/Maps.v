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
    rewrite singleton_subseteq_l +
    rewrite fmap_propset_singleton
  ).

Ltac basic_simplify_krule :=
  eval_helper2;
  simpl sort_inj;
  repeat (rewrite_app_ext; try rewrite fmap_propset_singleton);
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
  | SortList
  | SortMap.

  (* We prove decidable equality and finiteness of the type above. *)
  Instance DemoSorts_eq_dec : EqDecision DemoSorts.
  Proof. solve_decision. Defined.
  Program Instance DemoSorts_finite : finite.Finite DemoSorts := {
    enum := [SortNat; SortBool; SortK; SortKItem; SortList; SortMap];
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
  | SymAppend
  | SymDotk
  | SymKseq
  | SymStopMap
  | SymChoiceMap
  | SymLookupMap
  | SymUpdateMap.

  (* We prove decidable equality and finiteness of the type above. *)
  Instance DemoSyms_eq_dec : EqDecision DemoSyms.
  Proof. solve_decision. Defined.
  Program Instance DemoSyms_finite : finite.Finite DemoSyms := {
    enum := [SymZero;SymSucc;SymAdd;SymTrue;
    SymFalse;SymIsList;SymNil;SymCons;SymInList;SymAppend;
    SymDotk;SymKseq;
    SymStopMap;SymChoiceMap;SymLookupMap;SymUpdateMap];
  }.
  Next Obligation. compute_done. Defined.
  Final Obligation. destruct x; set_solver. Defined.

  Inductive Demo_subsort : CRelationClasses.crelation DemoSorts :=
 (*  | kitem_is_top s : s ≠ SortK -> s ≠ SortKItem -> Demo_subsort s SortKItem *)
  | inj_nat_kitem : Demo_subsort SortNat SortKItem
  | inj_bool_kitem : Demo_subsort SortBool SortKItem
  | inj_list_kitem : Demo_subsort SortList SortKItem
  | inj_map_kitem : Demo_subsort SortMap SortKItem.

(*   Instance Demo_subsort_PreOrder : CRelationClasses.PreOrder Demo_subsort.
  Proof.
    split.
    (* cbv. intro. constructor 1.
    cbv. intros. inversion H; subst. assumption.
    inversion H0; subst. assumption. assumption.
    admit. *)
  Admitted.

  Instance Demo_subsort_PartialOrder : CRelationClasses.PartialOrder eq Demo_subsort.
  Proof.
    cbv. intros. split; intros. rewrite H. repeat constructor.
    destruct H. (*  inversion d; subst. reflexivity.
    inversion d0; subst; reflexivity.
    inversion d0. *)
  (* Defined. *)
  Admitted. *)

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
                 | SymDotk => []
                 | SymKseq => [SortKItem; SortK]
                 | SymStopMap => []
                 | SymChoiceMap => [SortMap]
                 | SymUpdateMap => [SortMap; SortKItem; SortKItem]
                 | SymLookupMap => [SortMap; SortKItem]
                 end;
      ret_sort := fun σ => match σ with
                           | SymZero | SymSucc | SymAdd => SortNat
                           | SymTrue | SymFalse => SortBool
                           | SymNil | SymCons | SymAppend => SortList
                           | SymInList | SymIsList => SortBool
                           | SymDotk | SymKseq => SortK
                           | SymStopMap => SortMap
                           | SymChoiceMap => SortKItem
                           | SymLookupMap => SortKItem
                           | SymUpdateMap => SortMap
                           end;
    |};
  |}.


 Definition map_funs : @Theory DemoSignature :=
   PropSet (λ pat,
    (exists R, pat = existT R (
      kore_exists SortMap (SymStopMap ⋅ ⟨⟩ =k{R} kore_bevar In_nil)
    ))
    \/
    (exists R, pat = existT R (
      kore_exists SortMap (SymUpdateMap ⋅ ⟨kore_fevar "K0"; kore_fevar "K1"; kore_fevar "K2"⟩ =k{R} kore_bevar In_nil)
    ))
(*     \/
    (exists R, pat = existT R (
      kore_exists SortKItem (SymLookupMap ⋅ ⟨kore_fevar "K0"; kore_fevar "K1"⟩ =k{R} kore_bevar In_nil)
    )) *)
  ).

  Definition map_beh : @Theory DemoSignature :=
   PropSet (λ pat,
    (exists R, pat = existT R (
      SymLookupMap ⋅ ⟨SymUpdateMap ⋅ ⟨kore_fevar "K0"; kore_fevar "K1"; kore_fevar "K2"⟩; kore_fevar "K1"⟩ =k{R} kore_fevar "K2"
    ))).

  Inductive knat_carrier : Set :=
  | c_nat (n : nat)
  with kbool_carrier : Set :=
  | c_bool (b : bool)
  with klist_carrier : Set :=
  | c_nil
  | c_cons (x : kitem_carrier) (xs : klist_carrier)
  with k_carrier : Set  :=
  | c_dotk
  | c_kseq (x : kitem_carrier) (xs : k_carrier)
  with kmap_carrier : Set :=
  (* | c_map (x : gmap kitem_carrier kitem_carrier) -- This won't work due to the lack of EqDec *)
  | c_map (x : list (kitem_carrier * kitem_carrier))
  with kitem_carrier : Set :=
  | c_nat_kitem (n : knat_carrier)
  | c_bool_kitem (b : kbool_carrier)
  | c_list_kitem (l : klist_carrier)
  | c_map_kitem (m : kmap_carrier).


  (* Scheme Boolean Equality for knat_carrier. (* DANGER! *)
  Print kmap_carrier_beq. *)
  Definition knat_carrier_beq (k1 k2 : knat_carrier) : bool :=
  match k1, k2 with
  | c_nat n1, c_nat n2 => Nat.eqb n1 n2
  end.
  Definition kbool_carrier_beq (k1 k2 : kbool_carrier) : bool :=
  match k1, k2 with
  | c_bool b1, c_bool b2 => Bool.eqb b1 b2
  end.

  Fixpoint klist_carrier_beq (k1 k2 : klist_carrier) : bool :=
  match k1, k2 with
  | c_nil, c_nil => true
  | c_cons x xs, c_cons y ys => kitem_carrier_beq x y &&
                                klist_carrier_beq xs ys
  | _, _ => false
  end
  with kmap_carrier_beq (k1 k2 : kmap_carrier) : bool :=
  match k1, k2 with
  | c_map m1, c_map m2 =>
    forallb (fun (x : kitem_carrier * kitem_carrier) =>
      match find (fun y => kitem_carrier_beq (fst x) (fst y) &&
                           kitem_carrier_beq (snd x) (snd y)) m2 with
      | None => false | _ => true end) m1
  end
  with kitem_carrier_beq (k1 k2 : kitem_carrier) : bool :=
  match k1, k2 with
  | c_nat_kitem n1, c_nat_kitem n2 => knat_carrier_beq n1 n2
  | c_bool_kitem n1, c_bool_kitem n2 => kbool_carrier_beq n1 n2
  | c_list_kitem n1, c_list_kitem n2 => klist_carrier_beq n1 n2
  | c_map_kitem n1, c_map_kitem n2 => kmap_carrier_beq n1 n2
  | _, _ => false
  end.

  Lemma forallb_impl :
    forall {A} (P Q : A -> bool),
      (forall a, P a = true -> Q a = true) ->
      forall l, forallb P l = true -> forallb Q l = true.
  Proof.
    induction l; simpl; auto.
    intros. destruct_andb!.
    apply H in H1.
    rewrite H1. rewrite IHl; auto.
  Qed.

  Lemma klist_carrier_beq_refl :
    forall k, klist_carrier_beq k k = true
  with kmap_carrier_beq_refl :
    forall k, kmap_carrier_beq k k = true
  with kitem_carrier_beq_refl :
    forall k, kitem_carrier_beq k k = true.
  Proof.
    * induction k.
      - by [].
      - simpl. by rewrite kitem_carrier_beq_refl IHk.
    * destruct k. simpl.
      induction x; simpl.
      - reflexivity.
      - destruct a; simpl in *.
        do 2 rewrite kitem_carrier_beq_refl. simpl.
        (* exfalso. apply f. *)
        eapply forallb_impl. 2: exact IHx.
        simpl. destruct a. intros.
        destruct (kitem_carrier_beq (k1, k2).1 k && kitem_carrier_beq (k1, k2).2 k0).
        reflexivity.
        assumption.
    * destruct k; simpl.
      - destruct n. simpl. by rewrite Nat.eqb_refl.
      - destruct b; simpl. by destruct b.
      - apply klist_carrier_beq_refl.
      - apply kmap_carrier_beq_refl.
  Qed.

(*   Inductive knat_carrier {K} {Keqdec : EqDecision K} {Kcount : Countable K} : Set :=
  | c_nat (n : nat)
  with kbool_carrier {K} {Keqdec : EqDecision K} {Kcount : Countable K} : Set :=
  | c_bool (b : bool)
  with klist_carrier {K} {Keqdec : EqDecision K} {Kcount : Countable K} : Set :=
  | c_nil
  | c_cons (x : kitem_carrier) (xs : klist_carrier)
  with k_carrier {K} {Keqdec : EqDecision K} {Kcount : Countable K} : Set  :=
  | c_dotk
  | c_kseq (x : kitem_carrier) (xs : k_carrier)
  with k_map_carrier {K} {Keqdec : EqDecision K} {Kcount : Countable K} : Set :=
  (* | c_map (x : gmap kitem_carrier kitem_carrier) -- This won't work due to the lack of EqDec *)
  | c_map (x : gmap K kitem_carrier)
  with kitem_carrier {K} {Keqdec : EqDecision K} {Kcount : Countable K} : Set :=
  | c_nat_kitem (n : knat_carrier)
  | c_bool_kitem (b : kbool_carrier)
  | c_list_kitem (l : klist_carrier).

  

  Scheme Boolean Equality for knat_carrier. (* DANGER! *) *)

  Definition carrier (s : DemoSorts) : Set :=
  match s with
   | SortNat => knat_carrier
   | SortBool => kbool_carrier
   | SortK => k_carrier
   | SortKItem => kitem_carrier
   | SortList => klist_carrier
   | SortMap => kmap_carrier
  end.

  Fixpoint klist_elem_of (y : kitem_carrier) (xs : klist_carrier) : kbool_carrier :=
  match xs with
  | c_nil => c_bool false
  | c_cons x xs => if kitem_carrier_beq x y
                   then c_bool true
                   else klist_elem_of y xs
  end.

  Fixpoint klist_app (xs ys : klist_carrier) : klist_carrier :=
  match xs with
  | c_nil => ys
  | c_cons x xs => c_cons x (klist_app xs ys)
  end.

  Definition klist_islist (xs : k_carrier) : kbool_carrier :=
  match xs with
   | c_kseq x c_dotk =>
     match x with
     | c_nat_kitem n => c_bool false
     | c_map_kitem n => c_bool false
     | c_bool_kitem b => c_bool false
     | c_list_kitem l => c_bool true
     end
   | _ => c_bool false
  end.

  (* For simplicity, update in just ::, lookup looks for the first occurence *)
  Definition kmap_update (m : kmap_carrier) (k : kitem_carrier) (v : kitem_carrier) : kmap_carrier :=
  match m with
  | c_map m => c_map ((k, v) :: m)
  end.

  Definition kmap_lookup (m : kmap_carrier) (k : kitem_carrier) : option kitem_carrier :=
  match m with
  | c_map m =>
    snd <$> find (fun '(k', v') => kitem_carrier_beq k k') m
  end.

  Program Definition DemoModel : @Model DemoSignature :=
    mkModel_partial
    carrier
    (fun σ =>
        match σ with
        | SymZero => Some (c_nat 0)
        | SymSucc => fun n => Some
                       match n with
                       | c_nat m => c_nat (S m)
                       end
        | SymAdd => fun n m => Some
                      match n, m with
                      | c_nat n, c_nat m => c_nat (n + m)
                      end
        | SymTrue => Some (c_bool true)
        | SymFalse => Some (c_bool false)
        | SymIsList => fun x => Some (klist_islist x)
        | SymNil => Some c_nil
        | SymCons => fun x y => Some (c_cons x y)
        | SymInList => fun x y => Some (klist_elem_of x y)
        | SymAppend => fun x y => Some (klist_app x y)
        | SymDotk => Some c_dotk
        | SymKseq => fun x y => Some (c_kseq x y)
        | SymStopMap => Some (c_map [])
        | SymUpdateMap => fun x y z => Some (kmap_update x y z)
        | SymLookupMap => fun x y => kmap_lookup x y
        | SymChoiceMap => fun m => 
                            match m with
                            | c_map [] => None
                            | c_map ((k, _v) :: _ms) => Some k
                            end
        end
      )
    (ltac:(destruct s; repeat constructor))
    _
    .
  Final Obligation.
    destruct s1, s2; simpl; intros H x; inversion H; subst.
    * exact (c_nat_kitem x).
    * exact (c_bool_kitem x).
    * exact (c_list_kitem x).
    * exact (c_map_kitem x).
  Defined.

  Set Transparent Obligations.
  Program Definition test : @Theory DemoSignature := PropSet (λ pat,
    (* 0 ∈ [1; 0] *)
    (exists R, pat = existT R (SymTrue ⋅ ⟨ ⟩ =k{R} (let zero := SymZero ⋅ ⟨ ⟩ in let zero_i := kore_inj _ _ zero in kore_app SymInList ⟨ zero_i ; (SymCons ⋅ ⟨ (kore_inj _ _ (SymSucc ⋅ ⟨ zero ⟩)) ; SymCons ⋅ ⟨ zero_i ; SymNil ⋅ ⟨ ⟩ ⟩ ⟩) ⟩))) \/
    (* [] ++ x = x *)
    (exists R, pat = existT R (SymAppend ⋅ ⟨ SymNil ⋅ ⟨ ⟩ ; kore_fevar "x" ⟩ =k{R} kore_fevar "x")) \/
    (* x ++ [] = x *)
    (exists R, pat = existT R (SymAppend ⋅ ⟨ kore_fevar "x" ; SymNil ⋅ ⟨ ⟩ ⟩ =k{R} kore_fevar "x")
  ) \/
    (* isList (_ : K) = false if K <> kseq List dots *)
    (exists R, pat = existT R (
      (! ((∃k SortList, Top{R} and (kore_fevar "X0" ⊆k{R} SymKseq ⋅ ⟨kore_inj _ _ (kore_bevar In_nil); SymDotk ⋅⟨⟩⟩) and Top{R}) or ⊥{R})
        and
        (Top{R} and @kore_fevar _ _ _ SortK "X0" ⊆k{R} kore_fevar "K" and Top{R})
      )
      --->ₖ
      (SymIsList ⋅ ⟨kore_fevar "K"⟩ =k{R} (SymFalse ⋅ ⟨⟩ and Top{SortBool}))
    ))
  ).
  Solve Obligations with (constructor).

  Goal satT test DemoModel.
  Proof.
    unfold satT, satM, test. intros.
    unfold test_obligation_1, test_obligation_2, test_obligation_3 in *.
    (* Generate a goal for each axiom: *)
    unfold_elem_of; destruct_or?; destruct_ex?; subst; cbn.
    * by simplify_krule.
(*    Step-by-step simplification would look like this:
      rewrite eval_simpl.
      apply propset_top_elem_of_2;
      intro;
      apply elem_of_PropSet.
      rewrite (@eval_app_simpl DemoSignature _ _ _ SymTrue).
      simpl.
      rewrite_app_ext.
      simpl.
      rewrite (@eval_app_simpl DemoSignature _ _ _ SymInList).
      simpl.
      rewrite eval_simpl. simpl.
      rewrite (@eval_app_simpl DemoSignature _ _ _ SymZero).
      simpl hmap.
      rewrite_app_ext. rewrite fmap_propset_singleton.
      unfold test_obligation_2, test_obligation_1.
      rewrite (@eval_app_simpl DemoSignature _ _ _ SymCons).
      simpl hmap.
      rewrite eval_simpl. simpl.
      rewrite (@eval_app_simpl DemoSignature _ _ _ SymSucc).
      simpl hmap.
      rewrite (@eval_app_simpl DemoSignature _ _ _ SymZero).
      simpl hmap.
      rewrite_app_ext. rewrite_app_ext.
      rewrite fmap_propset_singleton.
      rewrite (@eval_app_simpl DemoSignature _ _ _ SymCons).
      simpl hmap.
      rewrite eval_simpl. simpl.
      rewrite (@eval_app_simpl DemoSignature _ _ _ SymZero).
      simpl hmap.
      rewrite_app_ext.
      rewrite fmap_propset_singleton.
      rewrite (@eval_app_simpl DemoSignature _ _ _ SymNil).
      simpl hmap.
      rewrite_app_ext.
      rewrite_app_ext.
      rewrite_app_ext.
      rewrite_app_ext.
      reflexivity. *)
    * by simplify_krule.
    * simplify_krule.
      (* NOTE This is a simplification rule, therefore, we have
         to show it by induction. *)
      { remember (evar_valuation _ _) as l. clear.
        induction l. by simpl.
        simpl. by rewrite IHl. }
    * simplify_krule. remember (fresh_evar _ _) as F.
      simpl bevar_subst. cbn.
      do 2 abstract_var.
      destruct (klist_islist _) eqn:P; destruct b.
      2: by right.
      left. intros []. subst var var0.
      apply H. clear H.
      destruct (evar_valuation ρ "K"); simpl in *; try congruence.
      destruct c; simpl in *; try congruence.
      destruct x0; simpl in *; try congruence.
      exists l. basic_simplify_krule.
      apply elem_of_PropSet. apply singleton_subseteq.
      rewrite decide_eq_same.
      rewrite update_evar_val_diff_sort. congruence.
      by rewrite H0.
  Qed.

  Goal satT map_beh DemoModel.
  Proof.
    unfold satT, satM, test. intros.
    (* Generate a goal for each axiom: *)
    unfold_elem_of; destruct_or?; destruct_ex?; subst; cbn.
    simplify_krule.
    (* proof *)
    do 3 abstract_var.
    unfold kmap_update.
    destruct var. simpl.
    case_match; simpl. reflexivity.
    by rewrite (kitem_carrier_beq_refl) in H.
  Qed.

  Goal satT map_funs DemoModel.
  Proof.
    unfold satT, satM, test. intros.
    (* Generate a goal for each axiom: *)
    unfold_elem_of; destruct_or?; destruct_ex?; subst; cbn.
    * solve_functional_axiom_option.
      cbn. clear. repeat dependent destruction l. congruence.
    * solve_functional_axiom_option.
      cbn. clear. repeat dependent destruction l. congruence.
  Qed.

