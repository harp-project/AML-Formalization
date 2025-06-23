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

(**
   Metatheoretical implementation of machine integers and their functions
   since they are hooked. This is a type theoretical approximation of how
   the native integers might work.
 *)
Module MInt.

  From stdpp.bitvector Require Import bitvector.

  Definition MInt : N -> Set := bv.
  Definition MInt_nondep : Set := bvn.

  Check MInt 3.
  Check BV 3 5.
  Check 5%bv : MInt 3.

  Definition bitwidth {n : N} (_ : MInt n) : N := n.

  Compute bitwidth 5%bv.
  Compute bitwidth (BV 3 5).

  Definition uvalue {n : N} : MInt n -> Z := bv_unsigned.
  Definition svalue {n : N} : MInt n -> Z := bv_signed.

  Goal let x := BV 3 7 in uvalue x = 7%Z /\ svalue x = (-1)%Z.
  Proof. auto. Qed.

  (**
     I'm not sure how exactly the hooked version of this works. Z_to_bv
     wraps its argument.
   *)
  Definition integer {n : N} : Z -> MInt n := Z_to_bv n.

  (**
     Z_to_bv is opaque, which might cause problems later. For proofs, helper
     lemmas such as bv_eq might be necessary. There is also bv_simplify and
     bv_solve.
   *)
  (* Transparent Z_to_bv. *)
  Goal @integer 3 10 = 2%bv.
  Proof. cbv. apply bv_eq. reflexivity. Restart.
  cbv. bv_simplify. reflexivity. Qed.

  (**
     The first check might not be desired, I don't know what the hooked
     definition does. I made it easy to comment out.
   *)
  Definition eqb {n m : N} (x : MInt n) (y : MInt m) : bool :=
    N.eqb n m &&
    Z.eqb (uvalue x) (uvalue y).

  Definition eqb_nondep (x y : MInt_nondep) : bool :=
    match (x, y) with
    | (bv_to_bvn x, bv_to_bvn y) => eqb x y
    end.

  (**
     There is a myriad of operations on bv in this module. I didn't rename
     all of them, copy them when needed.
   *)
  (* Search _ in definitions. *)

End MInt.

Module T.

  (* We have two sorts: natural numbers and bools *)
  Inductive DemoSorts :=
  | SortNat
  | SortBool
  | SortK
  | SortKItem
  | SortList
  | SortMInt (n : nat).

  (**
     These types are no longer finite, but it is still countable, which may
     be proven via isomorphism with a sum type made up of the constructor
     arguments. If this type ever becomes recursive, we may need gentree
     from stdpp. This requires a lot of boilerplate code, but importantly,
     it can looks to be easy to generate.
   *)
  Definition DemoSorts_base : Set :=
    () + () + () + () + () + nat.

  (* We prove decidable equality and finiteness of the type above. *)
  Instance DemoSorts_eq_dec : EqDecision DemoSorts.
  Proof. solve_decision. Defined.
  (* Program Instance DemoSorts_finite : finite.Finite DemoSorts := { *)
  (*   enum := [SortNat; SortBool; SortK; SortKItem; SortList; SortMInt]; *)
  (* }. *)
  (* Next Obligation. compute_done. Defined. *)
  (* Final Obligation. destruct x; set_solver. Defined. *)

  Instance DemoSorts_countable : Countable DemoSorts.
  Proof.
    unshelve refine (inj_countable' (A := DemoSorts_base) _ _ _).
    refine (λ x, match x with
                  | SortNat    => inl (inl (inl (inl (inl ()))))
                  | SortBool   => inl (inl (inl (inl (inr ()))))
                  | SortK      => inl (inl (inl (inr ())))
                  | SortKItem  => inl (inl (inr ()))
                  | SortList   => inl (inr ())
                  | SortMInt n => inr n
                  end
    ).
    refine (λ x, match x with
                  | inl (inl (inl (inl (inl ())))) => SortNat
                  | inl (inl (inl (inl (inr ())))) => SortBool
                  | inl (inl (inl (inr ())))       => SortK
                  | inl (inl (inr ()))             => SortKItem
                  | inl (inr ())                   => SortList
                  | inr n                          => SortMInt n
                  end
    ).
    intros []; simpl; reflexivity.
  Defined.

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
  | SymBitwidthMInt (n : nat).

  Definition DemoSyms_base : Type :=
    () + () + () + () + () + () + () + () + () + () + () + () + nat.

  (* We prove decidable equality and finiteness of the type above. *)
  Instance DemoSyms_eq_dec : EqDecision DemoSyms.
  Proof. solve_decision. Defined.
  (* Program Instance DemoSyms_finite : finite.Finite DemoSyms := { *)
  (*   enum := [SymZero;SymSucc;SymAdd;SymTrue; *)
  (*   SymFalse;SymIsList;SymNil;SymCons;SymInList;SymAppend; *)
  (*   SymDotk;SymKseq;SymBitwidthMInt]; *)
  (* }. *)
  (* Next Obligation. compute_done. Defined. *)
  (* Final Obligation. destruct x; set_solver. Defined. *)
  Instance DemoSyms_countable : Countable DemoSyms.
  Proof.
    unshelve refine (inj_countable' (A := DemoSyms_base) _ _ _).
    refine (λ x, match x with
                  | SymZero           => inl (inl (inl (inl (inl (inl (inl (inl (inl (inl (inl (inl ())))))))))))
                  | SymSucc           => inl (inl (inl (inl (inl (inl (inl (inl (inl (inl (inl (inr ())))))))))))
                  | SymAdd            => inl (inl (inl (inl (inl (inl (inl (inl (inl (inl (inr ()))))))))))
                  | SymTrue           => inl (inl (inl (inl (inl (inl (inl (inl (inl (inr ())))))))))
                  | SymFalse          => inl (inl (inl (inl (inl (inl (inl (inl (inr ()))))))))
                  | SymIsList         => inl (inl (inl (inl (inl (inl (inl (inr ())))))))
                  | SymNil            => inl (inl (inl (inl (inl (inl (inr ()))))))
                  | SymCons           => inl (inl (inl (inl (inl (inr ())))))
                  | SymInList         => inl (inl (inl (inl (inr ()))))
                  | SymAppend         => inl (inl (inl (inr ())))
                  | SymDotk           => inl (inl (inr ()))
                  | SymKseq           => inl (inr ())
                  | SymBitwidthMInt n => inr n
                  end
    ).
    refine (λ x, match x with
                  | inl (inl (inl (inl (inl (inl (inl (inl (inl (inl (inl (inl ()))))))))))) => SymZero
                  | inl (inl (inl (inl (inl (inl (inl (inl (inl (inl (inl (inr ()))))))))))) => SymSucc
                  | inl (inl (inl (inl (inl (inl (inl (inl (inl (inl (inr ()))))))))))       => SymAdd
                  | inl (inl (inl (inl (inl (inl (inl (inl (inl (inr ())))))))))             => SymTrue
                  | inl (inl (inl (inl (inl (inl (inl (inl (inr ()))))))))                   => SymFalse
                  | inl (inl (inl (inl (inl (inl (inl (inr ())))))))                         => SymIsList
                  | inl (inl (inl (inl (inl (inl (inr ()))))))                               => SymNil
                  | inl (inl (inl (inl (inl (inr ())))))                                     => SymCons
                  | inl (inl (inl (inl (inr ()))))                                           => SymInList
                  | inl (inl (inl (inr ())))                                                 => SymAppend
                  | inl (inl (inr ()))                                                       => SymDotk
                  | inl (inr ())                                                             => SymKseq
                  | inr n                                                                    => SymBitwidthMInt n
                  end
    ).
    intros []; simpl; reflexivity.
  Defined.

  Inductive Demo_subsort : CRelationClasses.crelation DemoSorts :=
 (*  | kitem_is_top s : s ≠ SortK -> s ≠ SortKItem -> Demo_subsort s SortKItem *)
  | inj_nat_kitem : Demo_subsort SortNat SortKItem
  | inj_bool_kitem : Demo_subsort SortBool SortKItem
  | inj_list_kitem : Demo_subsort SortList SortKItem
  | inj_mint_kitem n : Demo_subsort (SortMInt n) SortKItem.

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
                 | SymBitwidthMInt n => [SortMInt n]
                 end;
      ret_sort := fun σ => match σ with
                           | SymZero | SymSucc | SymAdd | SymBitwidthMInt _ => SortNat
                           | SymTrue | SymFalse => SortBool
                           | SymNil | SymCons | SymAppend => SortList
                           | SymInList | SymIsList => SortBool
                           | SymDotk | SymKseq => SortK
                           end;
    |};
  |}.

(*   Inductive mynat := FromNat (n : nat) | FromBool (b : bool).
  Inductive kitem := KNat (n : mynat) | KBool (b : bool) | KList (l : list kitem).

  Definition carrier (s : DemoSorts) : Set :=
    match s with
    | SortNat => mynat
    | SortBool => bool
    | SortList => list kitem
    | SortKItem => kitem
    | SortK => unit
    end. *)

(*   Inductive carrier : DemoSorts -> Set := *)
  (* | c_nat (n : nat) : carrier SortNat *)
  (* | c_bool (b : bool) : carrier SortBool *)
  (* (1* | c_nil : carrier SortList *1) *)
  (* (1* | c_cons : carrier SortKItem -> carrier SortList -> carrier SortList *1) *)
  (* | c_list (l : list (carrier SortKItem)) : carrier SortList *)
  (* (1* | c_subsort (s1 s2 : DemoSorts) (P : subsort s1 s2) (x : carrier s1) : carrier s2 *1) *)
  (* (1* This should match the subsort relation *1) *)
  (* | c_kitem {A} : A ≠ SortK -> A ≠ SortKItem -> carrier A -> carrier SortKItem *)
  (* | c_boolnat : carrier SortBool -> carrier SortNat *)
  (* | c_dotk : carrier SortK. *)

  (* Check c_nat 1. *)
  (* Check c_nil. *)
  (* Check c_cons (c_kitem (eq_ind SortNat (λ x, if x is SortNat then True else False) I _) (c_nat 1)) c_nil. *)
  (* Check c_cons (c_nat 1) (c_cons (c_bool false) c_nil). *)
  (* Check c_cons (c_nat 1) (c_cons (c_bool false) (c_cons (c_cons (c_nat 1) c_nil) c_nil)). *)

  Lemma neqs_eq {A} {a b : A} (p q : a ≠ b) : p = q.
  Proof.
    apply functional_extensionality. intros. destruct (p x).
  Defined.

  (* Lemma subsort_unique {s1 s2} (p1 p2 : Demo_subsort s1 s2) : p1 = p2. *)
  (* Proof. *)
  (*   dependent induction p1; dependent destruction p2. *)
  (*   reflexivity. *)
  (*   destruct n0. reflexivity. *)
  (*   destruct n0. reflexivity. *)
  (*   f_equal; apply neqs_eq. *)
  (* Defined. *)

  (* Instance carrier_eqdec A : EqDecision (carrier A). *)
  (* Proof. *)
  (*   unfold EqDecision, Decision. *)
  (*   (1* No induction principle if the type appears in another *1) *)
  (*   (1* type (list here). As usual... *1) *)
  (*   revert A. fix IH 2. *)
  (*   intros. *)
  (*   dependent destruction x; dependent destruction y; try ((right; discriminate) + (left; reflexivity)). *)
  (*   * destruct (decide (n = n0)) as [-> | ?]; [left; reflexivity | right; congruence]. *)
  (*   * destruct (decide (b = b0)) as [-> | ?]; [left; reflexivity | right; congruence]. *)
  (*   * pose proof @list_eq_dec _ (IH SortKItem) l l0 as [-> | ?]; [left; reflexivity | right; congruence]. *)
  (*     Guarded. *)
  (*   * destruct (decide (s0 = s1)) as [-> | ?]. *)
  (*     - destruct (IH _ x y) as [-> | ?]. *)
  (*       + rewrite (subsort_unique P P0); by left. *)
  (*       + right. intro. inversion H. inversion_sigma H2. *)
  (*         rewrite <- Eqdep.EqdepTheory.eq_rect_eq in H2_0. *)
  (*         congruence. *)
  (*     - right. intro. inversion H. congruence. *)
  (* Qed. *)

  Definition inb {A} {_ : EqDecision A} (x : A) (xs : list A) : bool.
  Proof.
    induction xs. exact false.
    exact (if decide (x = a) then true else false).
  Defined.

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
  with kitem_carrier : Set :=
  | c_nat_kitem (n : knat_carrier)
  | c_bool_kitem (b : kbool_carrier)
  | c_list_kitem (l : klist_carrier)
  | c_mint_kitem (n : nat) (x : kmint_carrier n)
  with kmint_carrier : nat -> Set :=
  | c_mint (n : nat) (x : MInt.MInt (N.of_nat n)) : kmint_carrier n.
  (* | c_mint (x : MInt.MInt_nondep) : kmint_carrier (N.to_nat (definitions.bvn_n x)). *)

  (**
     I don't fully know what this line does and why it's dangerous, but for
     me it just doesn't work so I tried to recreate it. I hope I did
     everything right. As stated above, I'm not entirely sure how MInts are
     supposed to be compared, change the code above if it's wrong.
   *)
  (* Scheme Boolean Equality for knat_carrier. (1* DANGER! *1) *)

  Fixpoint knat_carrier_beq (x y : knat_carrier) : bool :=
    match x, y with
    | c_nat x, c_nat y => Nat.eqb x y
    end
  with kbool_carrier_beq (x y : kbool_carrier) : bool :=
    match x, y with
    | c_bool x, c_bool y => eqb x y
    end
  with klist_carrier_beq (x y : klist_carrier) : bool :=
    match x, y with
    | c_nil, c_nil => true
    | c_cons x xs, c_cons y ys => kitem_carrier_beq x y && klist_carrier_beq xs ys
    | _, _ => false
    end
  with k_carrier_beq (x y : k_carrier) : bool :=
    match x, y with
    | c_dotk, c_dotk => true
    | c_kseq x xs, c_kseq y ys => kitem_carrier_beq x y && k_carrier_beq xs ys
    | _, _ => false
    end
  with kitem_carrier_beq (x y : kitem_carrier) : bool :=
    match x, y with
    |  c_nat_kitem x,  c_nat_kitem y =>  knat_carrier_beq x y
    | c_bool_kitem x, c_bool_kitem y => kbool_carrier_beq x y
    | c_list_kitem x, c_list_kitem y => klist_carrier_beq x y
    | c_mint_kitem n x, c_mint_kitem m y => kmint_carrier_beq n m x y
    | _, _ => false
    end
  with kmint_carrier_beq (n m : nat) (x : kmint_carrier n) (y : kmint_carrier m) : bool :=
    match x, y with
    | c_mint _ x, c_mint _ y => MInt.eqb x y
    end.

  Definition carrier (s : DemoSorts) : Set :=
  match s with
   | SortNat => knat_carrier
   | SortBool => kbool_carrier
   | SortK => k_carrier
   | SortKItem => kitem_carrier
   | SortList => klist_carrier
   | SortMInt n => kmint_carrier n
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
     | c_bool_kitem b => c_bool false
     | c_list_kitem l => c_bool true
     (* I hope this is right. Why not use | _ => c_bool false? *)
     | c_mint_kitem _ _ => c_bool false
     end
   | _ => c_bool false
  end.

  Program Definition DemoModel : @Model DemoSignature := mkModel_singleton
    carrier
    (fun σ =>
        match σ with
        | SymZero => c_nat 0
        | SymSucc => fun n =>
                       match n with
                       | c_nat m => c_nat (S m)
                       end
        | SymAdd => fun n m =>
                      match n, m with
                      | c_nat n, c_nat m => c_nat (n + m)
                      end
        | SymTrue => c_bool true
        | SymFalse => c_bool false
        | SymIsList => klist_islist
        | SymNil => c_nil
        | SymCons => c_cons
        | SymInList => klist_elem_of
        | SymAppend => klist_app
        | SymDotk => c_dotk
        | SymKseq => c_kseq
        (**
           There are several choices to make here, so I won't add all of
           them as a comment:
           - this
           - just return the ignored parmeter in this instead -> might not
             be good for generation
           - with the nondep representation, we need a different
             bitwidth_nondep function
           - for ALL of the above: make the MInt module do the conversion
             to nat -> might be best for generation
         *)
        | SymBitwidthMInt _ => fun '(c_mint _ x) => c_nat (N.to_nat (MInt.bitwidth x))
        end
      )
    _
    _.
  Next Obligation.
    (* Important change here to accomodate dependent types! *)
    destruct s; repeat unshelve econstructor.
    (* Now this doesn't solve. *)
  Fail Defined.
  Admitted.
  Final Obligation.
    destruct s1, s2; simpl; intros H x; inversion H; subst.
    * exact (c_nat_kitem x).
    * exact (c_bool_kitem x).
    * exact (c_list_kitem x).
    * exact (c_mint_kitem n x).
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
