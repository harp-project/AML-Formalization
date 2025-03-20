From Equations Require Import Equations.
From Kore Require Export Substitution
                         Freshness
                         Basics.
Require Import Coq.Program.Equality.



Section Semantics.
  Context {Σ : Signature}.

  Record OPMLModel := {
    carrier :> sort -> Set;
    app (σ : symbol) :
       @hlist _ carrier (arg_sorts σ) -> propset (carrier (ret_sort σ));
    inhabited (s : sort) : Inhabited (carrier s)
  }.

  Section with_model.

  Context {M : OPMLModel}.
  Record Valuation : Type := {
    evar_valuation (x : evar) : carrier M (evar_sort x);
    svar_valuation (X : svar) : propset (carrier M (svar_sort X)) ;
  }.

  Definition app_ext
    (σ : symbol)
    (args : @hlist _ (fun s => propset (carrier M s)) (arg_sorts σ))
    : propset (carrier M (ret_sort σ)) :=
  PropSet (
    fun e => exists (l : @hlist _ (carrier M) (arg_sorts σ)),
      pointwise_elem_of _ l args /\ e ∈ app M σ l
  ).

  Fixpoint map_to_hlist {A} (F : A -> Type) (f : forall (a : A), F a) (l : list A) {struct l} : @hlist Type id (map F l) :=
    match l return @hlist _ _ (map F l) with
    | []    => hnil
    | x::xs => hcons (f x) (map_to_hlist F f xs)
    end.
  Print map_to_hlist.

  Fixpoint app_map (l : list Pattern)
    {ls}
    (pf : app_ws (well_sorted default default) l ls)
    (f : forall (φ :Pattern) {s}
         (pf : well_sorted default default s φ)
         (psize : pat_size φ < 1 + foldr (fun φ acc => pat_size φ + acc) 0 l), propset (carrier M s)) {struct l} :
    @hlist _ (fun x => propset (carrier M x)) ls
    .
  Proof.
    (* refine (
    match l return  -> @hlist _ (fun x => propset (carrier M x)) ls with
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

  Program Definition update_evar_val
    (ev : evar)
    (x : carrier M (evar_sort ev))
    (val : Valuation) : Valuation :=
    {|
    evar_valuation := fun ev' : evar => _;
      (* if decide (ev = ev')
      then x
      else evar_valuation val ev' ; *)
    svar_valuation := (svar_valuation val)
    |}.
  Next Obligation.
    intros ev H ρ ev'.
    destruct (decide (ev = ev')).
    * rewrite -e. exact H.
    * exact (evar_valuation ρ ev').
  Defined.

  Program Definition update_svar_val
    (sv : svar)
    (X : propset (carrier M (svar_sort sv)))
    (val : Valuation) : Valuation :=
    {|
    evar_valuation := (evar_valuation val);
    svar_valuation := fun sv' : svar =>
      if decide (sv = sv') is left _ then _ else svar_valuation val sv' ;
    |}.
  Next Obligation.
    intros.
    rewrite -wildcard'.
    exact X.
  Defined.

  (* Oké-e ha a nem well-sorted dolgoknak valami default értéket
     adjunk, és így elhagyjuk a well-sorted judgementet (Hws-t) *)
  Equations? eval (ρ : Valuation) (φ : Pattern) {s}
    (Hws : well_sorted default default s φ)
      : propset (carrier M s) by wf (pat_size φ) :=
    eval ρ (kore_fevar x) pf    := _ ;
    eval ρ (kore_fsvar X) pf    := _;
    eval ρ (kore_bevar x) pf    := ∅ ;
    eval ρ (kore_bsvar x) pf    := ∅ ;

    eval ρ (kore_app σ args) pf := _;

    eval ρ (kore_bot s0)   pf    := ∅ ;
    eval ρ (kore_top s0)   pf    := ⊤ ;
    eval ρ (kore_not φ)   pf    := (⊤ ∖ eval ρ φ _);
    eval ρ (kore_imp φ1 φ2)  pf := (⊤ ∖ eval ρ φ1 _) ∪ (eval ρ φ2 _);
    (* Dont use let in the following definition, because the missing proofs become harder! *)
    eval ρ (kore_iff φ1 φ2)  pf := (⊤ ∖ eval ρ φ1 _ ∪ eval ρ φ2 _) ∩
                                   (⊤ ∖ eval ρ φ2 _ ∪ eval ρ φ1 _);
    eval ρ (kore_and φ1 φ2)  pf := eval ρ φ1 _ ∩ eval ρ φ2 _;
    eval ρ (kore_or φ1 φ2)  pf := eval ρ φ1 _ ∪ eval ρ φ2 _;

    eval ρ (kore_exists s0 φ)    pf := _;
    eval ρ (kore_forall s0 φ)    pf := _;
    eval ρ (kore_mu s0 φ)    pf := _;
    eval ρ (kore_nu s0 φ)    pf := _;

    eval ρ (kore_ceil s1 s2 φ) pf := _;
    eval ρ (kore_floor s1 s2 φ) pf := _;
    eval ρ (kore_equals s1 s2 φ1 φ2) pf := _;
    eval ρ (kore_in s1 s2 φ1 φ2) pf := _;.
    Proof.
      * (* kore_fevar *)
        simpl in *.
        epose {[ evar_valuation ρ x ]} as d.
        exact d.
        Unshelve.
        destruct decide.
        - rewrite e. typeclasses eauto.
        - simpl in pf. congruence.
      * (* kore_fsvar *)
        simpl in *.
        epose (svar_valuation ρ X) as d.
        destruct decide.
        - rewrite <- e. exact d.
        - simpl in pf. congruence.
      * (* kore_app *)
        apply andb_split_1 in pf as pf1.
        apply andb_split_2 in pf as pf2.
        pose (app_ext σ (app_map args pf2 (eval ρ))) as X.
        destruct decide.
        rewrite e. exact X.
        inversion pf1.
      * (* kore_not *)
        by apply pf.
      * simpl. lia.
      * (* kore_and *)
        by apply andb_split_1 in pf.
      * simpl. lia.
      * by apply andb_split_2 in pf.
      * simpl. lia.
      * (* kore_or *)
        by apply andb_split_1 in pf.
      * simpl. lia.
      * by apply andb_split_2 in pf.
      * simpl. lia.
      * (* kore_imp *)
        by apply andb_split_1 in pf.
      * simpl. lia.
      * by apply andb_split_2 in pf.
      * simpl. lia.
      * (* kore_iff *)
        by apply andb_split_1 in pf.
      * simpl. lia.
      * by apply andb_split_2 in pf.
      * simpl. lia.
      * by apply andb_split_2 in pf.
      * simpl. lia.
      * by apply andb_split_1 in pf.
      * simpl. lia.
      * (* kore_exists *)
        simpl in *.
        eapply (propset_fa_union (
          fun c : carrier M s0 =>
            let newx := fresh_evar s0 φ in
            eval (update_evar_val (projT1 newx) _ ρ)
                      (bevar_subst (kore_fevar (projT1 newx)) 0 φ)
                      _ _ _
        )).
        Unshelve.
        - pose proof (projT2 newx) as Is. simpl in Is.
          destruct decide. 2: simpl in Is; congruence.
          rewrite e. exact c.
        - eapply (well_sorted_bevar_subst _ (kore_fevar (projT1 newx)) s s0 _ _ 0) in pf.
          3: reflexivity.
          2: { cbn. exact (projT2 newx). }
          clear -pf.
          assert (update 0 None (shift default (Some s0)) = default). {
            unfold update, shift.
            extensionality x. destruct x; simpl.
            reflexivity.
            reflexivity.
          }
          rewrite H in pf.
          exact pf.
        - rewrite bevar_subst_size. lia.
      * (* kore_forall *)
        simpl in *.
        eapply (propset_fa_intersection (
          fun c : carrier M s0 =>
            let newx := fresh_evar s0 φ in
            eval (update_evar_val (projT1 newx) _ ρ)
                      (bevar_subst (kore_fevar (projT1 newx)) 0 φ)
                      _ _ _
        )).
        Unshelve.
        - pose proof (projT2 newx) as Is. simpl in Is.
          destruct decide. 2: simpl in Is; congruence.
          rewrite e. exact c.
        - eapply (well_sorted_bevar_subst _ (kore_fevar (projT1 newx)) s s0 _ _ 0) in pf.
          3: reflexivity.
          2: { cbn. exact (projT2 newx). }
          clear -pf.
          assert (update 0 None (shift default (Some s0)) = default). {
            unfold update, shift.
            extensionality x. destruct x; simpl.
            reflexivity.
            reflexivity.
          }
          rewrite H in pf.
          exact pf.
        - rewrite bevar_subst_size. lia.
      * (* kore_mu *)
        exact ∅.
      * (* kore_nu *)
        exact ∅.
      * (* kore_eq *)
        apply andb_split_1 in pf as pf1.
        apply andb_split_1 in pf1 as pf0.
        apply andb_split_2 in pf1 as pf2. clear pf1.
        rename pf0 into pf1.
        apply andb_split_2 in pf as pf3. clear pf.
        destruct decide. 2: { simpl in *. congruence. }
        epose (X1 := eval ρ φ1 s1 pf1 _).
        epose (X2 := eval ρ φ2 s1 pf2 _).
        exact (PropSet (fun e => X1 = X2)).
        Unshelve.
        all: lia.
    Defined.
  Print eval.

  Definition satM φ s (ws : well_sorted default default s φ) :=
    forall ρ, eval ρ φ ws = ⊤.
  Definition Theory := propset Pattern.
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

  Fixpoint HForall {J} {A : J -> Type}
    (P : ∀ j, A j -> Prop)
    {js : list J} (v : @hlist J A js) {struct v} : Prop :=
    match v with
    | hnil => True
    | hcons x xs => P _ x ∧ HForall P xs
    end.

  Fixpoint HBiForall {J1 J2} {A1 : J1 -> Type} {A2 : J2 -> Type}
    (P : ∀ j1 j2, A1 j1 -> A2 j2 -> Prop)
    {js1 : list J1}
    {js2 : list J2}
    (v1 : @hlist J1 A1 js1) (v2 : @hlist J2 A2 js2)
      {struct v1} : Prop :=
    match v1, v2 with
    | hnil, hnil => True
    | hcons x xs, hcons y ys => P _ _ x y ∧ HBiForall P xs ys
    | _, _ => False
    end.

  Fixpoint hmap {J} {A B : J -> Type}
    (f : ∀ j, A j -> B j)
    {js : list J} (v : @hlist J A js) : @hlist J B js :=
  match v with
  | hnil => hnil
  | hcons x xs => hcons (f _ x) (hmap f xs)
  end.

End with_model.
End Semantics.