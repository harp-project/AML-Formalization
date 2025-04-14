From Equations Require Import Equations.
From Kore Require Export Substitution
                         Freshness
                         Basics.
Require Import Coq.Program.Equality.



Section Semantics.
  Context {Σ : Signature}.

  Record Model := {
    carrier :> sort -> Set;
    app (σ : symbol) :
       @hlist _ carrier (arg_sorts σ) -> propset (carrier (ret_sort σ));
    inhabited (s : sort) : Inhabited (carrier s)
  }.

  Section with_model.

  Context {M : Model}.
  Record Valuation : Type := {
    evar_valuation {s : sort} (x : evar s) : carrier M s;
    svar_valuation {s : sort} (X : svar s) : propset (carrier M s) ;
  }.

  Definition app_ext
    (σ : symbol)
    (args : @hlist _ (fun s => propset (carrier M s)) (arg_sorts σ))
    : propset (carrier M (ret_sort σ)) :=
  PropSet (
    fun e => exists (l : @hlist _ (carrier M) (arg_sorts σ)),
      pointwise_elem_of _ l args /\ e ∈ app M σ l
  ).


  Definition update_evar_val {s} (ev : evar s) (x : carrier M s) (val : Valuation) : Valuation.
  Proof.
    unshelve esplit.
    intros s' ev'.
    destruct (decide (s = s')).
    destruct (decide (eq_rect s evar ev _ e = ev')).
    exact (eq_rect s M x _ e).
    1,2:exact (evar_valuation val ev').
    exact (@svar_valuation val).
  Defined.

  Definition update_svar_val {s} (sv : svar s) (X : propset (carrier M s)) (val : Valuation) : Valuation.
  Proof.
    unshelve esplit.
    exact (@evar_valuation val).
    intros s' sv'.
    destruct (decide (s = s')).
    * destruct (decide (eq_rect s svar sv _ e = sv')).
      - rewrite e in X. exact X.
      - exact (svar_valuation val sv').
    * exact (svar_valuation val sv').
  Defined.

  Let OS s := PropsetOrderedSet (carrier M s).
  Let  L s := PowersetLattice (carrier M s).

  Equations? eval {ex mu} {s} (ρ : Valuation) (φ : Pattern ex mu s) : propset (carrier M s) by wf (pat_size φ) :=
    eval ρ (kore_bevar _) := empty ;
    eval ρ (kore_fevar x) := {[evar_valuation ρ x]} ;
    eval ρ (kore_bsvar _) := empty ;
    eval ρ (kore_fsvar X) := svar_valuation ρ X ;

    eval ρ (kore_app σ l) := app_ext σ _ (*@hlist_rect _ _ (λ l _, hlist (propset ∘ M) l) hnil (λ _ _ a _ b, hcons (eval ρ a) b) _ l*)
      (* (hmap (fun j (p : Pattern ex mu j) => eval ρ p) l) *) ;

    eval ρ kore_bot         := empty ;
    eval ρ kore_top         := ⊤ ;
    eval ρ (kore_not φ)     := ⊤ ∖ (eval ρ φ) ;
    eval ρ (kore_and φ1 φ2) := (eval ρ φ1) ∩ (eval ρ φ2) ;
    eval ρ (kore_or φ1 φ2)  := (eval ρ φ1) ∪ (eval ρ φ2) ;
    eval ρ (kore_imp φ1 φ2) := (⊤ ∖ (eval ρ φ1)) ∪ (eval ρ φ2) ;
    eval ρ (kore_iff φ1 φ2) := (⊤ ∖ eval ρ φ1 ∪ eval ρ φ2) ∩
                               (⊤ ∖ eval ρ φ2 ∪ eval ρ φ1) ;

    eval ρ (kore_exists s' φ) := (* ⊤ ≫= λ X, let o := fresh_evar s' φ in eval (update_evar_val o X ρ) (bevar_subst [] φ (kore_fevar o)) *)
      let x := fresh_evar s' φ in
        propset_fa_union (λ c,
           eval (update_evar_val x c ρ)
                (bevar_subst [] (kore_fevar x) φ)) ;
    eval ρ (kore_forall s' φ) :=
      let x := fresh_evar s' φ in
        propset_fa_intersection (λ c,
           eval (update_evar_val x c ρ)
                (bevar_subst [] (kore_fevar x) φ)) ;

(*@LeastFixpointOf _ OS L
                                  (fun S =>
                                    let ρ' := (update_svar_val X S ρ) in
                                    eval ρ' (ϕ'^{svar: 0 ↦ X})
                                  )*)

    eval ρ (kore_mu φ)     :=
      let X := fresh_svar s φ in
        @LeastFixpointOf _ (OS s) (L s) (fun S =>
          eval (update_svar_val X S ρ)
               (bsvar_subst [] (kore_fsvar X) φ)
        )
     ;
    eval ρ (kore_nu φ)     :=
      let X := fresh_svar s φ in
        @GreatestFixpointOf _ (OS s) (L s) (fun S =>
          eval (update_svar_val X S ρ)
               (bsvar_subst [] (kore_fsvar X) φ)
        );

    eval ρ (kore_ceil φ)       := PropSet (λ _, ∃ c, c ∈ eval ρ φ) ;
    eval ρ (kore_floor φ)      := PropSet (λ _, ∀ c, c ∈ eval ρ φ) ;
    eval ρ (kore_equals φ1 φ2) := PropSet (λ _, (eval ρ φ1) = (eval ρ φ2)) ;
    eval ρ (kore_in φ1 φ2)     := PropSet (λ _, (eval ρ φ1) ⊆ (eval ρ φ2)) ;
  .
  Proof.
    1: {
      simpl in *.
      induction l.
      * exact hnil.
      * apply hcons.
        - apply (eval _ _ _ ρ f). lia.
        - apply IHl. intros.
          apply (eval x0 x1 x2 x3 x4). lia.
    }
    all: try by simpl; lia.
    1-2: rewrite (bevar_subst_size [] ex mu s s' φ x); constructor.
    1-2: rewrite (bsvar_subst_size ex [] mu s s φ X); constructor.
  Defined.

  Lemma eval_app_simpl :
    forall {ex mu} (σ : symbol) (l : hlist (Pattern ex mu) (arg_sorts σ)) (ρ : Valuation),
      eval ρ (kore_app σ l) = app_ext σ (hmap (fun _ => eval ρ) l).
  Proof.
    intros.
    simp eval. f_equal.
    simpl in *. unfold eval_obligation_1. simpl. cbn.
    induction l.
    * reflexivity.
    * rewrite IHl. reflexivity.
  Defined.


(*   Fixpoint HForall {J} {A : J -> Type}
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
    end.*)

  Lemma app_ext_singleton
    {σ}
    {args : hlist (propset ∘ M) (arg_sorts σ)}
    (H : all_singleton args) :
      app_ext σ args = app M σ (all_singleton_extract H).
  Proof.
    apply set_eq. split; intros.
    unfold app_ext in H0.
    destruct H0 as [? []].
    replace (all_singleton_extract H) with x0. auto.
    clear x H1. induction args.
    simpl in *.
    apply destruct_hnil.
    simpl in H. destruct H. destruct s.
    simpl in c. simpl.
    epose proof destruct_hcons x0 as [[] ?]. rewrite y in H0.
    simpl in H0. destruct H0. rewrite c in H. inversion H.
    rewrite y. f_equal. apply IHargs. apply H0.
    apply elem_of_PropSet. exists (all_singleton_extract H).
    split. 2: auto. clear. induction args. simpl. split.
    simpl in H. destruct H. destruct s. simpl in c. subst.
    simpl. split. congruence.
    apply IHargs.
  Defined.

  Lemma all_singleton_var_list {l} (vars : hlist evar l) ρ:
    all_singleton (hmap (fun s (x : evar s) => {[evar_valuation ρ x]}) vars).
  Proof.
    induction vars; simpl.
    * exact tt.
    * apply pair. 2: exact IHvars.
      eapply existT. reflexivity.
  Defined.

  Corollary eval_app_var_list :
    forall ex mu (σ : symbol) (vars : hlist evar (arg_sorts σ)) (ρ : Valuation),
      eval ρ (kore_app σ (var_list ex mu vars)) =
        app M σ (all_singleton_extract (all_singleton_var_list vars ρ)).
  Proof.
    intros. rewrite eval_app_simpl.
    rewrite <- app_ext_singleton.
    (* there is a slight difference in the arguments *)
    f_equal.
    induction vars; simpl.
    * reflexivity.
    * rewrite IHvars. reflexivity.
  Defined.

(*   Lemma functional_symbol_eval :
    forall (σ : symbol) (R : sort) (vars : hlist evar (arg_sorts σ)) (ρ : Valuation),
      eval ρ (functional_symbol σ R vars) =
        app M σ (all_singleton_extract (all_singleton_var_list vars ρ)).
  Proof.
    
  Defined. *)

(*   Lemma app_var_list_eval :
    forall ex mu (σ : symbol) (vars : hlist evar (arg_sorts σ)) (M : Model) (ρ : Valuation),
      eval ρ (kore_app σ (var_list ex mu vars)) =
      app_ext σ (hmap (fun s (x : evar s) => {[evar_valuation ρ x]}) vars). *)

End with_model.

  Definition satM {ex mu s} (φ : Pattern ex mu s) (M : Model) :=
    forall ρ, @eval M _ _ _ ρ φ = ⊤.
  Definition satT (Γ : Theory) (M : Model) :=
    forall p, p ∈ Γ -> @satM _ _ (projT1 p) (projT2 p) M.

  Program Definition mkModel
    (custom_carrier : sort → Set)
    (custom_app : forall (σ : symbol),
      foldr (λ c a, custom_carrier c -> a)
            (propset (custom_carrier (ret_sort σ)))
            (arg_sorts σ))
    (custom_inh : ∀ s : sort, Inhabited (custom_carrier s)) :
    Model :=
  {|
    carrier := custom_carrier;
    inhabited := custom_inh;
    app := fun σ => uncurry_n (custom_app σ)
  |}.

  Definition mkModel_singleton
    (custom_carrier : sort → Set)
    (custom_app : forall (σ : symbol), foldr (λ c a, custom_carrier c -> a) (custom_carrier (ret_sort σ)) (arg_sorts σ))
    (custom_inh : ∀ s : sort, Inhabited (custom_carrier s)) :
    Model :=
  {|
    carrier := custom_carrier;
    inhabited := custom_inh;
    app := fun σ => singleton ∘ uncurry_n (custom_app σ)
  |}.

  Lemma functional_symbol_is_functional :
    forall (σ : symbol) (R : sort) (vars : hlist evar (arg_sorts σ)),
      forall (M : Model),
        (exists (f : hlist M (arg_sorts σ) -> M (ret_sort σ)), app M σ = singleton ∘ f) ->
        satM (functional_symbol σ R vars) M.
  Proof.
    intros.
    unfold satM, functional_symbol. intros.
    simp eval. simpl.
    apply propset_fa_union_full. intro.
    cbn.
    setoid_rewrite eval_equation_19.
    remember (fresh_evar _ _) as x.
    assert (X : 
      hlist_rec sort (Pattern [ret_sort σ] [])
                   (λ (l : list sort) (_ : hlist 
                                             (Pattern [ret_sort σ] []) l),
                      hlist (Pattern [] []) l) ⟨ ⟩%hlist
                   (λ (x0 : sort) (xs : list sort) 
                      (H0 : Pattern [ret_sort σ] [] x0) 
                      (_ : hlist (Pattern [ret_sort σ] []) xs) 
                      (H1 : hlist (Pattern [] []) xs),
                      hcons (bevar_subst [] (kore_fevar x) H0) H1)
                   (arg_sorts σ) (var_list [ret_sort σ] [] vars) =
                     var_list [] [] vars
    ). {
      clear ρ t H M Heqx.
      induction vars; simpl.
      * reflexivity.
      * rewrite IHvars. reflexivity.
    }
    rewrite X.
    clear X.
    setoid_rewrite elem_of_PropSet.
    setoid_rewrite eval_app_var_list.
    simp eval.
    destruct H as [f H].
    rewrite H. cbn.
    setoid_rewrite eval_equation_3.
    unfold evar_valuation, update_evar_val at 2.
    rewrite decide_eq_same. simpl.
    rewrite decide_eq_same.
    (* c still appears on the lhs *)
    assert (x ∉ free_evars (ret_sort σ) (kore_app σ (var_list [ret_sort σ] [] vars))). {
      pose proof (fresh_evar_is_fresh (ret_sort σ) (kore_equals R (kore_app σ (var_list [ret_sort σ] [] vars))
       (kore_bevar In_nil))).
       subst x.
       simpl in *. set_solver.
    }
    clear -H0.
    cbn in H0.
    exists (f
      (all_singleton_extract
         (all_singleton_var_list vars ρ))).
    f_equal. f_equal.
    remember (f _) as c. clear f Heqc.
    revert ρ c.
    induction vars; intros; simpl in *.
    * reflexivity.
    * destruct decide; subst; simpl in *.
      - destruct decide.
        + subst. clear-H0. exfalso.
          set_solver.
        + f_equal.
          specialize (IHvars ltac:(set_solver)).
          by rewrite IHvars.
      - f_equal.
        specialize (IHvars ltac:(set_solver)).
        by rewrite IHvars.
  Qed.

End Semantics.

  Ltac unfold_elem_of :=
  match goal with
  | [H : _ ∈ _ |- _]  => destruct H
  end.

  Ltac destruct_evar_val :=
  match goal with
  | [ |- context [evar_valuation ?ρ ?x] ] =>
    let H := fresh "Val" in
      destruct (evar_valuation ρ x) eqn:H
  end.

  Ltac solve_dep_prods :=
    match goal with
    | [ |- ()] => exact tt
    | [ |- prod (sigT _) _] =>
      apply pair; [
        eapply existT; reflexivity
      |
        solve_dep_prods
      ]
    end.

  Ltac solve_all_singleton :=
  match goal with
  | [ |- all_singleton _] => cbn; solve_dep_prods
  end.

  (* This would be much more simple, if rewrite_stat innermost worked... *)
  Ltac rewrite_app_ext_innnermost G :=
  match G with
  | context [@app_ext _ ?M ?σ ?args] =>
    rewrite_app_ext_innnermost args (* This step is just to reach
                                        the innermost app_ext *)
    (* idtac "match" σ args *)
  | context [@app_ext _ ?M ?σ ?args] => (* This branch fails, if there is no
                                     more app_exts, therefore
                                     it succeeds for the last (innermost)
                                     app_ext *)
    (* idtac "last1" σ args; *)
    (* let H := fresh "H" in
    (* we explicitly rewrite: *)
    unshelve (epose proof (@app_ext_singleton _ ImpModel σ args ltac:(solve_all_singleton)) as H);
    (* idtac "last2" σ args; *)
    rewrite H; (* erewrite does not work here, for some reason *)
    clear H *)
    rewrite (@app_ext_singleton _ M σ args ltac:(solve_all_singleton))
  end.

  Ltac rewrite_app_ext :=
  match goal with
  | |- ?G => rewrite_app_ext_innnermost G; cbn
  end.


Tactic Notation "deconstruct_elem_of_Theory" :=
  repeat match goal with
  | [ H : _ ∈ _ |- _ ] => inversion H; subst; clear H
  end; clear; simpl.

Tactic Notation "eval_helper" :=
  repeat
    match goal with
    | [ |- context [eval ?ρ (@kore_app ?Σ ?ex ?mu ?σ ?l) ] ] =>
       let H := fresh "H" in
       pose proof (eval_app_simpl σ l ρ) as H;
       rewrite H;
       clear H;
       cbn
    | _ => simp eval
    end.

Tactic Notation "rewrite_singleton_all" :=
    unshelve (rewrite_strat bottomup app_ext_singleton); [repeat esplit.. |].

  Ltac solve_functional_axiom :=
  match goal with
  | [ |- @eval _ ?M _ _ _ ?ρ (kore_exists _
                  (kore_equals ?s (kore_app ?σ ?l)
                               (kore_bevar In_nil))) = ⊤]
                               (* ^- NOTE: this is a restriction on db index 0!!! This pattern checks whether the axiom is a functional axiom *) =>
    let H := fresh "H" in
    epose proof (functional_symbol_is_functional σ s (hmap (fun s p =>
      match p with
      | kore_fevar x => x
      | _ => "_"%string
      end) l) M);
    apply H;
    eexists;
    reflexivity
  end.

Add Search Blacklist "_elim".
Add Search Blacklist "FunctionalElimination_".
Add Search Blacklist "_graph_mut".
Add Search Blacklist "_graph_rect".
