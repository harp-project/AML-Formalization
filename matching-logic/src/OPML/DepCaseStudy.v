From MatchingLogic.OPML Require Export OpmlSignature.
From stdpp Require Import base tactics list list_numbers propset.
Set Transparent Obligations.
From Coq Require Import Program.Equality String PropExtensionality.
From Equations Require Export -(notations) Equations.
From MatchingLogic Require Import stdpp_ext.
Set Default Proof Mode "Classic".

Inductive hlist {A : Type} (F : A -> Type) : list A -> Type :=
  | hnil : hlist F []
  | hcons {x} {xs} : F x -> hlist F xs -> hlist F (x :: xs)
.

Arguments hlist {_} _ & _.
Arguments hnil {_} {_}.
Arguments hcons {_} {_} {_} {_} & _ _.
Arguments hlist_rect {_} {_} {_} & _ _ {_} _ /.

Declare Scope hlist_scope.
Delimit Scope hlist_scope with hlist.
Bind Scope hlist_scope with hlist.

Infix "::" := hcons (at level 60, right associativity) : hlist_scope.
Notation "[ ]" := hnil (format "[ ]") : hlist_scope.
Notation "[ x ]" := (hcons x hnil) : hlist_scope.
Notation "[ x ; y ; .. ; z ]" := (hcons x (hcons y .. (hcons z hnil) ..)) (format "[ '[' x ; '/' y ; '/' .. ; '/' z ']' ]") : hlist_scope.

Tactic Notation "hlist_map" uconstr(f) "in" ident(h) :=
  let y := fresh in let H := fresh in
  induction h as [ | ? ? y _ H];
  [left | right];
  [eapply f; eauto using y | exact H].

Tactic Notation "hlist_foldr" uconstr(f) "with" uconstr(def) "in" ident(h) :=
let y := fresh in let H := fresh in
  induction h as [ | ?x ?xs y _ H ];
  [exact def | eapply f];
  [exact y | exact H].

Inductive Dbi {Σ : OPMLSignature} : opml_sort -> list opml_sort -> Type :=
  | dbiz {x} {xs} : Dbi x (x :: xs)
  | dbis {x y} {xs} : Dbi y xs -> Dbi y (x :: xs)
.

Definition cons_eq_inv {A} {x y : A} {xs ys} (H : x :: xs = y :: ys) : x = y /\ xs = ys := conj (f_equal (list_rect _ x (λ a _ _, a)) H) (f_equal (list_rect _ xs (λ _ a _, a)) H).

Fixpoint inc_dbi {Σ : OPMLSignature} {s} {ex ex' ex''} (dbi : Dbi s (ex ++ ex'')) : Dbi s (ex ++ ex' ++ ex'').
Proof.
  dependent destruction dbi.
  - destruct ex; simpl in *.
    + induction ex'; simpl.
      * rewrite <- x. left.
      * right. exact IHex'.
    + apply cons_eq_inv in x as [-> ->].
      left.
  - destruct ex; simpl in *.
    + induction ex'; simpl.
      * rewrite <- x.
        right. exact dbi.
      * right. exact IHex'.
    + apply cons_eq_inv in x as [-> ->].
      right. apply inc_dbi. exact dbi.
Defined. 

Arguments inc_dbi {_} {_} {_} {_} {_} !_.

Inductive OPMLPattern {Σ : OPMLSignature} : opml_sort -> list opml_sort -> Type :=
  | op_bot {s} {ex} : OPMLPattern s ex
  | op_bevar {s} {ex} : Dbi s ex -> OPMLPattern s ex
  | op_fevar {s} {ex} : opml_evar s -> OPMLPattern s ex
  | op_imp {s} {ex} : OPMLPattern s ex -> OPMLPattern s ex -> OPMLPattern s ex
  | op_app {ex} (σ : opml_symbol) : hlist (OPMLPattern ^~ ex) (opml_arg_sorts σ) -> OPMLPattern (opml_ret_sort σ) ex
  | op_eq {s s'} {ex} : OPMLPattern s ex -> OPMLPattern s ex -> OPMLPattern s' ex
  | op_ex {s s'} {ex} : OPMLPattern s (s' :: ex) -> OPMLPattern s ex
.

Fixpoint inc_evar {Σ : OPMLSignature} {s} {ex ex' ex''} (base : OPMLPattern s (ex ++ ex'')) : OPMLPattern s (ex ++ ex' ++ ex'').
Proof.
  revert s ex ex' ex'' base.
  fix IH 5.
  intros.
  dependent destruction base.
  - exact op_bot.
  - apply op_bevar, inc_dbi, d.
  - apply op_fevar, o.
  - apply op_imp; apply inc_evar.
    exact base1. exact base2.
  - apply op_app.
    hlist_map inc_evar in h.
  - eapply op_eq; apply inc_evar.
    exact base1. exact base2.
  - eapply op_ex. instantiate (1 := s').
    rewrite app_comm_cons.
    apply inc_evar.
    rewrite <- app_comm_cons.
    exact base.
Defined.

Arguments inc_evar {_} {_} {_} {_} {_} !_.

Fixpoint sub_evar {Σ : OPMLSignature} {s s'} {ex ex'} (dbi : Dbi s (ex ++ s' :: ex')) (repl : OPMLPattern s' ex') {struct dbi} : OPMLPattern s (ex ++ ex').
Proof.
  refine (match dbi in (Dbi o l) return (o = s -> l = ex ++ s' :: ex' -> OPMLPattern s (ex ++ ex')) with
          | dbiz => _
          | dbis dbi => _
          end eq_refl eq_refl); intros; subst.
  - destruct ex; simpl in *; apply cons_eq_inv in H0 as [-> ->].
    + exact repl.
    + apply op_bevar, dbiz.
  - destruct ex; simpl in *; apply cons_eq_inv in H0 as [-> ->].
    + apply op_bevar, dbi.
    + specialize (sub_evar _ _ _ _ _ dbi repl).
      apply (@inc_evar _ _ [] [o0]). simpl. exact sub_evar.
Defined.

Arguments sub_evar {_} {_} {_} {_} {_} !_ _.

Fixpoint bevar_subst {Σ : OPMLSignature} {s s'} {ex ex'} (base : OPMLPattern s (ex ++ s' :: ex')) (repl : OPMLPattern s' ex') {struct base} : OPMLPattern s (ex ++ ex').
Proof.
  intros.
  dependent destruction base.
  - exact op_bot.
  - eapply sub_evar; eauto.
  - apply op_fevar, o.
  - apply op_imp; eapply bevar_subst.
    2,4: exact repl. exact base1. exact base2.
  - apply op_app.
    hlist_map bevar_subst in h.
  - eapply op_eq; eapply bevar_subst.
    2,4: exact repl. exact base1. exact base2.
  - eapply op_ex.
    rewrite app_comm_cons.
    eapply bevar_subst.
    rewrite <- app_comm_cons. all: eauto.
Defined.

Arguments bevar_subst {_} {_} {_} _ {_} !_ _.

Module NatBool.
  Inductive sorts := nat_s | bool_s.
  Inductive symbols := add_s | is0_s | zero_s | succ_s | true_s | false_s.

  Fixpoint pos_idx {A : Type} (l : list A) (p : positive) {struct l} : option A :=
    match p, l with
    | 1%positive, (x :: xs) => Some x
    | 1%positive, [] => None
    | p, (x :: xs) => pos_idx xs (Pos.pred p)
    | _, [] => None
    end.

  Arguments pos_idx {_} _ _ : simpl nomatch.

  Create HintDb opml.
  Hint Unfold AntiSymm : opml.
  Hint Constructors PartialOrder : opml.
  Hint Extern 5 (EqDecision _) => unfold EqDecision, Decision; decide equality : opml.

  Instance NatBool : OPMLSignature.
  Proof.
    unshelve esplit.
    unshelve esplit;
    [exact sorts | exact eq | ..];
    auto with typeclass_instances opml.
    unshelve esplit. exact (sorts_rect _ 1%positive 2%positive).
    exact (pos_idx [nat_s; bool_s]).
    intros []; auto.
    unshelve esplit;
    only 1,2: exact (const string);
    auto with typeclass_instances.
    unshelve esplit;
    only 1: exact symbols;
    auto with opml.
    unshelve esplit.
    exact (symbols_rect _ 1%positive 2%positive 3%positive 4%positive 5%positive 6%positive).
    exact (pos_idx [add_s; is0_s; zero_s; succ_s; true_s; false_s]).
    intros []; auto.
    exact (symbols_rect _ [nat_s; nat_s] [nat_s] [] [nat_s] [] []).
    exact (symbols_rect _ nat_s bool_s nat_s nat_s bool_s bool_s).
  Defined.
End NatBool.

Instance propset_leibniz_equiv {A} : LeibnizEquiv (propset A).
Proof.
  intros ? ? ?. unfold equiv, set_equiv_instance in H.
  destruct x, y. f_equal. apply functional_extensionality.
  intros. specialize (H x). apply propositional_extensionality.
  auto.
Defined.

Section Model.
  Context {Σ : OPMLSignature}.

  Record OPMLModel := {
    opml_carrier :> opml_sort -> Set;
    opml_app (σ : opml_symbol) :
    hlist opml_carrier (opml_arg_sorts σ) -> propset (opml_carrier (opml_ret_sort σ));
    opml_inhabited (s : opml_sort) : Inhabited (opml_carrier s)
  }.

  Context {M : OPMLModel}.

  Record OPMLValuation : Type := {
    evar_valuation {s : opml_sort} (x : opml_evar s) : opml_carrier M s;
    svar_valuation {s : opml_sort} (X : opml_svar s) : propset (opml_carrier M s) ;
  }.

  Definition hcons_inv {A} {F : A -> Type} {x} {xs} P (X : forall (y : F x) (ys : hlist F xs), P) (ys : hlist F (x :: xs)) : P :=
    match ys in (hlist _ l) return (l = x :: xs -> P) with
    | hnil => λ H, False_rect _ (eq_ind nil (list_rect _ True (λ _ _ _, False)) I _ H)
    | @hcons _ _ a l y ys => λ H, X (eq_rect a F y x (f_equal (list_rect _ x (λ a _ _, a)) H)) (eq_rect l (hlist F) ys xs (f_equal (list_rect _ xs (λ _ a _, a)) H))
    end eq_refl.

  Fixpoint pointwise_elem_of {A} {F : A -> Type} {ss} (l : hlist F ss) (lps : hlist (propset ∘ F) ss) {struct ss} : Prop :=
    match ss return (hlist F ss -> hlist (propset ∘ F) ss -> Prop) with
    | [] => λ _ _, True
    | (x :: xs) => λ l lps, hcons_inv _ (λ y ys, hcons_inv _ (λ y' ys', y ∈ y' /\ pointwise_elem_of ys ys') lps) l
    end l lps.

  Arguments pointwise_elem_of {_} {_} {_} & _ _ /.

  Definition test1 : hlist (bool_rect _ nat bool) [true; false] := [1; true].
  Definition test2 : hlist (propset ∘ bool_rect _ nat bool) [true; false] := [{[1]}; {[true]}].
  Goal pointwise_elem_of test1 test2.
  Proof.
    simpl. set_solver.
  Qed.

  Definition app_ext (σ : opml_symbol) (args : hlist (propset ∘ (opml_carrier M)) (opml_arg_sorts σ)) : propset (opml_carrier M (opml_ret_sort σ)) := PropSet (fun e => exists (l : hlist (opml_carrier M) (opml_arg_sorts σ)), pointwise_elem_of l args /\ e ∈ opml_app M σ l).

  Definition update_evar_val {s} (ev : opml_evar s) (x : opml_carrier M s) (val : OPMLValuation) : OPMLValuation.
  Proof.
    unshelve esplit.
    intros s' ev'.
    destruct (decide (s = s')).
    destruct (decide (eq_rect s opml_evar ev _ e = ev')).
    exact (eq_rect s M x _ e).
    1,2:exact (evar_valuation val ev').
    exact (@svar_valuation val).
  Defined.

  Fixpoint free_evars {s} {ex} (sTarget : opml_sort) (φ : OPMLPattern s ex) : gset (opml_evar sTarget) :=
    match φ in (OPMLPattern s' _) return (s = s' -> gset (opml_evar sTarget)) with
    | op_bot | op_bevar _ => λ _, empty
    | @op_fevar _ o _ x => λ H, match decide (s = sTarget) with
                                   | left e => {[eq_rect o opml_evar x sTarget (eq_trans (eq_sym H) e)]}
                                   | _ => empty
                                   end
    | op_imp φ1 φ2 | op_eq φ1 φ2 => λ _, free_evars sTarget φ1 ∪ free_evars sTarget φ2
    | op_app σ l => λ _, ltac:(hlist_foldr (union ∘ free_evars _ _ sTarget) with empty in l)
    | op_ex x => λ _, free_evars sTarget x
    end eq_refl.

  Definition fresh_evar {s} {ex} (sTarget : opml_sort) (φ : OPMLPattern s ex) : opml_evar sTarget := fresh (elements (free_evars sTarget φ)).

  Fixpoint opml_size {s} {ex} (φ : OPMLPattern s ex) : nat :=
    match φ with
    | op_bot | op_bevar _ | op_fevar _ => 1
    | op_imp φ1 φ2 | op_eq φ1 φ2 => S (opml_size φ1 + opml_size φ2)
    | op_app σ l => S (hlist_rect 0 (λ _ _ a _ b, opml_size a + b) l)
    | op_ex φ => S (opml_size φ)
    end.

  Arguments opml_size {_} {_} & !_.

  Lemma JMeq_eq_rect {U : Type} {P : U → Type} {p q : U} {x : P p} {y : P q} (H : p = q) : JMeq x y -> eq_rect p P x q H = y.
  Proof.
    intros.
    apply JMeq_eq_dep, eq_dep_eq_sigT, eq_sigT_sig_eq in H0 as [].
    rewrite (Eqdep.EqdepTheory.UIP _ _ _ H x0).
    all: assumption.
  Defined.

  Hint Unfold eq_rect_r : opml.
  Hint Rewrite -> Eqdep.EqdepTheory.eq_rect_eq : opml.
  Hint Rewrite <- Eqdep.EqdepTheory.eq_rect_eq : opml.

  Lemma inc_evar_size : forall s ex ex' ex'' (φ : OPMLPattern s (ex ++ ex'')), opml_size (@inc_evar _ s ex ex' ex'' φ) = opml_size φ.
  Proof.
    fix IH 5. intros.
    dependent destruction φ; simpl; try reflexivity.
    1,3: auto.
    - induction h; auto.
    - autounfold with opml. autorewrite with opml.
      specialize (IH s (s' :: ex) ex' ex'' φ). auto.
  Defined.

  Hint Unfold Equality.block solution_left : opml.

  Lemma bevar_subst_size : forall ex ex' s s' (φ : OPMLPattern s (ex ++ s' :: ex')) o, opml_size (bevar_subst ex φ (op_fevar o)) = opml_size φ.
  Proof.
    fix IH 5.
    intros.
    dependent destruction φ; simpl; try reflexivity.
    2,4: auto.
    - autounfold with opml.
      simpl. clear IH.
      dependent induction d; simpl;
      apply (JMeq_eq_rect x1) in x as <-;
      destruct ex; simpl in *;
      pose proof (cons_eq_inv x1) as [];
      subst; autorewrite with opml;
      simpl; try reflexivity.

      autounfold with opml. simpl.
      specialize (IHd _ _ _ d erefl JMeq_refl o). rewrite <- IHd.

      remember (sub_evar _ _).
      exact (inc_evar_size y [] [o0] (ex ++ ex') o1).
    - induction h; auto.
    - autounfold with opml. autorewrite with opml.
      specialize (IH (s'0 :: ex) ex' s s'). auto.
  Defined.

  Obligation Tactic := idtac.

  Equations? opml_eval {ex} (ρ : OPMLValuation) {s} (φ : OPMLPattern s ex) : propset (opml_carrier M s) by wf (opml_size φ) :=
    opml_eval ρ op_bot                := empty ;
    opml_eval ρ (op_bevar _)          := empty ;
    opml_eval ρ (op_fevar x)          := {[evar_valuation ρ x]} ;
    opml_eval ρ (op_imp φ1 φ2)        := (⊤ ∖ (opml_eval ρ φ1)) ∪ (opml_eval ρ φ2) ;
    opml_eval ρ (op_app σ l)          := app_ext σ _ (*@hlist_rect _ _ (λ l _, hlist (propset ∘ M) l) hnil (λ _ _ a _ b, hcons (opml_eval ρ a) b) _ l*) ;
    opml_eval ρ (op_eq φ1 φ2)         := PropSet (λ _, (opml_eval ρ φ1) = (opml_eval ρ φ2)) ;
    opml_eval ρ (@op_ex _ _ s' _ φ) := ⊤ ≫= λ X, let o := fresh_evar s' φ in opml_eval (update_evar_val o X ρ) (bevar_subst [] φ (op_fevar o)) ;
  .
  Proof.
    1,2,4,5: simpl; lia.
    2: rewrite (bevar_subst_size [] ex s s' φ o); left.
    
    simpl in opml_eval.
    induction l. left.
    right. apply (opml_eval _ ρ _ f). lia.
    apply IHl. intros.
    apply (opml_eval _ x1 _ x3). lia.
  Defined.

  Definition Theory := propset (sigT (OPMLPattern ^~ [])).
  (* Instance elem_of_Theory : ElemOf (sigT (OPMLPattern ^~ [] ^~ [])) Theory. *)
  (* Proof. *)
  (*   unfold Theory. typeclasses eauto. *)
  (* Defined. *)
  Definition sat (Γ : Theory) := forall (ax : sigT (OPMLPattern ^~ [])), ax ∈ Γ -> forall ρ, @opml_eval [] ρ (projT1 ax) (projT2 ax) ≡ ⊤.

  Fixpoint all_singleton {xs} (ys : hlist (propset ∘ M) xs) : Type :=
    if ys isn't hcons y ys then unit else prod (sigT (eq y ∘ singleton)) (all_singleton ys).

  Fixpoint all_singleton_extract {xs} {ys : hlist (propset ∘ M) xs} (H : all_singleton ys) {struct ys} : hlist M xs.
  Proof.
    destruct ys. left.
    simpl in H. destruct H as [[] ?].
    right. assumption.
    eapply all_singleton_extract. eassumption.
  Defined.

  Lemma elem_of_PropSet_1 {A : Type} (P : A → Prop) (x : A) : x ∈ PropSet P -> P x.
  Proof.
    intros. apply elem_of_PropSet. assumption.
  Defined.

  Lemma destruct_hcons {A} {F : A -> Type} {x} {xs} (l : hlist F (x :: xs)) : sigT (λ '(y, ys), l = hcons y ys).
  Proof.
    dependent destruction l.
    exists (f, l). reflexivity.
  Defined.

  Lemma destruct_hnil {A} {F : A -> Type} (l : hlist F []) : l = hnil.
  Proof.
    dependent destruction l.
    reflexivity.
  Defined.

  Lemma app_ext_all_singleton_is_app {σ} {args : hlist (propset ∘ M) (opml_arg_sorts σ)} (H : all_singleton args) : app_ext σ args = opml_app _ σ (all_singleton_extract H).
  Proof.
    apply set_eq. split; intros.
    unfold app_ext in H0.
    apply elem_of_PropSet_1 in H0.
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
End Model.

Arguments sat {_} _ _ /.

Module NatBool_Sematics.
  Import NatBool.

  (* Fixpoint hlist_to_prod `(@hlist A F xs) : foldr (prod ∘ F) unit xs. *)
  (* Proof. *)
  (*   destruct xs; simpl. *)
  (*   split. *)
  (*   unshelve eapply (hcons_inv _ _ H); intros. *)
  (*   split. exact y. apply hlist_to_prod. exact ys. *)
  (* Defined. *)

  Definition mk_OPMLModel {Σ : OPMLSignature} (opml_carrier : opml_sort → Set) : (forall (σ : opml_symbol), foldr (λ c a, opml_carrier c -> a) (propset (opml_carrier (opml_ret_sort σ))) (opml_arg_sorts σ)) → (∀ s : opml_sort, Inhabited (opml_carrier s)) → OPMLModel.
  Proof.
    intros.
    unshelve esplit.
    exact opml_carrier.
    intros.
    specialize (X σ).
    induction (opml_arg_sorts σ). simpl in X. exact X.
    simpl in X. unshelve eapply (hcons_inv _ _ X0); intros.
    specialize (X y). specialize (IHl X ys). exact IHl.
    exact H.
  Defined.

  Definition mk_OPMLModel_singleton {Σ : OPMLSignature} (opml_carrier : opml_sort → Set) : (forall (σ : opml_symbol), foldr (λ c a, opml_carrier c -> a) (opml_carrier (opml_ret_sort σ)) (opml_arg_sorts σ)) → (∀ s : opml_sort, Inhabited (opml_carrier s)) → OPMLModel.
  Proof.
    intros.
    unshelve esplit.
    exact opml_carrier.
    intros.
    specialize (X σ).
    induction (opml_arg_sorts σ). simpl in X. exact {[X]}.
    simpl in X. unshelve eapply (hcons_inv _ _ X0); intros.
    specialize (X y). specialize (IHl X ys). exact IHl.
    exact H.
  Defined.

  Definition NatBool_Model : OPMLModel.
  Proof.
    unshelve eapply mk_OPMLModel_singleton.
    exact (sorts_rect _ nat bool). (* carriers of the sorts *)
    
    exact (symbols_rect _ Nat.add (nat_rect _ true (λ _ _, false)) 0 S true false).
    intros []; auto with typeclass_instances.
  Defined.

  Definition op_not {s} {ex} (φ : OPMLPattern s ex) := op_imp φ op_bot.
  Definition op_all {s s'} {ex} (φ : OPMLPattern s (s' :: ex)) := op_not (op_ex (op_not φ)).

  Definition NatBool_Theory : Theory := {[
    existT bool_s (op_eq (op_app is0_s [op_app zero_s []]) (op_app true_s []));
    existT nat_s (op_all (op_eq (op_app is0_s [op_app succ_s [op_bevar dbiz]]) (op_app false_s [])))
  ]}.

  Arguments NatBool_Theory /.

  (* Hint Extern 5 (?x ∈ ⊤) => simple apply elem_of_top' : opml. *)
  (* (1* Hint Resolve elem_of_top' : opml. *1) *)

  (* Lemma propset_top_elem_of_rev {A : Type} (S : propset A) (_ : ∀ t : A, t ∈ S) : S = ⊤. *)
  (* Proof. *)
  (*   apply set_eq. auto with opml extcore. *)
  (* Defined. *)

  Tactic Notation "deconstruct_elem_of_Theory" :=
    repeat match goal with
    | [ H : _ ∈ _ |- _ ] => inversion H; clear H
    end; clear; simpl.

  Tactic Notation "eval_helper" :=
    repeat match goal with
           | [ |- context [opml_eval ?ρ (@op_app ?Σ ?ex ?σ ?l)] ] => let H := fresh in pose proof (opml_eval_equation_5 ex ρ σ l) as H; simpl in H; rewrite H; clear H
           | _ => simp opml_eval
           end.

  Arguments opml_eval_obligation_3 {_} {_} _ _ _ _ _ /.

  (* Tactic Notation "rewrite_singleton" constr(sy) := *)
  (*   match goal with *)
  (*   | [ |- context [@app_ext ?Σ ?M sy ?l]] => let H := fresh in unshelve epose (_ : (@all_singleton Σ M _ l)) as H; [repeat esplit | rewrite (@app_ext_all_singleton_is_app Σ M sy l H)] *)
  (*   end. *)

  Tactic Notation "set_helper" :=
    repeat match goal with
           | [ |- PropSet ?P ≡ ⊤ ] => enough (forall x, P x) by set_solver; intros
           | [ |- context[?x ∪ ∅] ] => rewrite union_empty_r
           (* put these into separate lemmas? *)
           | [ |- ⊤ ∖ ?X ≡ ⊤ ] => enough (X ≡ ∅) by set_solver
           | [ |- ⊤ ∖ ?X ≡ ∅ ] => enough (X ≡ ⊤) by set_solver
           | [ |- ⊤ ≫= ?f ≡ ∅ ] => enough (forall x, f x ≡ ∅) by set_solver; intros
           end.

  Tactic Notation "rewrite_singleton_all" :=
    unshelve (rewrite_strat bottomup app_ext_all_singleton_is_app); [repeat esplit.. |].

  Goal sat NatBool_Model NatBool_Theory.
  Proof.
    simpl. unfold op_all, op_not. intros.
    deconstruct_elem_of_Theory; eval_helper; set_helper.
    now rewrite_singleton_all.

    repeat (unfold bevar_subst, Equality.block, solution_left, eq_rect_r; simpl).
    eval_helper. set_helper. now rewrite_singleton_all.
  Qed.
