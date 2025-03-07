From MatchingLogic.OPML Require Export OpmlSignature.
From stdpp Require Import base tactics list list_numbers propset.
Set Transparent Obligations.
From Coq Require Import Program.Equality String.
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

Fixpoint inc_dbi {Σ : OPMLSignature} {s} {ex ex' ex''} (dbi : Dbi s (ex ++ ex'')) : Dbi s (ex ++ ex' ++ ex'').
Proof.
  dependent destruction dbi.
  - destruct ex; simpl in *.
    + induction ex'; simpl.
      * rewrite <- x. left.
      * right. exact IHex'.
    + apply cons_eq_inj in x as [-> ->].
      left.
  - destruct ex; simpl in *.
    + induction ex'; simpl.
      * rewrite <- x.
        right. exact dbi.
      * right. exact IHex'.
    + apply cons_eq_inj in x as [-> ->].
      right. apply inc_dbi. exact dbi.
Defined. 

Arguments inc_dbi {_} {_} {_} {_} {_} !_.

Inductive OPMLPattern {Σ : OPMLSignature} : opml_sort -> list opml_sort -> list opml_sort -> Type :=
  | op_bot {s} {ex mu} : OPMLPattern s ex mu
  | op_bevar {s} {ex mu} : Dbi s ex -> OPMLPattern s ex mu
  | op_fevar {s} {ex mu} : opml_evar s -> OPMLPattern s ex mu
  | op_imp {s} {ex mu} : OPMLPattern s ex mu -> OPMLPattern s ex mu -> OPMLPattern s ex mu
  | op_app {ex mu} (σ : opml_symbol) : hlist (OPMLPattern ^~ ex ^~ mu) (opml_arg_sorts σ) -> OPMLPattern (opml_ret_sort σ) ex mu
  | op_eq {s s'} {ex mu} : OPMLPattern s ex mu -> OPMLPattern s ex mu -> OPMLPattern s' ex mu
  | op_ex {s s'} {ex mu} : OPMLPattern s (s' :: ex) mu -> OPMLPattern s ex mu
.

Fixpoint inc_evar {Σ : OPMLSignature} {s} {ex ex' ex'' mu} (base : OPMLPattern s (ex ++ ex'') mu) : OPMLPattern s (ex ++ ex' ++ ex'') mu.
Proof.
  revert s ex ex' ex'' mu base.
  fix IH 6.
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

Arguments inc_evar {_} {_} {_} {_} {_} {_} !_.

Fixpoint sub_evar {Σ : OPMLSignature} {s s'} {ex ex' mu} (dbi : Dbi s (ex ++ s' :: ex')) (repl : OPMLPattern s' ex' mu) {struct dbi} : OPMLPattern s (ex ++ ex') mu.
Proof.
  dependent destruction dbi.
  - destruct ex; simpl in *; apply cons_eq_inj in x as [-> ->].
    + exact repl.
    + apply op_bevar, dbiz.
  - destruct ex; simpl in *; apply cons_eq_inj in x as [-> ->].
    + apply op_bevar, dbi.
    + specialize (sub_evar _ _ _ _ _ _ dbi repl).
      apply (@inc_evar _ _ [] [o]). simpl. exact sub_evar.
Defined.

Arguments sub_evar {_} {_} {_} {_} {_} {_} !_ _.

Fixpoint bevar_subst {Σ : OPMLSignature} {s s'} {ex ex' mu} (base : OPMLPattern s (ex ++ s' :: ex') mu) (repl : OPMLPattern s' ex' mu) {struct base} : OPMLPattern s (ex ++ ex') mu.
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

Arguments bevar_subst {_} {_} {_} _ {_} {_} !_ _.

Module Example.
Inductive sorts := nat_s | bool_s.
Inductive symbols := add_s | is0_s | zero_s | succ_s | true_s | false_s.

Fixpoint pos_idx {A : Type} (l : list A) (p : positive) {struct l} : option A :=
  match p, l with
  | 1%positive, (x :: xs) => Some x
  | 1%positive, [] => None
  | p, (x :: xs) => pos_idx xs (Pos.pred p)
  | _, [] => None
  end.

Instance NatBool : OPMLSignature.
Proof.
  unshelve esplit.
  unshelve esplit.
  exact sorts. exact (λ x y, x = y).
  unfold EqDecision, Decision. decide equality.
  unshelve esplit. exact (sorts_rect _ 1%positive 2%positive).
  exact (pos_idx [nat_s; bool_s]).
  simpl. intros []; auto.
  split. split. auto. intros ? ? ? ? ?. rewrite <- H0. exact H.
  intros ? ? ? ?. exact H.
  unshelve esplit.
  1,2: exact (const string).
  1-6: typeclasses eauto.
  unshelve esplit.
  exact symbols.
  unfold EqDecision, Decision. decide equality.
  unshelve esplit.
  exact (symbols_rect _ 1%positive 2%positive 3%positive 4%positive 5%positive 6%positive).
  exact (pos_idx [add_s; is0_s; zero_s; succ_s; true_s; false_s]).
  intros []; auto.
  exact (symbols_rect _ [nat_s; nat_s] [nat_s] [] [nat_s] [] []).
  exact (symbols_rect _ nat_s bool_s nat_s nat_s bool_s bool_s).
Defined.

End Example.

Section asd.
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

  (* Definition cons_eq_inv {A} {x y : A} {xs ys} (H : x :: xs = y :: ys) : x = y /\ xs = ys := conj (f_equal (list_rect _ x (λ a _ _, a)) H) (f_equal (list_rect _ xs (λ _ a _, a)) H). *)

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

  (* Fixpoint map_hlist {A : Type} {F G : A -> Type} {l : list A} (f : forall (a : A), F a -> G a) (xs : hlist F l) {struct l} : hlist G l. *)
  (* Proof. *)
  (*   induction l. *)
  (*   left. *)
  (*   inversion xs; subst. *)
  (*   right. *)
  (*   apply f, X. *)
  (*   apply IHl, X0. *)
  (* Defined. *)

  Fixpoint free_evars {s} {ex mu} (sTarget : opml_sort) (φ : OPMLPattern s ex mu) : gset (opml_evar sTarget) :=
    match φ in (OPMLPattern s' _ _) return (s = s' -> gset (opml_evar sTarget)) with
    | op_bot | op_bevar _ => λ _, empty
    | @op_fevar _ o _ _ x => λ H, match decide (s = sTarget) with
                                   | left e => {[eq_rect o opml_evar x sTarget (eq_trans (eq_sym H) e)]}
                                   | _ => empty
                                   end
    | op_imp φ1 φ2 | op_eq φ1 φ2 => λ _, free_evars sTarget φ1 ∪ free_evars sTarget φ2
    | op_app σ l => λ _, ltac:(hlist_foldr (union ∘ free_evars _ _ _ sTarget) with empty in l)
    | op_ex x => λ _, free_evars sTarget x
    end eq_refl.

  Definition fresh_evar {s} {ex mu} (sTarget : opml_sort) (φ : OPMLPattern s ex mu) : opml_evar sTarget := fresh (elements (free_evars sTarget φ)).
  
  Fixpoint opml_size {s} {ex mu} (φ : OPMLPattern s ex mu) : nat :=
    match φ with
    | op_bot | op_bevar _ | op_fevar _ => 1
    | op_imp φ1 φ2 | op_eq φ1 φ2 => S (opml_size φ1 + opml_size φ2)
    | op_app σ l => ltac:(hlist_foldr (plus ∘ opml_size _ _ _) with 0 in l)
    | op_ex φ => S (opml_size φ)
    end.

  Arguments opml_size {_} {_} {_} & !_.

  Obligation Tactic := idtac.

  Fixpoint hlistIn {A} {F : A -> Type} {x} {xs} {ED : EqDecision A} (y : F x) (ys : hlist F xs) : Prop.
  Proof.
    destruct ys.
    exact False.
    destruct (decide (x = x0)).
    exact (eq_rect x F y x0 e = f \/ hlistIn _ _ _ _ _ y ys).
    exact False.
  Defined.

  Arguments hlistIn {_} {_} {_} {_} {_} & _ !_.

  Program Fixpoint opml_eval {ex mu} (ρ : OPMLValuation) {s} (φ : OPMLPattern s ex mu) {measure (opml_size φ)} : propset (opml_carrier M s) :=
    match φ with
    | op_bot | op_bevar _ => empty
    | op_fevar x => {[evar_valuation ρ x]}
    | op_imp φ1 φ2 => (⊤ ∖ (opml_eval ρ φ1)) ∪ (opml_eval ρ φ2)
    | op_app σ l => app_ext σ _
    | op_eq φ1 φ2 => PropSet (λ _, (opml_eval ρ φ1) = (opml_eval ρ φ2))
    | @op_ex _ _ s' _ _ φ => propset_fa_union (λ X, let o := fresh_evar s' φ in opml_eval (update_evar_val o X ρ) (bevar_subst [] φ (op_fevar o)))
    end.

  Next Obligation.
    intros. subst. simpl. lia.
  Defined.
  Next Obligation.
    intros. subst. simpl. lia.
  Defined.
  Next Obligation.
    intros. subst. simpl in opml_eval.
  Admitted.
  Next Obligation.
    intros. subst. simpl. lia.
  Defined.
  Next Obligation.
    intros. subst. simpl. lia.
  Defined.
  Lemma bevar_subst_opml_size : forall s s' ex mu (φ : OPMLPattern s (s' :: ex) mu) x, opml_size (bevar_subst [] φ (op_fevar x)) = opml_size φ.
  Proof.
    intros.
    dependent induction φ; simpl; auto.
    * erewrite <- IHφ1, <- IHφ2. simpl.
    * f_equal. induction H; simpl.
      reflexivity.
      rewrite IHForall.
      erewrite H.
      reflexivity.
    * by erewrite IHφ.
    * by erewrite IHφ.
    * by rewrite ->IHφ1, ->IHφ2.
  Defined.
  Next Obligation.
    intros. subst. simpl.
    clear. subst o.
    induction φ; simpl.
  Admitted.
  Next Obligation.
    apply measure_wf, lt_wf.
  Defined.
