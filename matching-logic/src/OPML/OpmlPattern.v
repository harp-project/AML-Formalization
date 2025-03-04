(* From Coq Require Import ssreflect ssrfun ssrbool. *)
From MatchingLogic.OPML Require Export OpmlSignature.
From stdpp Require Export base list list_numbers fin.
(* This is unset by stdpp. We need to set it again.*)
Set Transparent Obligations.
From Coq Require Import Program.Equality.
From Equations Require Export -(notations) Equations.

Set Default Proof Mode "Classic".

(* De Bruijn indices for element and set variables*)
Record Edbi := { edbi_n : nat; }.
Record Sdbi := { sdbi_n : nat; }.

Inductive dephlist {A : Type} {F : A -> Type} : list A -> Type :=
  | dhnil : dephlist []
  | dhcons {x : A} {xs : list A} : F x -> dephlist xs -> dephlist (x :: xs)
.

Arguments dhcons {_} {_} {_} {_} & _ _.

Notation "[ ]" := dhnil (format "[ ]").
Notation "[ x ]" := (dhcons x dhnil).
Notation "[ x ; y ; .. ; z ]" := (dhcons x (dhcons y .. (dhcons z dhnil) ..)).

(* Inductive dephlist : list Type -> Type := *)
(*   | dhnil : dephlist [] *)
(*   | dhcons {T : Type} {Ts : list Type} : T -> dephlist Ts -> dephlist (T :: Ts) *)
(* . *)

Inductive OPMLPattern {Σ : OPMLSignature} : opml_sort -> Type :=
  | op_upcast (from to : opml_sort) (subsort : opml_subsort from to) (φ : OPMLPattern from) : OPMLPattern to
  | op_bot {s : opml_sort} : OPMLPattern s
  | op_bevar {s : opml_sort} (dbi : Edbi) : OPMLPattern s
  | op_bsvar {s : opml_sort} (dbi : Sdbi) : OPMLPattern s
  | op_fevar {s : opml_sort} (x : opml_evar s) : OPMLPattern s
  | op_fsvar {s : opml_sort} (X : opml_svar s) : OPMLPattern s
  | op_imp {s : opml_sort} (φ1 φ2 : OPMLPattern s) : OPMLPattern s
  | op_app (σ : opml_symbol) (args : @dephlist _ OPMLPattern (opml_arg_sorts σ)) : OPMLPattern (opml_ret_sort σ)
  (* | op_app (σ : opml_symbol) (args : dephlist (map OPMLPattern (opml_arg_sorts σ))) : OPMLPattern (opml_ret_sort σ) *)
  | op_ex {s : opml_sort} (φ : OPMLPattern s) : OPMLPattern s
  | op_mu {s : opml_sort} (φ : OPMLPattern s) : OPMLPattern s
.

Inductive Edbi2 {Σ : OPMLSignature} : list opml_sort -> opml_sort -> Type :=
  | edbi0 {s : opml_sort} {ss : list opml_sort} : Edbi2 (s :: ss) s
  | edbis {s s' : opml_sort} {ss : list opml_sort} : Edbi2 ss s -> Edbi2 (s' :: ss) s
.

Check edbis (edbis edbi0).

(* Definition nth_lt {A : Type} n (l : list A) (H : n < length l) : A := *)
(*   (match nth_error l n as asd return (nth_error l n = asd -> A) with *)
(*    | Some x => λ _, x *)
(*    | None => λ H1, False_rect A (proj2 (nth_error_Some l n) H H1) *)
(*    end) erefl. *)

(* Definition nat_to_edbi2 {Σ : OPMLSignature} {ss : list opml_sort} (n : nat) (nlt : n < length ss) : Edbi2 ss (nth_lt n ss nlt). *)
(* Proof. *)
(*   induction n. destruct ss; simpl in nlt. *)
(*   destruct (Nat.nlt_0_r _ nlt). *)
(*   unfold nth_lt. simpl. left. *)
(*   (1* specialize (IHn (Nat.lt_succ_l _ _ nlt)). *1) *)
(*   destruct ss. simpl in nlt. *)
(*   destruct (Nat.nlt_0_r _ nlt). *)
(*   unfold nth_lt. simpl. *)
(*   (1* enough {x : opml_sort & nth_error ss n = Some x} as [? ->]. *1) *)
(*   (1* destruct (nth_error ss n). *1) *)
(*   (1* Search nth_error lt length. *1) *)
(*   (1* case_match. *1) *)
(*   (1* pose proof (n0 nlt). *1) *)
(*   (1* rewrite nth_error_cons_succ in H0. *1) *)
(*   (1* Search not eq None Some. *1) *)
(*   (1* right. *1) *)
(*   (1* simpl in IHn. *1) *)
(*   (1* unfold nth_lt. simpl. *1) *)
(* Abort. *)

(* Inductive OPMLClosedPattern {Σ : OPMLSignature} : opml_sort -> list opml_sort -> list opml_sort -> Type := *)
(*   | ocp_upcast {ex mu : list opml_sort} (from to : opml_sort) (subsort : opml_subsort from to) (φ : OPMLClosedPattern from ex mu) : OPMLClosedPattern to ex mu *)
(*   | ocp_bot {s : opml_sort} {ex mu : list opml_sort} : OPMLClosedPattern s ex mu *)
(*   | ocp_bevar {ex mu : list opml_sort} (dbi : nat) {dbilt : dbi < length ex} : OPMLClosedPattern (nth_lt dbi ex dbilt) ex mu *)
(*   | ocp_bsvar {ex mu : list opml_sort} (dbi : nat) (dbilt : dbi < length mu) : OPMLClosedPattern (nth_lt dbi mu dbilt) ex mu *)
(*   | ocp_fevar {s : opml_sort} {ex mu : list opml_sort} (x : opml_evar s) : OPMLClosedPattern s ex mu *)
(*   | ocp_fsvar {s : opml_sort} {ex mu : list opml_sort} (X : opml_svar s) : OPMLClosedPattern s ex mu *)
(*   | ocp_imp {s : opml_sort} {ex mu : list opml_sort} (φ1 : OPMLClosedPattern s ex mu) (φ2 : OPMLClosedPattern s ex mu) : OPMLClosedPattern s ex mu *)
(*   | ocp_app {ex mu : list opml_sort} (σ : opml_symbol) (args : @dephlist _ (OPMLClosedPattern ^~ ex ^~ mu) (opml_arg_sorts σ)) : OPMLClosedPattern (opml_ret_sort σ) ex mu *)
(*   | ocp_ex {s s' : opml_sort} {ex mu : list opml_sort} (φ : OPMLClosedPattern s (s' :: ex) mu) : OPMLClosedPattern s ex mu *)
(*   | ocp_mu {s s' : opml_sort} {ex mu : list opml_sort} (φ : OPMLClosedPattern s ex (s' :: mu)) : OPMLClosedPattern s ex mu *)
(* . *)

(* Definition nth_fin {A : Type} (l : list A) (n : fin (length l)) : A. *)
(* Proof. *)
(*   induction l; simpl in n; inv_fin n; auto. *)
(* Defined. *)

(* Compute nth_fin [4;5;2] 0%fin. *)
(* Compute nth_fin [4;5;2] 1%fin. *)
(* Compute nth_fin [4;5;2] 2%fin. *)
(* Fail Compute nth_fin [4;5;2] 3%fin. *)

(* Definition fin_to_edbi2 {Σ : OPMLSignature} {ss : list opml_sort} (n : fin (length ss)) : Edbi2 ss (nth_fin ss n). *)
(* Proof. *)
(*   induction ss; simpl in n; inv_fin n. *)
(*   simpl. left. *)
(*   intros. simpl. specialize (IHss i). right. exact IHss. *)
(* Defined. *)

(* Check @fin_to_edbi2 _ [_;_;_;_] 3%fin. *)

(* Inductive OPMLClosedPattern {Σ : OPMLSignature} : opml_sort -> list opml_sort -> list opml_sort -> Type := *)
(*   | ocp_upcast {ex mu : list opml_sort} (from to : opml_sort) (subsort : opml_subsort from to) (φ : OPMLClosedPattern from ex mu) : OPMLClosedPattern to ex mu *)
(*   | ocp_bot {s : opml_sort} {ex mu : list opml_sort} : OPMLClosedPattern s ex mu *)
(*   | ocp_bevar {ex mu : list opml_sort} (dbi : fin (length ex)) : OPMLClosedPattern (nth_fin ex dbi) ex mu *)
(*   | ocp_bsvar {ex mu : list opml_sort} (dbi : fin (length mu)) : OPMLClosedPattern (nth_fin mu dbi) ex mu *)
(*   | ocp_fevar {s : opml_sort} {ex mu : list opml_sort} (x : opml_evar s) : OPMLClosedPattern s ex mu *)
(*   | ocp_fsvar {s : opml_sort} {ex mu : list opml_sort} (X : opml_svar s) : OPMLClosedPattern s ex mu *)
(*   | ocp_imp {s : opml_sort} {ex mu : list opml_sort} (φ1 : OPMLClosedPattern s ex mu) (φ2 : OPMLClosedPattern s ex mu) : OPMLClosedPattern s ex mu *)
(*   | ocp_app {ex mu : list opml_sort} (σ : opml_symbol) (args : @dephlist _ (OPMLClosedPattern ^~ ex ^~ mu) (opml_arg_sorts σ)) : OPMLClosedPattern (opml_ret_sort σ) ex mu *)
(*   | ocp_ex {s s' : opml_sort} {ex mu : list opml_sort} (φ : OPMLClosedPattern s (s' :: ex) mu) : OPMLClosedPattern s ex mu *)
(*   | ocp_mu {s s' : opml_sort} {ex mu : list opml_sort} (φ : OPMLClosedPattern s ex (s' :: mu)) : OPMLClosedPattern s ex mu *)
(* . *)

Inductive OPMLClosedPattern {Σ : OPMLSignature} : opml_sort -> list opml_sort -> list opml_sort -> Type :=
  | ocp_upcast {ex mu : list opml_sort} (from to : opml_sort) (subsort : opml_subsort from to) (φ : OPMLClosedPattern from ex mu) : OPMLClosedPattern to ex mu
  | ocp_bot {s : opml_sort} {ex mu : list opml_sort} : OPMLClosedPattern s ex mu
  | ocp_bevar {s : opml_sort} {ex mu : list opml_sort} (dbi : Edbi2 ex s) : OPMLClosedPattern s ex mu
  | ocp_bsvar {s : opml_sort} {ex mu : list opml_sort} (dbi : Edbi2 mu s) : OPMLClosedPattern s ex mu
  | ocp_fevar {s : opml_sort} {ex mu : list opml_sort} (x : opml_evar s) : OPMLClosedPattern s ex mu
  | ocp_fsvar {s : opml_sort} {ex mu : list opml_sort} (X : opml_svar s) : OPMLClosedPattern s ex mu
  | ocp_imp {s : opml_sort} {ex mu : list opml_sort} (φ1 : OPMLClosedPattern s ex mu) (φ2 : OPMLClosedPattern s ex mu) : OPMLClosedPattern s ex mu
  | ocp_app {ex mu : list opml_sort} (σ : opml_symbol) (args : @dephlist _ (OPMLClosedPattern ^~ ex ^~ mu) (opml_arg_sorts σ)) : OPMLClosedPattern (opml_ret_sort σ) ex mu
  (* | ocp_app {ex mu : list opml_sort} (σ : opml_symbol) : foldr (λ c a, OPMLClosedPattern c ex mu -> a) (OPMLClosedPattern (opml_ret_sort σ) ex mu) (opml_arg_sorts σ) *)
  (* | ocp_app {ex mu : list opml_sort} (σ : opml_symbol) (args : foldr (λ c a, (OPMLClosedPattern c ex mu * a)%type) unit (opml_arg_sorts σ)) : OPMLClosedPattern (opml_ret_sort σ) ex mu *)
  | ocp_ex {s s' : opml_sort} {ex mu : list opml_sort} (φ : OPMLClosedPattern s (s' :: ex) mu) : OPMLClosedPattern s ex mu
  | ocp_mu {s s' : opml_sort} {ex mu : list opml_sort} (φ : OPMLClosedPattern s ex (s' :: mu)) : OPMLClosedPattern s ex mu
.

Definition dephlist_map {A : Type} {F G : A -> Type} {l : list A} (f : forall (a : A), F a -> G a) (xs : @dephlist A F l) : @dephlist A G l.
Proof.
  induction l. left.
  inversion_clear xs; subst.
  right; auto.
Defined.

(* (1* evar_open *1) *)
(* Goal forall {Σ : OPMLSignature} `{ex : list opml_sort} `(x : opml_evar s') `(OPMLClosedPattern s (s' :: ex) mu), OPMLClosedPattern s ex mu. *)
(* Proof. *)
(*   intros * ? *. *)
(*   generalize mu, s. *)
(*   fix IH 3. *)
(*   inversion_clear 1; subst. *)
(*   - eapply (ocp_upcast); eauto. *)
(*   - apply ocp_bot. *)
(*   - inversion dbi; subst. *)
(*     + apply ocp_fevar; auto. *)
(*     + apply ocp_bevar; auto. *)
(*   - apply ocp_bsvar; auto. *)
(*   - apply ocp_fevar; auto. *)
(*   - apply ocp_fsvar; auto. *)
(*   - apply ocp_imp; auto. *)
(*   - apply ocp_app. eapply dephlist_map. exact (IH mu0). auto. *)
(*   - eapply ocp_ex. admit. *)
(*   - eapply ocp_mu; eauto. *)
(* Abort. *)

(* Inductive sub {Σ : OPMLSignature} : list opml_sort -> list opml_sort -> Type := *)
(*   | subp {xs : list opml_sort} {x : opml_sort} : sub (x :: xs) xs *)
(*   | subz {xs mu : list opml_sort} {x : opml_sort} : OPMLClosedPattern x xs mu -> sub xs (x :: xs) *)
(*   | subs {xs ys : list opml_sort} {x : opml_sort} : sub xs ys -> sub (x :: xs) (x :: ys) *)
(*   . *)

Inductive sub {Σ : OPMLSignature} : list opml_sort -> list opml_sort -> list opml_sort -> Type :=
  | subp {xs mu : list opml_sort} {x : opml_sort} : sub (x :: xs) xs mu
  | subz {xs mu : list opml_sort} {x : opml_sort} : OPMLClosedPattern x xs mu -> sub xs (x :: xs) mu
  | subs {xs ys mu : list opml_sort} {x : opml_sort} : sub xs ys mu -> sub (x :: xs) (x :: ys) mu
  .

(* Fixpoint sub_evar `(dbi : @Edbi2 Σ ex0 s) `(σ : sub ex1 ex0 mu) : OPMLClosedPattern s ex1 mu. *)
(* Proof. *)
(*   inversion σ; subst. *)
(*   - apply ocp_bevar, edbis, dbi. *)
(*   - inversion dbi; subst. *)
(*     + exact H. *)
(*     + apply ocp_bevar, H3. *)
(*   - inversion dbi; subst. *)
(*     + apply ocp_bevar, edbi0. *)
(*     + specialize (sub_evar _ _ _ H3 _ _ H). *)

(* About OPMLClosedPattern_rect. *)

(* Fixpoint sub_subp {Σ : OPMLSignature} (ex mu : list opml_sort) (s x : opml_sort) (φ : OPMLClosedPattern s ex mu) : OPMLClosedPattern s (x :: ex) mu. *)
(* Proof. *)
(*   intros. *)
(*   inversion φ; subst. *)
(*   - eapply ocp_upcast. eauto. apply sub_subp, φ0. *)
(*   - apply ocp_bot. *)
(*   - apply ocp_bevar, edbis, dbi. *)
(*   - apply ocp_bsvar. auto. *)
(*   - apply ocp_fevar. auto. *)
(*   - apply ocp_fsvar. auto. *)
(*   - apply ocp_imp; apply sub_subp; [exact φ1 | exact φ2]. *)
(*   - apply ocp_app. eapply dephlist_map. 2: exact args. *)
(*     intros. apply sub_subp, X. *)
(*   - eapply ocp_ex. *) 
(* Abort. *)

Fixpoint measure_Edbi2 `(dbi : @Edbi2 Σ xs x) : nat :=
  match dbi with
  | edbi0 => 0
  | edbis dbi' => S (measure_Edbi2 dbi')
  end.

Fixpoint dephlist_foldr {A B : Type} {F : A -> Type} {xs : list A} (f : ∀ a, F a -> B -> B) (def : B) (l : @dephlist A F xs) : B.
Proof.
  dependent destruction l.
  exact def.
  eapply f. exact f0.
  eapply dephlist_foldr. exact f. exact def. exact l.
Defined.

Compute dephlist_foldr (bool_rect _ plus (bool_rect _ (plus 1) (plus 0))) 0 ([2; true; 4; 5; false; false] : @dephlist _ (bool_rect _ nat bool) [true; false; true; true; false; false]).

(* Lemma OPMLClosedPattern_custom_ind : *)
(*   ∀ (Σ : OPMLSignature) (P : ∀ (o : opml_sort) (l l0 : list opml_sort), *)
(*   OPMLClosedPattern o l l0 → Prop), *)
(*   (∀ (ex mu : list opml_sort) (from to : opml_sort) (subsort : opml_subsort from to) (φ : OPMLClosedPattern from ex mu), P from ex mu φ → P to ex mu (ocp_upcast from to subsort φ)) → *)
(*   (∀ (s : opml_sort) (ex mu : list opml_sort), P s ex mu ocp_bot) → *)
(*   (∀ (s : opml_sort) (ex mu : list opml_sort) (dbi : Edbi2 ex s), P s ex mu (ocp_bevar dbi)) → *)
(*   (∀ (s : opml_sort) (ex mu : list opml_sort) (dbi : Edbi2 mu s), P s ex mu (ocp_bsvar dbi)) → *)
(*   (∀ (s : opml_sort) (ex mu : list opml_sort) (x : opml_evar s), P s ex mu (ocp_fevar x)) → *)
(*   (∀ (s : opml_sort) (ex mu : list opml_sort) (X : opml_svar s), P s ex mu (ocp_fsvar X)) → *)
(*   (∀ (s : opml_sort) (ex mu : list opml_sort) (φ1 : OPMLClosedPattern s ex mu), P s ex mu φ1 → ∀ φ2 : OPMLClosedPattern s ex mu, P s ex mu φ2 → P s ex mu (ocp_imp φ1 φ2)) → *)
(*   (∀ (ex mu : list opml_sort) (σ : opml_symbol) (args : dephlist (opml_arg_sorts σ)), dephlist_foldr (λ a x y, P a ex mu x /\ y) True args -> P (opml_ret_sort σ) ex mu (ocp_app σ args)) → *)
(*   (∀ (s s' : opml_sort) (ex mu : list opml_sort) (φ : OPMLClosedPattern s (s' :: ex) mu), P s (s' :: ex) mu φ → P s ex mu (ocp_ex φ)) → *)
(*   (∀ (s s' : opml_sort) (ex mu : list opml_sort) (φ : OPMLClosedPattern s ex (s' :: mu)), P s ex (s' :: mu) φ → P s ex mu (ocp_mu φ)) → *)
(*   ∀ (o : opml_sort) (l l0 : list opml_sort) (o0 : OPMLClosedPattern o l l0), P o l l0 o0. *)
(* Proof. *)
(*   intros * Hupcast Hbot Hbevar Hbsvar Hfevar Hfsvar Himp Happ Hex Hmu *. *)
(*   dependent induction o0. *)
(*   apply Hupcast. exact IHo0. *)
(*   7: { *)
(*     apply Happ. *)

Goal forall {Σ : OPMLSignature} (s : opml_sort) (ex mu : list opml_sort), OPMLClosedPattern s ex mu -> sigT (uncurry (OPMLClosedPattern s)).
Proof.
  intros.
  exists (ex, mu). simpl. exact X.
  (* Succeed Qed. *)
  Undo To 2.
  refine (existT (ex, mu) X).
Qed.

(* Inductive dephlistIn {A : Type} {F : A -> Type} {x : A} {xs : list A} : F x -> @dephlist A F xs -> Prop := *)
(*   | dhIn_hd x xs : dephlistIn x (dhcons x xs) *)
(*   | dhIn_tl x y ys : dephlistIn x ys -> dephlistIn x (dhcons y ys) *)
(* . *)

Arguments dephlist {_} {_} & _.

Inductive dephlistIn {A : Type} {F : A -> Type} : forall {x : A} {xs : list A}, F x -> @dephlist A F xs -> Prop :=
  | dhIn_hd x xs y ys : @dephlistIn _ _ x (x :: xs) y (dhcons y ys)
  | dhIn_tl x x' xs y y' ys: @dephlistIn _ _ x xs y ys -> @dephlistIn _ _ x (x' :: xs) y (dhcons y' ys)
.

Arguments dephlistIn {_} {_} {_} {_} & _ _.

Goal @dephlistIn _ (bool_rect _ nat bool) true _ 5 ([4; true; 3; 5; false] : @dephlist _ (bool_rect _ nat bool) [true; false; true; true; false]).
Proof.
  repeat constructor.
Qed.

Fixpoint dephlistIn' {A : Type} {F : A -> Type} {x : A} {xs : list A} {ED : EqDecision A} (y : F x) (ys : @dephlist A F xs) : Prop :=
  match ys with
  | dhnil => False
  | @dhcons _ _ x' _ y' ys => match decide (x = x') with
                              | left e => eq_rect x F y _ e = y'
                              | right _ => False
                              end \/ dephlistIn' y ys
  end.

Arguments dephlistIn' {_} {_} {_} {_} {_} & _ _ /.

Goal @dephlistIn' bool (bool_rect _ nat bool) true [true; false; true; true; false] _ 5 ([4; true; 3; 5; false] : @dephlist _ (bool_rect _ nat bool) [true; false; true; true; false]).
Proof.
  cbv. auto.
Qed.

Definition thing {Σ : OPMLSignature} : Type := sigT (λ '(s, ex, mu), OPMLClosedPattern s ex mu).

(* Lemma OPMLClosedPattern_custom_ind : *)
(*   ∀ (Σ : OPMLSignature) (P : ∀ (o : opml_sort) (l l0 : list opml_sort), *)
(*   OPMLClosedPattern o l l0 → Prop), *)
(*   (∀ (ex mu : list opml_sort) (from to : opml_sort) (subsort : opml_subsort from to) (φ : OPMLClosedPattern from ex mu), P from ex mu φ → P to ex mu (ocp_upcast from to subsort φ)) → *)
(*   (∀ (s : opml_sort) (ex mu : list opml_sort), P s ex mu ocp_bot) → *)
(*   (∀ (s : opml_sort) (ex mu : list opml_sort) (dbi : Edbi2 ex s), P s ex mu (ocp_bevar dbi)) → *)
(*   (∀ (s : opml_sort) (ex mu : list opml_sort) (dbi : Edbi2 mu s), P s ex mu (ocp_bsvar dbi)) → *)
(*   (∀ (s : opml_sort) (ex mu : list opml_sort) (x : opml_evar s), P s ex mu (ocp_fevar x)) → *)
(*   (∀ (s : opml_sort) (ex mu : list opml_sort) (X : opml_svar s), P s ex mu (ocp_fsvar X)) → *)
(*   (∀ (s : opml_sort) (ex mu : list opml_sort) (φ1 : OPMLClosedPattern s ex mu), P s ex mu φ1 → ∀ φ2 : OPMLClosedPattern s ex mu, P s ex mu φ2 → P s ex mu (ocp_imp φ1 φ2)) → *)
(*   (∀ (ex mu : list opml_sort) (σ : opml_symbol) (args : dephlist (opml_arg_sorts σ)), (∀ s φ, @dephlistIn' _ _ s _ _ φ args -> P s ex mu φ) -> P (opml_ret_sort σ) ex mu (ocp_app σ args)) → *)
(*   (∀ (s s' : opml_sort) (ex mu : list opml_sort) (φ : OPMLClosedPattern s (s' :: ex) mu), P s (s' :: ex) mu φ → P s ex mu (ocp_ex φ)) → *)
(*   (∀ (s s' : opml_sort) (ex mu : list opml_sort) (φ : OPMLClosedPattern s ex (s' :: mu)), P s ex (s' :: mu) φ → P s ex mu (ocp_mu φ)) → *)
(*   ∀ (o : opml_sort) (l l0 : list opml_sort) (o0 : OPMLClosedPattern o l l0), P o l l0 o0. *)
(* Proof. *)
(*   intros * Hupcast Hbot Hbevar Hbsvar Hfevar Hfsvar Himp Happ Hex Hmu *. *)
(*   destruct o0. *)
(*   (1* dependent induction o0. *1) *)
(*   (1* apply Hupcast. exact IHo0. *1) *)
(*   8: { *)
(*     apply Happ. intros. *)
(*     clear Hupcast Hbot Hbevar Hbsvar Hfevar Hfsvar Himp Happ Hex Hmu. *)
(*     (1* generalize dependent args. *1) *)
(*     (1* fix IHargs 1. destruct args; intros. *1) *)
(*     induction args; intros. *)
(*     simpl in H. destruct H. *)
(*     simpl in H. destruct H. *)
(*     2: apply IHargs, H. *)
(*     case_match. 2: destruct H. *)

(* Goal forall {Σ : OPMLSignature} (P : thing -> Prop), forall ex mu σ args, (forall s φ, @dephlistIn' _ _ s (opml_arg_sorts σ) _ φ args -> P (existT (s, ex, mu) φ)) -> P (existT (opml_ret_sort σ, ex, mu) (ocp_app σ args)). *)
(* Proof. *)
(*   intros. *)
(*   dependent induction args. *)

Inductive SubPatternOf {Σ : OPMLSignature} : thing -> thing -> Prop :=
  | sp_upcast from to subsort ex mu φ : SubPatternOf (existT (from, ex, mu) φ) (existT (to, ex, mu) (ocp_upcast from to subsort φ))
  | sp_imp_l s ex mu φ1 φ2 : SubPatternOf (existT (s, ex, mu) φ1) (existT (s, ex, mu) (ocp_imp φ1 φ2))
  | sp_imp_r s ex mu φ1 φ2 : SubPatternOf (existT (s, ex, mu) φ2) (existT (s, ex, mu) (ocp_imp φ1 φ2))
  | sp_ex s s' ex mu φ : SubPatternOf (existT (s, s' :: ex, mu) φ) (existT (s, ex, mu) (ocp_ex φ))
  | sp_mu s s' ex mu φ : SubPatternOf (existT (s, ex, s' :: mu) φ) (existT (s, ex, mu) (ocp_mu φ))
  | sp_app s ex mu σ args (φ : OPMLClosedPattern s ex mu) : @dephlistIn _ _ s (opml_arg_sorts σ) φ args -> SubPatternOf (existT (s, ex, mu) φ) (existT (opml_ret_sort σ, ex, mu) (ocp_app σ args))
.

Definition ex_signature : OPMLSignature.
Proof.
  unshelve esplit.
  unshelve esplit. exact nat. exact le. 1-3: typeclasses eauto.
  unshelve esplit. 1-2: exact (const nat). 1-6: typeclasses eauto.
  unshelve esplit. exact bool. 1-2: typeclasses eauto.
  intros []; simpl. exact [1; 3; 2]%list. exact [2; 0]%list.
  intros []; simpl. exact 0. exact 4.
Defined.

Goal @SubPatternOf ex_signature (existT (3, []%list, []%list) ocp_bot) (existT (0, []%list, []%list) (@ocp_app ex_signature _ _ true [ocp_bot; ocp_bot; ocp_bot])).
Proof.
  apply (@sp_app ex_signature 3 [] [] true [ocp_bot; ocp_bot; ocp_bot]).
  repeat constructor.
Qed.

Definition SubPatternOf' {Σ : OPMLSignature} : relation thing.
Proof.
  intros [[[s ex] mu] φ] [[[s' ex'] mu'] φ'].
  destruct φ'.
  2-6: exact False.
  - refine (match (decide ((s, ex, mu) = (from, ex0, mu0))) with
            | left e => eq_rect (s, ex, mu) (uncurry3 OPMLClosedPattern) φ _ e = φ'
            | right _ => False
            end).
  - refine (match (decide ((s, ex, mu) = (s0, ex0, mu0))) with
            | left e => eq_rect (s, ex, mu) (uncurry3 OPMLClosedPattern) φ _ e = φ'1 \/ eq_rect (s, ex, mu) (uncurry3 OPMLClosedPattern) φ _ e = φ'2
            | right _ => False
            end).
  - refine (match (decide ((ex, mu) = (ex0, mu0))) with
            | left e => let asd : OPMLClosedPattern s ex0 mu0 := (eq_rect (ex, mu) (uncurry (OPMLClosedPattern s)) φ _ e) in dephlistIn' asd args
            | right _ => False
            end).
  - refine (match (decide ((s, ex, mu) = (s0, s' :: ex0, mu0))) with
            | left e => eq_rect (s, ex, mu) (uncurry3 OPMLClosedPattern) φ _ e = φ'
            | right _ => False
            end).
  - refine (match (decide ((s, ex, mu) = (s0, ex0, s' :: mu0))) with
            | left e => eq_rect (s, ex, mu) (uncurry3 OPMLClosedPattern) φ _ e = φ'
            | right _ => False
            end).
Defined.

Arguments SubPatternOf' {_} _ _ /.

Goal forall {Σ : OPMLSignature}, well_founded SubPatternOf'.
Proof.
  intro.
  unfold well_founded.
  fix pleasework 1.
  intros [[[s ex] mu] a].
  induction a.
  2-6: split; intros [[[s' ex'] mu'] y] H; simpl in H; destruct H.
  - split; intros [[[s' ex'] mu'] y] H; simpl in H.
    case_match.
    rewrite (eq_existT_curried e H). exact IHa.
    destruct H.
  - split; intros [[[s' ex'] mu'] y] H; simpl in H.
    case_match.
    destruct H.
    rewrite (eq_existT_curried e H). exact IHa1.
    rewrite (eq_existT_curried e H). exact IHa2.
    destruct H.
  - split; intros [[[s' ex'] mu'] y] H; simpl in H.
    case_match.
    2: destruct H.
    induction args.
    destruct H.
    destruct H.
    2: apply IHargs, H.
    clear IHargs.
    case_match.
    2: destruct H.
    enough (@existT _ (uncurry3 OPMLClosedPattern) (s', ex', mu') y = existT (x, ex, mu) f).
    rewrite H2.
    (* It doesn't. And I don't know why. *)
    (* apply pleasework. Guarded. *)
    Search eq_rect.
    Search (eq_rect _ _ (eq_rect _ _ _ _ _) _ _).
    pose proof (eq_existT_curried e0 H).
Abort.

Goal forall {Σ : OPMLSignature}, well_founded SubPatternOf.
Proof.
  intros.
  unfold well_founded.
  fix pleasework 1.
  intros. destruct a as [[[s ex] mu] a].
  destruct a.
  8: {
    split.
    dependent induction args; intros.
    - (*inversion H; subst.*)
      dependent induction H.

      inversion_sigma.
      Search hyp:eq_rect.
      Search hyp:eq_dep1.


  intros. split.
  destruct a as [[[s ex] mu] a].
  induction a; intros.
  7: {
    dependent induction H.
  intros.
  Search Acc.
  (* dependent induction H. *)
  (* inversion H; subst. *)
  (* split. intros. *)
  (* inversion H0; subst. *)
  (* destruct a as [[[s ex] mu] a]. *)
  (* dependent induction a. *)
  (* - inversion H. *)
  (*   + inversion_sigma. *) 
  (*     About eq_rect. *)

  (* destruct y as [[[s ex] mu] y]. dependent induction y. *)
  (* dependent induction H. *)
Admitted.


(* Equations? measure_OCP `(φ : @OPMLClosedPattern Σ s xs ys) : nat := *)
(*   measure_OCP (ocp_upcast from to subsort φ) => measure_OCP φ ; *)
(*   measure_OCP ocp_bot => 0 ; *)
(*   measure_OCP (ocp_bevar dbi) => measure_Edbi2 dbi ; *)
(*   measure_OCP (ocp_bsvar dbi) => measure_Edbi2 dbi ; *)
(*   measure_OCP (ocp_fevar x) => 0 ; *)
(*   measure_OCP (ocp_fsvar X) => 0 ; *)
(*   measure_OCP (ocp_imp φ1 φ2) => measure_OCP φ1 + measure_OCP φ2 ; *)
(*   measure_OCP (ocp_app σ args) => _ (*dephlist_foldr (λ _ a c, measure_OCP a + c) 0 args*) ; *)
(*   (1* measure_OCP (ocp_app σ dhnil) => 0 ; *1) *)
(*   (1* measure_OCP (ocp_app σ (dhcons x xs)) => measure_OCP x + measure_OCP (ocp_app σ xs) ; *1) *)
(*   measure_OCP (ocp_ex φ) => measure_OCP φ ; *)
(*   measure_OCP (ocp_mu φ) => measure_OCP φ ; *)
(*   . *)
(* Proof. *)
(*   exact (dephlist_foldr (λ _ c a, measure_OCP Σ _ xs ys c + a) 0 args). *)
(* Defined. *)
(*   (1* refine (dephlist_foldr _ 0 args). *1) *)
(*   (1* intros. apply plus. eapply measure_OCP. exact X. exact H. *1) *)
(* (1* Defined. *1) *)

Section asd.
Context {Σ : OPMLSignature}.

Instance wfspo : WellFounded SubPatternOf. Admitted.

(* Definition dephlist_rect' : ∀ (A : Type) (F : A → Type) (P : ∀ l : list A, dephlist l → Type), *)
(*   P []%list [] -> *)
(*   (∀ (x : A) (xs : list A) (f : F x) (d : dephlist xs), dephlistIn f (dhcons f d) -> P xs d -> P (x :: xs) (dhcons f d)) -> *)
(*   ∀ (l : list A) (d : dephlist l), P l d. *)
(* Proof. *)
(*   intros. *)
(*   dependent induction d. *)
(*   exact X. *)
(*   apply X0. 2: exact IHd. *)
(*   left. *)
(* Defined. *)

Fixpoint dephlist_map' {A : Type} {F G : A -> Type} {l : list A} (xs : @dephlist A F l) (f : forall (a : A) (x : F a), dephlistIn x xs -> G a) {struct xs} : @dephlist A G l.
Proof.
  dependent destruction xs. left.
  right. eapply f0. left.
  eapply dephlist_map'.
  intros.
  eapply f0.
  right. exact H.
Defined.

Goal @dephlist _ (bool_rect _ nat bool) [true; false; false; true].
Proof.
  epose (@dephlist_map' _ (bool_rect _ nat bool) (bool_rect _ nat bool) [true; false; false; true] [3; true; false; 6]).
  apply d.
  intros.
  destruct a; simpl in x |- *. exact (x + 1). exact (negb x).
Defined dhlmptest.
Compute dhlmptest.

Axiom tobesolved : forall `(sub a b c), `(sub a b (x :: c)).

#[tactic=idtac]
Equations? test (base : thing) (ex' : list opml_sort) (sub0 : sub ex' ((projT1 base).1.2) ((projT1 base).2)) : OPMLClosedPattern ((projT1 base).1.1) ex' ((projT1 base).2) by wf base SubPatternOf := 
  test _ _ _ := _
  (* test (existT _ (ocp_upcast _ _ _ _)) _ sub0 := _ ; *)
  (* test (existT _ (ocp_bot))          _ sub0 := _ ; *)
  (* test (existT _ (ocp_bevar _))      _ sub0 := _ ; *)
  (* test (existT _ (ocp_bsvar _))      _ sub0 := _ ; *)
  (* test (existT _ (ocp_fevar _))      _ sub0 := _ ; *)
  (* test (existT _ (ocp_fsvar _))      _ sub0 := _ ; *)
  (* test (existT _ (ocp_imp _ _))      _ sub0 := _ ; *)
  (* test (existT _ (ocp_app _ _))      _ sub0 := _ ; *)
  (* test (existT _ (ocp_ex _))         _ sub0 := _ ; *)
  (* test (existT _ (ocp_mu _))         _ sub0 := _ ; *)
.
Proof.
  destruct base as [[[s ex] mu] base].
  simpl in *.
  dependent destruction base.
  - eapply ocp_upcast. eauto. apply (test (existT (from, ex, mu) base)). simpl. auto. constructor.
  - apply ocp_bot.
  - dependent destruction sub0.
    + apply ocp_bevar, edbis, dbi.
    + dependent destruction dbi.
      * auto.
      * apply ocp_bevar, dbi.
    + dependent destruction dbi.
      * apply ocp_bevar. left.
      * epose (test (existT (s, ys, mu) (ocp_bevar dbi)) _ sub0 _).
        simpl in o.
        epose (test (existT (s, xs, mu) o) _ subp _).
        simpl in o0. exact o0.
        Unshelve.
        2: { subst o. simpl.
  - apply ocp_bsvar. auto.
  - apply ocp_fevar. auto.
  - apply ocp_fsvar. auto.
  - apply ocp_imp.
    + apply (test (existT (s, ex, mu) base1)). simpl. auto. constructor.
    + apply (test (existT (s, ex, mu) base2)). simpl. auto. constructor.
  - apply ocp_app. unshelve eapply dephlist_map'. 2: exact args.
    intros. simpl in x. apply (test (existT (a, ex, mu) x)). simpl. auto.
    constructor. auto.
  - eapply ocp_ex. apply (test (existT (s, s' :: ex, mu) base)).
    simpl. apply subs. auto.
    constructor.
  - eapply ocp_mu. apply (test (existT (s, ex, s' :: mu) base)).
    simpl. apply tobesolved. auto.
    constructor.

Abort.

Program Fixpoint test (base : thing) (ex' : list opml_sort) {wf SubPatternOf base} : sub ex' ((projT1 base).1.2) ((projT1 base).2) -> OPMLClosedPattern ((projT1 base).1.1) ex' ((projT1 base).2) := _.

End asd.
(* Program Fixpoint test `(base : @OPMLClosedPattern Σ s ex0 mu0) `(sub ex1 ex0 mu0) {wf SubPatternOf (existT (s, ex0, mu0) base)} : OPMLClosedPattern s ex1 mu0 := _. *) 

#[tactic=idtac]
Equations? test {Σ : OPMLSignature} {s : opml_sort} {ex ex' mu : list opml_sort} (base : OPMLClosedPattern s ex mu) (σ : sub ex' ex mu) : OPMLClosedPattern s ex' mu by wf (existT (s, ex, mu) base) SubPatternOf :=
test (s := s) (ocp_upcast from s H φ) σ := ocp_upcast from s H (test φ σ) ;
test ocp_bot _ := ocp_bot ;
test (ocp_bevar dbi) subp := ocp_bevar (edbis dbi) ;
test (ocp_bevar edbi0) (subz repl) := repl ;
test (ocp_bevar (edbis dbi)) (subz repl) := ocp_bevar dbi ;
test (ocp_bevar edbi0) (subs σ) := ocp_bevar edbi0 ;
test (ocp_bevar (edbis dbi)) (subs σ) := _ ;
(* test (ocp_bevar (edbis dbi)) (subs σ) := test (test (ocp_bevar dbi) σ) subp ; *)
test (ocp_bsvar dbi) _ := ocp_bsvar dbi ;
test (ocp_fevar ev) _ := ocp_fevar ev ;
test (ocp_fsvar ev) _ := ocp_fsvar ev ;
test (ocp_imp φ1 φ2) σ := ocp_imp (test φ1 σ) (test φ2 σ) ;
test (ocp_app sy args) σ := ocp_app sy (dephlist_map (λ s' φ, _) args) ;
(* test (ocp_app sy args) σ := ocp_app sy (dephlist_map (λ s' φ, test φ σ) args) ; *)
test (ocp_ex φ) σ := ocp_ex (test φ (subs σ)) ;
test (ocp_mu φ) σ := ocp_mu (test φ _) ;
.
Proof.
  - eapply test. 2: exact subp.
    eapply test. exact (ocp_bevar dbi). exact σ.
  - eapply test. exact φ. exact σ.
  - apply trustmebro. exact σ.
Defined.
    
(* Proof. *)
(*   2: { *)
(*     eapply test. 2: exact σ. exact φ. Guarded. *)

Fixpoint test `(base : @OPMLClosedPattern Σ s ex0 mu0) `(sub ex1 ex0 mu0) : OPMLClosedPattern s ex1 mu0. 
Proof.
  inversion_clear base; subst.
  3: {
    inversion sub0; subst.
    - apply ocp_bevar, edbis, dbi.
    - inversion dbi; subst.
      + exact H.
      + apply ocp_bevar, H3.
    - inversion dbi; subst.
      + apply ocp_bevar, edbi0.
      + epose (test _ _ _ _ (ocp_bevar H3) _ H).
        epose (test _ _ _ _ o _ subp).
        exact o0. Fail Guarded.
  }
  7: {
    eapply ocp_app, dephlist_map, args.
    intros. simpl in H. eapply test; eauto.
    Fail Guarded.
  }
  7: {
    eapply ocp_ex.
    epose (test _ _ _ _ φ _ (subs sub0)).
    exact o. Fail Guarded.
  }
  7: {
    eapply ocp_mu.
    epose (test _ _ _ _ φ). admit.
  }

  (* refine (match base with *)
  (*         | ocp_upcast from to subsort φ => _ (*test _ _ _ _ φ _ sub0*) *)
  (*         | ocp_bot => ocp_bot *)
  (*         | ocp_bevar dbi => _ *)
  (*         | ocp_bsvar dbi => ocp_bsvar dbi *)
  (*         | ocp_fevar x => ocp_fevar x *)
  (*         | ocp_fsvar X => ocp_fsvar X *)
  (*         | @ocp_imp _ s ex mu φ1 φ2 => _ *)
  (*         | @ocp_app _ ex mu σ args => _ *)
  (*         | @ocp_ex _ s s' ex mu φ => _ *)
  (*         | @ocp_mu _ s s' ex mu φ => _ *)
  (*         end). *)
  (*         admit. *)
Abort.

Goal forall `(base : @OPMLClosedPattern Σ s ex0 mu0) `(sub ex1 ex0 mu0), OPMLClosedPattern s ex1 mu0.
Proof.
  intros.
  (* generalize dependent ex1. *)
  (* induction base; intros. *)
  (* generalize dependent base. *)
  (* generalize dependent s. *)
  (* fix IH 2. *)
  (* inversion_clear 1; subst. *)
  dependent induction base.
  - eapply ocp_upcast; eauto.
  - apply ocp_bot.
  - dependent induction sub0.
    + apply ocp_bevar, edbis, dbi.
    + dependent induction dbi.
      * exact o.
      * apply ocp_bevar, dbi.
    + clear IHsub0. dependent induction dbi.
      * apply ocp_bevar. left.
      * destruct ys.
        ** inversion dbi.
        ** specialize (IHdbi ys o eq_refl). admit.
  - apply ocp_bsvar; auto.
  - apply ocp_fevar; auto.
  - apply ocp_fsvar; auto.
  (* - apply ocp_imp; apply IH; [exact φ1 | exact φ2]. *)
  - apply ocp_imp; [apply IHbase1 | apply IHbase2]; auto.
  - apply ocp_app. admit.
    (* eapply dephlist_map. apply IH. exact args. Guarded. *)
  (* - specialize (IHbase (s' :: ex1) (subs sub0)). epose proof ocp_ex IHbase. exact H. *)
  - eapply ocp_ex. eauto using subs.
  - eapply ocp_mu. eauto. admit.
Abort.

Goal forall `(base : @OPMLClosedPattern Σ s ex0 mu0) `(dbi : Edbi2 ex0 s') `(repl : OPMLClosedPattern s' ex0 mu0), OPMLClosedPattern s ex0 mu0.
Proof.
  intros.
  dependent induction base.
  (* generalize dependent base. *)
  (* generalize dependent s. *)
  (* generalize dependent dbi. *)
  (* generalize dependent ex0. *)
  (* fix IH 5. *)
  (* inversion_clear 3; subst. *)
  - eapply ocp_upcast; eauto.
  - apply ocp_bot.
  - inversion dbi; subst.
    + inversion dbi0; subst.
      * exact repl.
      * apply ocp_bevar. exact dbi0. (*Not happy with this.*)
      (* * admit. *)
    + inversion dbi0; subst.
      * apply ocp_bevar. exact dbi0.
      * admit.
  - apply ocp_bsvar; auto.
  - apply ocp_fevar; auto.
  - apply ocp_fsvar; auto.
  - apply ocp_imp; auto.
  - apply ocp_app. eapply dephlist_map; [apply IH |]; auto.
  - eapply ocp_ex. eapply IH. 2: exact (edbis dbi). 2: exact φ. admit.
  - eapply ocp_mu. admit.
Abort.

(* Goal forall `(base : @OPMLClosedPattern Σ s (s' :: ex0) mu0) `(repl : OPMLClosedPattern s' ex1 mu1) `(dbi : Edbi2 ex1 s'), OPMLClosedPattern s ex1 mu1. *)
(* Proof. *)
(*   intros. *)
(*   (1* generalize dependent base. *1) *)
(*   (1* generalize dependent s. *1) *)
(*   (1* fix IH 2. *1) *)
(*   (1* inversion_clear 1; subst. *1) *)
(*   inversion_clear base; subst. *)
(*   - eapply ocp_upcast; eauto. *)
(*   - apply ocp_bot. *)
(*   - inversion dbi; subst. *)
(*     + inversion dbi0; subst. *)
(*       * exact repl. *)
(*       * apply ocp_bevar. *)
(* Abort. *)

(* Goal forall {Σ : OPMLSignature} (ex mu ex' mu' : list opml_sort) (s s' : opml_sort) (in_what : OPMLClosedPattern s ex mu) (change_what : OPMLClosedPattern s' ex' mu') (dbi : Edbi2 ex' s'), OPMLClosedPattern s ex mu. *)
(* Proof. *)
(*   intros. *)
(*   induction in_what. *)
(*   3: { *)
(*   - apply (ocp_upcast from). auto. *)

Definition test : OPMLSignature.
Proof.
  unshelve esplit.
  unshelve esplit. exact nat. exact le. 1-3: typeclasses eauto.
  unshelve esplit. 1-2: exact (const nat). 1-6: typeclasses eauto.
  unshelve esplit. exact bool. 1-2: typeclasses eauto.
  intros []. exact [1;3;2]. exact [2;0].
  intros []. exact 0. exact 4.
Defined.

(* Check @ocp_bevar test [_;_;_] _ 2 _. *)
(* Proof shouldn't be in type. *)

(* Check @ocp_bevar test [_;_;_] _ 2. *)
(* Check @ocp_ex test _ _ _ _ (@ocp_bevar test [_] _ 0) : @OPMLClosedPattern test 4 [] []. *)
(* Can't figure out list. *)

Check @ocp_ex test _ _ _ _ (ocp_bevar edbi0) : @OPMLClosedPattern test 4 [] [].
Check @ocp_bevar test _ _ _ (edbis (edbis edbi0)).
(* Check @ocp_bevar test _ _ _ (fin_to_edbi2 2%fin). *)
(* Conversion functions might not work, but it's implicit. *)

(* Check @ocp_bevar test [_;_;_] _ 2 _. *)
(* Proof shouldn't be in type. *)

(* Check @ocp_bevar test [_;_;_] _ 2. *)
(* Check @ocp_ex test _ _ _ _ (@ocp_bevar test [_] _ 0) : @OPMLClosedPattern test 4 [] []. *)
(* Can't figure out list. *)

Check @ocp_ex test _ _ _ _ (ocp_bevar edbi0) : @OPMLClosedPattern test 4 [] [].
Check @ocp_bevar test _ _ _ (edbis (edbis edbi0)).
(* Check @ocp_bevar test _ _ _ (fin_to_edbi2 2%fin). *)
(* Conversion functions might not work, but it's implicit. *)

Definition test2 : @OPMLPattern test 4.
Proof.
  apply (@op_app test false).
  simpl. right. constructor. right.
  apply (@op_app test true).
  simpl. repeat constructor.
  left.
Defined.
Print test2.

Check @op_app test false [op_bot; @op_app test true [op_bot; op_bot; op_bot]].

Check @ocp_app test _ _ false [ocp_bot; ocp_bot] : @OPMLClosedPattern test 4 [] [].
(* Check @ocp_ex test 12 _ _ _ (ocp_ex (ocp_bevar 4)) : @OPMLClosedPattern test 12 [0;1;2] []. *)
Check @ocp_imp test 1 _ _ (ocp_bevar 3) (ocp_bevar 4) : @OPMLClosedPattern test 1 [0;0;0;1;1] [].

Fixpoint OPMLPattern_size
    {Σ : OPMLSignature}
    (φ : OPMLPattern)
    : nat :=
match φ with
| op_bot _ => 1
| op_bevar _ => 1
| op_bsvar _ => 1
| op_fevar _ _ => 1
| op_fsvar _ _ => 1
| op_imp φ1 φ2 => 1 + OPMLPattern_size φ1 + OPMLPattern_size φ2
| op_upcast _ _ _ φ' => 1 + OPMLPattern_size φ'
| op_ex _ φ' => 1 + OPMLPattern_size φ'
| op_mu _ φ' => 1 + OPMLPattern_size φ'
| op_app s args => 1 + sum_list_with OPMLPattern_size args
end.

(* A better induction principle for OPMLPattern *)
Lemma OPMLPattern_deep_ind
    {Σ : OPMLSignature}
    (P : OPMLPattern -> Prop)
    (Hupcast :
        forall
        (from to : opml_sort)
        (subsort : opml_subsort from to)
        (φ : OPMLPattern),
        P φ ->
        P (op_upcast from to subsort φ)
    )
    (Hbot :
        forall s : opml_sort,
        P (op_bot s)
    )
    (Hbe :
        forall dbi : Edbi,
        P (op_bevar dbi)
    )
    (Hbs :
        forall dbi : Sdbi,
         P (op_bsvar dbi)
    )
    (Hfe : 
        forall
        (s : opml_sort)
        (x : opml_evar s),
        P (op_fevar s x)
    )
    (Hfs :
        forall
        (s : opml_sort)
        (X : opml_svar s),
        P (op_fsvar s X)
    )
    (Himp :
        forall
        φ1 : OPMLPattern,
        P φ1 ->
        forall
        φ2 : OPMLPattern,
        P φ2 -> P (op_imp φ1 φ2)
    )
    (Happ :
        forall
        (s : opml_symbol)
        (args : list OPMLPattern),
        (forall φ'', φ'' ∈ args -> P φ'') ->
        P (op_app s args)
    )
    (Hex :
        forall
        (s : opml_sort)
        (φ : OPMLPattern),
        P φ ->
        P (op_ex s φ)
    )
    (Hmu :
        forall
        (s : opml_sort)
        (φ : OPMLPattern),
        P φ ->
        P (op_mu s φ)
    ):
    forall φ' : OPMLPattern,
    P φ'
.
Proof.
    intros φ'.
    remember (OPMLPattern_size φ') as sz.
    assert (Hsz: OPMLPattern_size φ' <= sz) by lia.
    clear Heqsz.
    revert φ' Hsz.
    induction sz;
        intros φ' Hsz.
    {
        destruct φ'; cbn in Hsz; exfalso; lia.
    }
    destruct φ'; cbn in Hsz.
    { apply Hupcast. apply IHsz. lia. }
    { apply Hbot. }
    { apply Hbe. }
    { apply Hbs. }
    { apply Hfe. }
    { apply Hfs. }
    { apply Himp; apply IHsz; lia. }
    {
        apply Happ.
        intros φ'' Hϕ''.
        apply IHsz.
        cut (OPMLPattern_size φ'' <= sum_list_with OPMLPattern_size args).
        { intros H. lia. }
        apply sum_list_with_in.
        exact Hϕ''.
    }
    { apply Hex. apply IHsz. lia. }
    { apply Hmu. apply IHsz. lia. }
Qed.
