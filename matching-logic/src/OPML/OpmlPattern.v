(* From Coq Require Import ssreflect ssrfun ssrbool. *)
From MatchingLogic.OPML Require Export OpmlSignature.
From stdpp Require Export base list list_numbers fin.
(* This is unset by stdpp. We need to set it again.*)
Set Transparent Obligations.

Set Default Proof Mode "Classic".

(* De Bruijn indices for element and set variables*)
Record Edbi := { edbi_n : nat; }.
Record Sdbi := { sdbi_n : nat; }.

Inductive dephlist {A : Type} {F : A -> Type} : list A -> Type :=
  | dhnil : dephlist []
  | dhcons {x : A} {xs : list A} : F x -> dephlist xs -> dephlist (x :: xs)
.

Inductive OPMLPattern {Σ : OPMLSignature} : opml_sort -> Type :=
  | op_upcast (from to : opml_sort) (subsort : opml_subsort from to) (φ : OPMLPattern from) : OPMLPattern to
  | op_bot {s : opml_sort} : OPMLPattern s
  | op_bevar {s : opml_sort} (dbi : Edbi) : OPMLPattern s
  | op_bsvar {s : opml_sort} (dbi : Sdbi) : OPMLPattern s
  | op_fevar {s : opml_sort} (x : opml_evar s) : OPMLPattern s
  | op_fsvar {s : opml_sort} (X : opml_svar s) : OPMLPattern s
  | op_imp {s : opml_sort} (φ1 φ2 : OPMLPattern s) : OPMLPattern s
  | op_app (σ : opml_symbol) (args : @dephlist _ OPMLPattern (opml_arg_sorts σ)) : OPMLPattern (opml_ret_sort σ)
  | op_ex {s : opml_sort} (φ : OPMLPattern s) : OPMLPattern s
  | op_mu {s : opml_sort} (φ : OPMLPattern s) : OPMLPattern s
.

Inductive Edbi2 {Σ : OPMLSignature} : list opml_sort -> opml_sort -> Set :=
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
  | ocp_ex {s s' : opml_sort} {ex mu : list opml_sort} (φ : OPMLClosedPattern s (s' :: ex) mu) : OPMLClosedPattern s ex mu
  | ocp_mu {s s' : opml_sort} {ex mu : list opml_sort} (φ : OPMLClosedPattern s ex (s' :: mu)) : OPMLClosedPattern s ex mu
.

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

Notation "[ ]" := dhnil (format "[ ]").
Notation "[ x ]" := (dhcons x dhnil).
Notation "[ x ; y ; .. ; z ]" := (dhcons x (dhcons y .. (dhcons z dhnil) ..)).

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
