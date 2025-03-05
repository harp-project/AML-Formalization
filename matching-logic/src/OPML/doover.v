From MatchingLogic.OPML Require Export OpmlSignature.
From stdpp Require Import base tactics list list_numbers.
Set Transparent Obligations.
From Coq Require Import Program.Equality.
From Equations Require Export -(notations) Equations.
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

(* Check [1; 2; true; 3; false]%hlist : hlist (bool_rect _ nat bool) [true; true; false; true; false]. *)

(* Definition hlistIn {A : Type} {ED : EqDecision A} {F : A -> Type} {x : A} {xs : list A} (y : F x) (ys : hlist F xs) : Prop := *)
(*   match ys with *)
(*   | hnil => False *)
(*   | @hcons _ _ x' _ y' ys' => match (decide (x = x')) with *)
(*                               | left e => (eq_rect _ _ y _ e = y') *)
(*                               | _ => False *)
(*                               end *)
(*   end. *)

(* Arguments hlistIn {_} {_} {_} {_} {_} & _ !_. *)

Inductive Dbi {Σ : OPMLSignature} : opml_sort -> list opml_sort -> Type :=
  | dbiz {x} {xs} : Dbi x (x :: xs)
  | dbis {x y} {xs} : Dbi y xs -> Dbi y (x :: xs)
.

(* Fixpoint dbi_depth {Σ : OPMLSignature} {s} {xs} (x : Dbi s xs) : nat := *)
(*   match x with *)
(*   | dbiz => 0 *)
(*   | dbis e => 1 + dbi_depth e *)
(*   end. *)

(* Arguments dbi_depth {_} {_} {_} !_. *)

Inductive OPMLPattern {Σ : OPMLSignature} : opml_sort -> list opml_sort -> list opml_sort -> Type :=
  | op_bot {s} {ex mu} : OPMLPattern s ex mu
  | op_bevar {s} {ex mu} : Dbi s ex -> OPMLPattern s ex mu
  | op_app {ex mu} (σ : opml_symbol) : hlist (OPMLPattern ^~ ex ^~ mu) (opml_arg_sorts σ) -> OPMLPattern (opml_ret_sort σ) ex mu
  | op_ex {s s'} {ex mu} : OPMLPattern s (s' :: ex) mu -> OPMLPattern s ex mu
.

(* Fixpoint depth {Σ : OPMLSignature} {s : opml_sort} {ex mu : list opml_sort} (x : OPMLPattern s ex mu) : nat := *)
(*   match x with *)
(*   | op_bot => 0 *)
(*   | op_bevar e => dbi_depth e *)
(*   | op_app σ l => hlist_rect 0 (fun _ _ y _ z => 1 + depth y + z) l *)
(*   | op_ex φ => 1 + depth φ *)
(*   end. *)

(* Arguments depth {_} {_} {_} {_} !_. *)

(* Definition expat {Σ : OPMLSignature} : Type := sigT (uncurry3 OPMLPattern). *)

(* Definition SubTree {Σ : OPMLSignature} : relation (sigT (uncurry3 OPMLPattern)). *)
(* Proof. *)
(*   intros [[[s ex] mu] x] [[[s' ex'] mu'] y]. *)
(*   simpl in x, y. *)
(*   destruct_with_eqn y. *)
(*   exact False. *)
(*   exact False. *)
(*   refine (match decide ((ex, mu) = (ex0, mu0)) with *)
(*           | left e => let u := eq_rect (ex, mu) (uncurry (OPMLPattern s)) x _ e : OPMLPattern s ex0 mu0 in hlistIn u h *)
(*           | _ => False *)
(*           end). *)
(*   refine (match decide ((s, ex, mu) = (s0, s' :: ex0, mu0)) with *)
(*           | left e => eq_rect (s, ex, mu) (uncurry3 OPMLPattern) x _ e = o *)
(*           | _ => False *)
(*           end). *)
(* Defined. *)

(* Arguments SubTree {_} _ _ /. *)

(*Goal forall {Σ : OPMLSignature}, well_founded SubTree. *)
(*Proof. *)
(*  intros. *)
(*  unfold well_founded. *)
(*  intros [[[s ex] mu] a]. simpl in a. *)
(*  revert s ex mu a. *)
(*  fix IH 4. *)
(*  intros ? ? ? []. *)
(*  split. intros [[[s' ex'] mu'] y] H. simpl in H. destruct H. *)
(*  split. intros [[[s' ex'] mu'] y] H. simpl in H. destruct H. *)
(*  split. intros [[[s' ex'] mu'] y] H. simpl in H. *)
(*  case_match. 2: destruct H. *)
(*  destruct h. simpl in H. destruct H. *)
(*  simpl in H. case_match. 2: destruct H. *)
(*  assert (existT (s', ex', mu') y = existT (x, ex0, mu0) o). { *)
(*    eapply eq_existT_curried. *)
(*    Search eq_rect. *)
(*    admit. *)
(*  } *)
(*  rewrite H2. *)
(*  apply IH. Guarded. *)
(*  split. intros [[[s'' ex'] mu'] y] H. simpl in H. *)
(*  case_match. 2: destruct H. *)
(*  epose proof eq_existT_curried e H. rewrite H1. *)
(*  apply IH. Guarded. *)
(*Abort. *)

(* Inductive sub {Σ : OPMLSignature} : list opml_sort -> list opml_sort -> list opml_sort -> Type := *)
(*   | subp {xs mu : list opml_sort} {x : opml_sort} : sub (x :: xs) xs mu *)
(*   | subz {xs mu : list opml_sort} {x : opml_sort} : OPMLPattern x xs mu -> sub xs (x :: xs) mu *)
(*   | subs {xs ys mu : list opml_sort} {x : opml_sort} : sub xs ys mu -> sub (x :: xs) (x :: ys) mu *)
(*   . *)

(* Check subs (subs (subs (subz op_bot))). *)

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

(* Goal forall {Σ : OPMLSignature} {s s0 s1 s2 s3 s4 : opml_sort} , Dbi s [s0; s1; s4] -> Dbi s [s0; s1; s2; s3; s4]. *)
(* Proof. *)
(*   intros. *)
(*   pose (@inc_dbi _ s [s0; s1] [s2; s3] [s4]). *)
(*   simpl in d. *)
(*   apply d, H. *)
(* Qed. *)

Fixpoint inc_evar {Σ : OPMLSignature} {s} {ex ex' ex'' mu} (base : OPMLPattern s (ex ++ ex'') mu) : OPMLPattern s (ex ++ ex' ++ ex'') mu.
Proof.
  revert s ex ex' ex'' mu base.
  fix IH 6.
  intros.
  dependent destruction base.
  - exact op_bot.
  - apply op_bevar, inc_dbi, d.
  - apply op_app.
    induction h; simpl.
    + left.
    + right.
      * apply inc_evar, f.
      * apply IHh.
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
  (* remember base. *)
  dependent destruction base.
  - exact op_bot.
  - eapply sub_evar; eauto.
  - apply op_app.
    induction h.
    + left.
    + right.
      * eapply bevar_subst; eauto.
      * apply IHh.
  - eapply op_ex.
    rewrite app_comm_cons.
    eapply bevar_subst.
    rewrite <- app_comm_cons. all: eauto.
Defined.

Arguments bevar_subst {_} {_} {_} {_} {_} {_} !_ _.
