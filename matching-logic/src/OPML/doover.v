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

Definition hlistIn {A : Type} {ED : EqDecision A} {F : A -> Type} {x : A} {xs : list A} (y : F x) (ys : hlist F xs) : Prop :=
  match ys with
  | hnil => False
  | @hcons _ _ x' _ y' ys' => match (decide (x = x')) with
                              | left e => (eq_rect _ _ y _ e = y')
                              | _ => False
                              end
  end.

Arguments hlistIn {_} {_} {_} {_} {_} & _ !_.

Inductive OPMLPattern {Σ : OPMLSignature} : opml_sort -> list opml_sort -> list opml_sort -> Type :=
  | op_bot {s} {ex} {mu} : OPMLPattern s ex mu
  | op_app {ex} {mu} (σ : opml_symbol) : hlist (OPMLPattern ^~ ex ^~ mu) (opml_arg_sorts σ) -> OPMLPattern (opml_ret_sort σ) ex mu
  | op_ex {s} {s'} {ex} {mu} : OPMLPattern s (s' :: ex) mu -> OPMLPattern s ex mu
.

Fixpoint subterms {Σ : OPMLSignature} {s : opml_sort} {ex mu : list opml_sort} (x : OPMLPattern s ex mu) : nat :=
  match x with
  | op_bot => 0
  | op_app σ l => hlist_rect 0 (fun _ _ y _ z => subterms y + z) l
  | op_ex φ => subterms φ
  end.

Arguments subterms {_} {_} {_} {_} !_.

Definition expat {Σ : OPMLSignature} : Type := sigT (uncurry3 OPMLPattern).

Definition SubTree {Σ : OPMLSignature} (x : expat) (y : expat) : Prop.
Proof.
  destruct x as [[[s ex] mu] x], y as [[[s' ex'] mu'] y].
  destruct_with_eqn y.
  exact False.
  refine (match decide ((ex, mu) = (ex0, mu0)) with
          | left e => let u := eq_rect (ex, mu) (uncurry (OPMLPattern s)) x _ e : OPMLPattern s ex0 mu0 in hlistIn u h
          | _ => False
          end).
  refine (match decide ((s, ex, mu) = (s0, s' :: ex0, mu0)) with
          | left e => eq_rect (s, ex, mu) (uncurry3 OPMLPattern) x _ e = u
          | _ => False
          end).
Defined.

Arguments SubTree {_} _ _ /.

Goal forall {Σ : OPMLSignature}, well_founded SubTree.
Proof.
  intros.
  unfold well_founded.
  intros [[[s ex] mu] a]. simpl in a.
  revert s ex mu a.
  fix IH 4.
  (* intros [s []]. *)
  intros ? ? ? [].
  split. intros [[[s' ex'] mu'] y] H. simpl in H. destruct H.
  split. intros [[[s' ex'] mu'] y] H. simpl in H.
  case_match. 2: destruct H.
  destruct h. simpl in H. destruct H.
  simpl in H. case_match. 2: destruct H.
  (* apply eq_existT_curried in H.  rewrite H. *)
  (* epose proof (rew_swap (OPMLPattern ^~ ex0 ^~ mu0) e y H). *)
  assert (existT (s', ex', mu') y = existT (x, ex0, mu0) o). {
    eapply eq_existT_curried.
    Search eq_rect.
    (**)
  }
  rewrite H2.
  apply IH. Guarded.
  split. intros [[[s'' ex'] mu'] y] H. simpl in H.
  case_match. 2: destruct H.
  epose proof eq_existT_curried e H. rewrite H1.
  apply IH. Guarded.
Qed.

