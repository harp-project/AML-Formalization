(* From Coq Require Import ssreflect ssrfun ssrbool. *)
From MatchingLogic.OPML Require Export OpmlSignature.
From stdpp Require Export base list list_numbers.
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
