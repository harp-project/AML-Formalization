From Coq Require Import ssreflect ssrfun ssrbool.

From stdpp Require Import base finite gmap mapset listset_nodup numbers propset list pretty strings.


Global Instance string_app_empty_rightid :
  RightId (=) "" String.append
.
Proof.
  intros s.
  induction s; simpl.
  { reflexivity. }
  cbv.
  fold String.append. (* This is weird. *)
  rewrite IHs.
  reflexivity.
Qed.

Global Instance string_app_empty_leftid :
  LeftId (=) "" String.append
.
Proof.
  intros s. reflexivity.
Qed.

Lemma string_of_list_ascii_app l1 l2:
  string_of_list_ascii (l1 ++ l2)
  = (string_of_list_ascii l1) +:+ (string_of_list_ascii l2)
.
Proof.
  induction l1; cbn.
  {
    unfold String.append. reflexivity.
  }
  {
    rewrite IHl1. clear IHl1.
    reflexivity.
  }
Qed.


Global Instance string_of_list_ascii_of_string_cancel:
  Cancel (=) string_of_list_ascii list_ascii_of_string
.
Proof.
  intros x.
  apply string_of_list_ascii_of_string.
Qed.

Global Instance list_ascii_of_string_of_list_ascii_cancel:
  Cancel (=) list_ascii_of_string string_of_list_ascii 
.
Proof.
  intros x.
  apply list_ascii_of_string_of_list_ascii.
Qed.

Global Instance string_of_list_ascii_inj:
  Inj (=) (=) string_of_list_ascii
.
Proof.
  apply cancel_inj.
Qed.

Global Instance list_ascii_of_string_inj:
  Inj (=) (=) list_ascii_of_string
.
Proof.
  apply cancel_inj.
Qed.

Global Instance string_app_assoc:
  Assoc (=) String.append
.
Proof.
  intros x y z.
  rewrite -(string_of_list_ascii_of_string x).
  rewrite -(string_of_list_ascii_of_string y).
  rewrite -(string_of_list_ascii_of_string z).
  rewrite -!string_of_list_ascii_app.
  rewrite app_assoc.
  reflexivity.
Qed.

Global Instance string_app_inj_2 s2 :
  Inj (=) (=) (fun s1 => String.append s1 s2).
Proof.
  intros s1 s1' H.
  move: s1 s1' H.
  induction s2; intros s1 s1' H; cbn in *.
  {
    do 2 rewrite right_id in H.
    exact H.
  }
  {
    replace (String a s2)
      with ((String a EmptyString) +:+ s2) in H
      by reflexivity.
    replace (String a s1)
      with ((String a EmptyString) +:+ s1) in H
      by reflexivity.
    rewrite 2!string_app_assoc in H.
    specialize (IHs2 _ _ H).
    clear H s2.
    rename IHs2 into H.
    rewrite -(string_of_list_ascii_of_string s1).
    rewrite -(string_of_list_ascii_of_string s1').
    rewrite -(string_of_list_ascii_of_string s1) in H.
    rewrite -(string_of_list_ascii_of_string s1') in H.
    rewrite -(string_of_list_ascii_of_string (String a "")) in H.
    rewrite [list_ascii_of_string (String a "")]/= in H.
    rewrite -!string_of_list_ascii_app in H.
    apply string_of_list_ascii_inj in H.
    simplify_list_eq.
    congruence.
    }
Qed.


Lemma list_ascii_of_string_app s1 s2:
  list_ascii_of_string (s1 +:+ s2)
  = (list_ascii_of_string s1) ++ (list_ascii_of_string s2)
.
Proof.
  induction s1; cbn.
  {
    reflexivity.
  }
  {
    cbv. fold list_ascii_of_string. fold String.append.
    apply f_equal. rewrite IHs1. reflexivity.
  }
Qed.