Require Import locally_nameless.
Require Import names.
Require Import ML.Signature.
Require Import ML.DefaultVariables.
Import MLNotations.



Inductive Symbols : Type :=
| ctor
| p
| f
.

Lemma Symbols_dec : forall (s1 s2 : Symbols), {s1 = s2} + {s1 <> s2}.
Proof.
  decide equality.
Qed.

Let signature :=
  {| symbols := Symbols;
     sym_eq := Symbols_dec;
     variables := DefaultMLVariables;
  |}.

(* Helpers. *)
Definition sym (s : Symbols) : @Pattern signature :=
  @patt_sym signature s.
Definition evar (sname : string) : @Pattern signature :=
  @patt_free_evar signature (find_fresh_evar_name (@evar_c sname) nil).
Definition svar (sname : string) : @Pattern signature :=
  @patt_free_svar signature (find_fresh_svar_name (@svar_c sname) nil).

(* Example patterns *)

Definition more := svar ("A") or ¬ (svar ("A") ). (* A \/ ~A *)

(* A -> (B -> ~C) (exists x. D (bot /\ top)) *)

Definition complex :=
  evar ("A") --> (evar("B") --> ¬(svar("C"))) $
       ex , svar ("D") $ Bot and Top.

Definition custom_constructor := sym ctor.

(* p x1 x2 *)
Definition predicate := sym (ctor) $ evar ("x1") $ evar ("x2").
(* f x (mu y . y) *)

Definition function :=
  sym (f) $ (evar ("x")) $ (mu , (patt_bound_svar 0)).


Print patt_forall.
(* forall x, x /\ y *)
Definition free_and_bound :=
  all , (patt_bound_evar 0) and evar ("y").
(* End of examples. *)
