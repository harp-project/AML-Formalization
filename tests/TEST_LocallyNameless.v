Require Import locally_nameless.
Require Import names.
Require Import ML.Signature.
Require Import ML.ConcreteSignature.
Import MLNotations.
Check @Pattern.
Check Signature.
Check ConcreteSignature.

Inductive Symbols : Type :=
| ctor
| p
| f
.

Print Pattern.
Let signature := {| symbols := Symbols; |}.

(* End Derived_operators. *)
Definition evar (sname : string) : @Pattern signature :=
  patt_free_evar (find_fresh_evar_name (@evar_c sname) nil). 
Definition svar (sname : string) : @Pattern signature :=
  patt_free_svar (find_fresh_svar_name (@svar_c sname) nil).

(*
Definition sym (sname : string)
  (in_sig : In _ (symbols signature) (@sigma_c sname)) : Pattern :=
  patt_sym (sigma_c sname) in_sig.
*)
(* Example patterns *)

(*
Axiom sig : Signature.
Axiom sym_in_sig : In _ (symbols signature) (@sigma_c "ctor").
Axiom p_in_sig : In _ (symbols signature) (@sigma_c "p").
Axiom f_in_sig : In _ (symbols signature) (@sigma_c "f").
*)
Definition more := svar ("A") or ¬ (svar ("A") ). (* A \/ ~A *)

(* A -> (B -> ~C) (exists x. D (bot /\ top)) *)

Definition complex :=
  evar ("A") --> (evar("B") --> ¬(svar("C"))) $
       ex , svar ("D") $ Bot and Top.

Program Definition custom_constructor := @patt_sym signature ctor.
(*
Definition custom_constructor := sym ("ctor") sym_in_sig $ evar ("a").
*)
(* p x1 x2 *)
(*
Definition predicate := sym ("p") p_in_sig $ evar ("x1") $ evar ("x2").
*)
(* f x (mu y . y) *)
(*
Definition function :=
  sym ("f") f_in_sig $ (evar ("x")) $ (mu , (patt_bound_svar 0)).
 *)

(* forall x, x /\ y *)
(*
Definition free_and_bound :=
  all , (patt_bound_evar 0) and evar ("y").
*)
(* End of examples. *)
