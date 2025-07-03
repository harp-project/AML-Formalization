
From Coq Require Import String Bool ZArith Ascii.
Require Import ssreflect.
Require Import stdpp.base.


Open Scope string_scope.

Definition bool_parser (str : string) : option bool :=
  match str with
  | "false" => Some false
  | "true"  => Some true
  | _       => None
  end.

Definition nat_parser (str : string) : option nat := let fix F n s := if s is String x xs then F (10 * n + Ascii.nat_of_ascii x - 48) xs else n in Some (F 0 str).

Compute nat_parser "7".
Compute nat_parser "123".
Compute nat_parser "".
Compute nat_parser "{@}".

Definition Z_parser_with_base (base : nat) (str : string) : option Z :=
  let fix F n s :=
    if s is String x xs
    then F (base * n + (nat_of_ascii x - 48)) xs
    else n in
  match str with
  | String "-" xs => Some (Z.opp (Z.of_nat (F 0 xs)))
  | String "+" xs => Some (Z.of_nat (F 0 xs))
  | _ => Some (Z.of_nat (F 0 str))
  end.

Compute Z_parser_with_base 10 "1111".
Compute Z_parser_with_base 2 "1111".
Compute Z_parser_with_base 8 "123".
Compute Z_parser_with_base 2 "".
Compute Z_parser_with_base 2 "{@}".
Compute Z_parser_with_base 10 "{@}".

Definition Z_parser : string -> option Z := Z_parser_with_base 10.

Definition string_parser (str : string) : option string := Some  str.


Module MInt.

  From stdpp Require Import bitvector.

  Definition MInt (n : nat) : Set := bv (N.of_nat n).

  Definition neg {n : nat} : MInt n -> MInt n := bv_opp.

  Definition natvalue {n : nat} (x : MInt n) : nat := Z.to_nat (bv_unsigned x).

  Definition natural {n : nat} (x : nat) : MInt n := Z_to_bv (N.of_nat n) (Z.of_nat x).

  Definition uvalue {n : nat} : MInt n -> Z := bv_unsigned.
  Definition svalue {n : nat} : MInt n -> Z := bv_signed.

  Goal let x : MInt 3 := 7%bv in uvalue x = 7%Z /\ svalue x = (-1)%Z.
  Proof. auto. Qed.

  (**
     I'm not sure how exactly the hooked version of this works. Z_to_bv
     wraps its argument.
   *)
  Definition integer {n : nat} : Z -> MInt n := Z_to_bv (N.of_nat n).

  Instance bv_wf_zero (n : N) : BvWf n 0.
  Proof.
    apply bv_wf_in_range. split.
    apply Z.le_refl. apply bv_modulus_pos.
  Defined.

  (**
     Find more operations in this module.
   *)
  (* Search _ in definitions. *)
End MInt.

Import MInt.

Definition MInt_parser (m : nat) (str : string) : option (MInt m) :=
      let fix G n s := if s is String x xs then G (10 * n + nat_of_ascii x - 48) xs else n in
      let fix F f n s :=
        match s with
        | String "p" xs => if Nat.eqb (G 0 xs) m then Some (MInt.integer (f (Z.of_nat n))) else None
        (**
          Use this for no width check. G may be removed too in this case.
        *)
        (* | String "p" xs => Some (c_mint m (MInt.integer (f (Z.of_nat n)))) *)
        | String x xs => F f (10 * n + nat_of_ascii x - 48) xs
        | _ => None
        end
      in match str with
         | String "-" xs => F Z.opp 0 xs
         | String "+" xs => F id 0 xs
         | _ => F id 0 str
         end.

Compute MInt_parser 3 "7p3". (* 7 *)
Compute MInt_parser 3 "7p4". (* None *)
Compute MInt_parser 3 "8p3". (* 0 *)
Compute MInt_parser 3 "-1p3". (* 7 *)
Compute MInt_parser 49 "kapa". (* 639 *)

Definition None_parser {T} (str : string) : option T := None.

Definition map_parser {T U} (inj : T -> U) (parser : string -> option T) : string -> option U := fun str => fmap inj (parser str).