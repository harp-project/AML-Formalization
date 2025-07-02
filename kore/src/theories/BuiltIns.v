
(* (** This won't work, because the data needs to be unboxed first! *)
Definition fun_notBool_Unds_ {T : Type} (inj : bool -> T) (b : bool) : option T :=
  Some (inj (negb b)).

Definition fun_Unds_andBool_Unds_ {T : Type} (inj : bool -> T) (b1 b2 : bool) : option T :=
  Some (inj (andb b1 b2)).

Definition fun_Unds_orBool_Unds_ {T : Type} (inj : bool -> T) (b1 b2 : bool) : option T :=
  Some (inj (orb b1 b2)).


 *)
Require Import ZArith Bool.

Definition neqbB (b1 b2 : bool) : bool :=
  negb (Bool.eqb b1 b2).
Arguments neqbB /.
Definition neqbZ (b1 b2 : Z) : bool :=
  negb (Z.eqb b1 b2).
Arguments neqbZ /.

Open Scope Z_scope.


(* NOTE: Beware the difference between mod and rem
   (and quot and div) *)
(*
  Following defs are taken from: https://github.com/runtimeverification/k/blob/eff6bea3f2118bb02c185888d1b369c5c2a59ec3/k-frontend/src/main/java/org/kframework/compile/ConstantFolding.java#L552
*)
(* TODO: Java throws an exception if idx or length is not unsigned *)
Definition bitRange (i idx len : Z) : Z :=
  Z.shiftr
    (Z.land i (Z.shiftl (Z.shiftl 1 len - 1) idx))
    idx.
Arguments bitRange /.

(* TODO: Java throws an exception if idx or length is not unsigned *)
Definition signExtendBitRange (i idx len : Z) : Z :=
match len with
| 0 => 0
| _ =>
  if Z.testbit i (idx + len - 1)
  then
    let max := Z.shiftl 1 (len - 1) in
      let tmp := bitRange i idx len in
        bitRange (tmp + max) 0 len - max
  else bitRange i idx len
end.
Arguments signExtendBitRange /.

Definition emod (a b : Z) : Z :=
  let rem := Z.rem a b in
  if rem <? 0
  then rem + Z.abs b
  else rem.
Arguments emod /.

Definition ediv (a b : Z) : Z :=
  Z.quot (a - emod a b) b.
Arguments ediv /.

(* REPORT modPow:
   This is how the Java code works, but every other
   operations is relying on rem, and not mod!
   Are we sure, that all backends understand mod and
   div as rem and quot?
 *)
Definition modPow (a b c : Z) : Z :=
  Z.modulo (Z.pow a b) c.
Arguments modPow /.

Compute modPow (-7) 3 20.

(* BEWARE the order of arguments! *)
Definition divides (a b : Z) : bool :=
  Z.rem b a =? 0.

