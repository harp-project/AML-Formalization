
(* (** This won't work, because the data needs to be unboxed first! *)
Definition fun_notBool_Unds_ {T : Type} (inj : bool -> T) (b : bool) : option T :=
  Some (inj (negb b)).

Definition fun_Unds_andBool_Unds_ {T : Type} (inj : bool -> T) (b1 b2 : bool) : option T :=
  Some (inj (andb b1 b2)).

Definition fun_Unds_orBool_Unds_ {T : Type} (inj : bool -> T) (b1 b2 : bool) : option T :=
  Some (inj (orb b1 b2)).


 *)
From MatchingLogic Require Export stdpp_ext.
Require Import ZArith Bool.
Require Import List.
From stdpp Require Import list.

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

Module Map.
  Section Map.

    Context {K V : Set}
    (**
       I'm tempted to use eqdecision instead, as that can be an instance,
       but I'm not sure if we want to go back to that.
     *)
    (K_eqb : K -> K -> bool)
    (V_eqb : V -> V -> bool).

    Definition Map : Set := list (K * V).

    Definition choice (m : Map) : option K := if m is (k, _) :: _ then Some k else None.

    Definition lookup (m : Map) (k : K) : option V :=
      let fix F m' := if m' is (k', v') :: xs then if K_eqb k k' then Some v' else F xs else None in F m.

    Definition lookupOrDefault (m : Map) (k : K) (v : V) : V :=
      if lookup m k is Some x then x else v.
      (* let fix F m' := if m' is (k', v') :: xs then if K_eqb k k' then v' else F xs else v in F m. *)

    (**
       Since the documentation doesn't mention what happens if the key is
       not in the map, I decided not to raise an error. It is probably
       never tested, so it shouldn't matter.
     *)
    Definition remove (m : Map) (k : K) : Map :=
      let fix F m' := if m' is (k', v') :: xs then if K_eqb k k' then xs else (k', v') :: F xs else [] in F m.

    (**
       Decided to use remove, to make getting the size easier. Please
       consider if it would be better to deduplicate in the size function
       and not here. If you do decide to do that, the remove function
       needs to be updated, so EVERY occurrence of a key is removed. If
       you keep it this way, but change remove to give an error for a
       non-existing key, this will be more complicated.
     *)
    Definition update (m : Map) (k : K) (v : V) : Map := (k, v) :: remove m k.

    Definition difference (m m' : Map) : Map :=
      let fix F m'' :=
        if m'' is (k, v) :: xs then
          if lookup m' k is Some v' then
            if V_eqb v v' then
              F xs
            else
              (k, v) :: F xs
          else
            (k, v) :: F xs
        else
          []
      in F m.

    (**
       The documentation says this is supposed to be a strict subset, but
       neither the <= symbol, nor the name "inclusion" seem to suggest that.
       This implementation is not strict.

       Here I am using the following lemma: A ⊆ B <=> A \ B = ∅.

       The bottom, commented line should express strict inclusion, using the
       lemma A ⊂ B <=> A \ B = ∅ /\ B \ A ≠ ∅.
     *)
    Definition inclusion (m m' : Map) : bool :=
      if difference m m' is [] then true else false.
      (* if difference m m' is [] then if difference m' m isn't [] then true else false else false. *)

    (**
       This method is not needed directly, and is not in the
       documentation, but it's easiest to use this for the check at
       concat. If that check is removed, this can be too.

       For this, I am using the lemma: A ∩ B = A \ (A \ B).
     *)
    Definition intersection (m m' : Map) : Map := difference m (difference m m').

    (**
       I added the disjointness check mentioned in the documentation.
     *)
    Definition concat (m m' : Map) : option Map :=
      if intersection m m' is [] then Some (m ++ m') else None.

    Definition in_keys (k : K) : Map -> bool := fix F m := if m is (k', v') :: xs then if K_eqb k k' then true else F xs else false.

    (**
       I think this is singleton. Denoted with |->.
     *)
    Definition element (k : K) (v : V) : Map := [(k, v)].

    Definition size (m : Map) : Z := Z.of_nat (length m).

    Definition updateAll : Map -> Map -> Map := fix F m m' := if m' is (k, v) :: xs then F (update m k v) xs else [].

    Definition values : Map -> list V := fix F m := if m is (_, v) :: xs then v :: F xs else [].

  End Map.
  Arguments Map K V : assert, clear implicits.
End Map.

Module SSet.
  Section SSet.

    Context {V : Set}
    (V_eqb : V -> V -> bool).

    Definition SSet : Set := list V.

    Definition choice (s : SSet) : option V := if s is x :: xs then Some x else None.

    Definition in_ (v : V) : SSet -> bool :=
      fix F s' := if s' is x :: xs then if V_eqb x v then true else F xs else false.

    Definition difference (s s' : SSet) : SSet :=
      let fix F s'' := if s'' is x :: xs then if in_ x s' then F xs else x :: F xs else [] in F s.

    (**
       I'm pretty sure this is supposed to be singleton, but it's not
       explicitly said what the purpose of this function is in the
       documentation.
     *)
    Definition setitem : V -> SSet := (.:: []).

    (**
       See the note for Map.inclusion, the same things apply here.
     *)
    Definition inclusion (s s' : SSet) : bool :=
      if difference s s' is [] then true else false.
      (* if difference s s' is [] then if difference s' s isn't [] then true else false else false. *)

    (**
       For sets, this function is actually used.
       Based on the same lemma as for maps.
     *)
    Definition intersection (s s' : SSet) : SSet := difference s (difference s s').

    Definition union (s s' : SSet) : SSet := s ++ difference s' s.

    (**
       So this is funny. Technically the disjointness check should be
       present here, but according to the documentation, concatenating
       non-disjoint sets "may be silently allowed during concrete
       execution".
     *)
    Definition concat (s s' : SSet) : option SSet :=
      if intersection s s' is [] then Some (s ++ s') else None.

    Definition size (s : SSet) : Z := Z.of_nat (length s).

  End SSet.
  Arguments SSet V : assert, clear implicits.
End SSet.

Module MapSet.

  Import Map.
  Import SSet.

  Section MapSet.

    Context {K V : Set}
    (K_eqb : K -> K -> bool).

    Definition keys : Map K V -> SSet K := fix F m := if m is (k, v) :: xs then k :: F xs else [].

    (**
       Since sets ARE lists, this is easy.
     *)
    Definition keys_list : Map K V -> list K := keys.

    Definition removeAll : Map K V -> SSet K -> Map K V := fix F m s := if s is x :: xs then F (Map.remove K_eqb m x) xs else m.

  End MapSet.
End MapSet.

Module List.
  Section List.

  Context {T : Type}.

  Definition List_get (xs : list T) (z : Z) : option T :=
    if Z.ltb z 0
    then nth_error xs (Z.to_nat (Z.of_nat (length xs) + z))
    else nth_error xs (Z.to_nat z).

  (* TODO: check negative indices in K! *)
  Definition List_range (xs : list T) (x y : Z) : list T :=
    take (length xs - Z.to_nat x - Z.to_nat y)%nat (drop (Z.to_nat x) xs).
  Search nat nat list is:Definition.

  (* TODO: check negative indices in K! *)
  Definition List_set (xs : list T) (z : Z) (t : T) : option (list T) :=
    if (Z.to_nat (Z.abs z) <? length xs)%nat
    then Some (take (Z.to_nat z) xs ++ t :: drop (1 + Z.to_nat z) xs)
    else None.



  End List.
End List.

