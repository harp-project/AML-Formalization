
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

From Coq.Program Require Import Wf.

Module String.

  Open Scope nat_scope.

  Import Ascii.

  (**
     The documentation says nothing about range checks, so I didn't add
     any.
   *)
  Definition asciiToNat (x : ascii) : nat :=
    let n := nat_of_ascii x - 48 in
      if 10 <=? n then
        let n' := n - 7 in
          if 36 <=? n' then
            n' - 32
          else
            n'
      else
        n
  .

  Compute asciiToNat "0".
  Compute asciiToNat "A".
  Compute asciiToNat "Z".
  Compute asciiToNat "a".
  Compute asciiToNat "z".

  (**
     Similar to the above, no safety checks. Also, the documentation says
     "whether the letters returned [...] are upper or lowercase is
     determined by the backend, but the backend will consistently choose
     one or the other". The backend™ (me) has chosen uppercase.
   *)
  Definition natToAscii (n : nat) : ascii :=
    ascii_of_nat (if n <=? 9 then n + 48 else n + 55).

  Compute natToAscii 0.
  Compute natToAscii 10.
  Compute natToAscii 35.

  (**
     Unfortunately I couldn't avoid a well-founded recursion here. I'm not
     sure how it will simplify.

     If it causes problems, it might be possible to rewrite it with
     multiple nested fix-es, similar to reverse later, this time
     reimplementing div, mod and addition or substraction.
   *)
  Program Fixpoint unsafeConvert (num base : nat) (H : 2 <= base) {measure num} : string :=
    if num is 0 then
      EmptyString
    else
      String
        (natToAscii (Nat.modulo num base))
        (unsafeConvert (Nat.div num base) base H)
  .
  Next Obligation.
    intros.
    apply Nat.div_lt; lia.
  Defined.
  Next Obligation.
    intros. auto.
  Defined.
  Final Obligation.
    apply measure_wf, lt_wf.
  Defined.

  (**
     I had to add a check for the base.
   *)
  Definition base2string (num base : Z) : option string :=
    let base' := Z.to_nat base in
      if decide (2 <= base' <= 36) is left (conj H _) then
        Some (
          if Z.ltb num 0 then
            String "-" (unsafeConvert (Z.to_nat (Z.opp num)) base' H)
          else
            unsafeConvert (Z.to_nat num) base' H
        )
      else
        None
  .

  Definition int2string (num : Z) : option string := base2string num 10.

  (**
     I check to make sure the base is in range, but I don't check if it's
     actually right for the string. Also the lack of checking described at
     asciiToNat applies here. Do we need any of these checks?
   *)
  Definition string2base (str : string) (base : Z) : option Z :=
    if (2 <=? base)%Z && (base <=? 36)%Z then
      Some (
        let fix F n str' :=
          if str' is String x xs then
            F (10 * n + asciiToNat x) xs
          else
            n
        in match str with
           | String "-" xs => Z.opp (Z.of_nat (F 0 xs))
           | String "+" xs => Z.of_nat (F 0 xs)
           | _ => Z.of_nat (F 0 str)
           end
      )
     else
       None
  .

  Compute string2base "-bEeF" 16.

  Definition string2int (str : string) : option Z := string2base str 10.

  (**
     I guess?
   *)
  Definition string2id : string -> string := id.

  Definition concat : string -> string -> string := append.

  (**
     These functions, very helpfully UNdocumented in the Coq docs, are, I
     think, lexicographical.
   *)
  Definition le : string -> string -> bool := String.leb.
  Definition lt : string -> string -> bool := String.ltb.
  Definition ge (s s' : string) : bool := le s' s.
  Definition gt (s s' : string) : bool := lt s' s.
  Definition eq : string -> string -> bool := String.eqb.
  Definition ne (s s' : string) : bool := negb (eq s s').

  (**
     Yet another pair of barely documented functions. What do I do if the
     string contains more than 1 character? And if the integer is negative?
     I made the function partial, but as no one wrote it down, I don't know
     what actually happens.
   *)
  Definition chrChar (x : Z) : option string :=
    if Z.ltb x 0 then
      None
    else
      Some (String (ascii_of_nat (Z.to_nat x)) EmptyString)
  .
  Definition ordChar (x : string) : option Z :=
    if x is String y EmptyString then
      Some (Z.of_nat (nat_of_ascii y))
    else
      None
  .

  (**
     Basic replace function. As there is no documentation for what to do
     with empty needles, I allow them, but since every haystack "contains"
     an infinite amount of empty strings, it will just be prefixed by
     replacement times times. Negative integers also have no documented
     behaviour, so I treat them as zero. Finally, what to do if there are
     fewer needles than times was also not mentioned in the documentation,
     so I just treat it as a maximum (or "fuel" for the recursion). With
     these assumptions, this is a total function.

     Since this code is definitely in the "write-only" category, I included
     line-by-line comments, in case anyone actually has to read it at some
     point.
   *)
  Definition replace (haystack needle replacement : string) (times : Z) : string :=
    (* F is the main loop, decreasing on "fuel" *)
    let fix F n s :=
      (* if we have "fuel" *)
      if n is S n' then
        (* G tries to do a replacement at the first possibility *)
        let fix G s' :=
          (* we need to match the string now to use it for a trick later *)
          if s' is String x xs then
            (* H is the one actually doing the replacing *)
            let fix H hs nd :=
              (* if we still have chars in the needle *)
              if nd is String y ys then
                (* and the haystack *)
                if hs is String z zs then
                  (* and they are equal *)
                  if (y =? z)%char then
                    (* then keep going *)
                    H zs ys
                  else
                    (* if they weren't equal, replacement failed, try one char later; this is the trick to call G with a decreasing arg *)
                    String x (G xs)
                else
                  (* if ran out of "hay" before the needle, just return what we started with, no replacement or recursion needed here *)
                  s'
              else
                (* if needle ran out, replacement successful, start main loop over with less "fuel" *)
                append replacement (F n' hs)
            (* we eat the needle *)
            in H s' needle
          else
            (* this is the price of our trick, bit of repetition if the haystack couldn't be split, shortcircuiting H *)
            EmptyString
        (* we eat the "hay" *)
        in G s
      else
        (* if no fuel, return *)
        s
    (* convert Z to nat, also eating some "hay" *)
    in F (Z.to_nat times) haystack
  .

  Compute replace "ababa" "ab" "cd" 2.
  Compute replace "ababa" "ba" "cd" 2.
  Compute replace "ababa" "x" "cd" 2.
  Compute replace "ababa" "" "cd" 2.
  Compute replace "ababa" "ab" "cd" 1.
  Compute replace "ababa" "ab" "cd" 3.
  Compute replace "ababa" "a" "c" 3.
  Compute replace "ababa" "b" "c" 3.

  Definition replaceFirst (haystack needle replacement : string) : string := replace haystack needle replacement 1.

  (**
     If the needle is non-empty, there can be at most |haystack|
     replacements done, so I use the original replace with the length of
     haystack. Since if needle could be empty for this function, it would
     have to run indefinitely. Still, I make no check to ensure this. If it
     is desired, just wrap it in an if.
   *)
  Definition replaceAll (haystack needle replacement : string) : string := replace haystack needle replacement (Z.of_nat (String.length haystack)).

  Compute replaceAll "ababbaba" "ab" "cd".
  Compute replaceAll "aaaa" "a" "xy".
  Compute replaceAll "aaaa" "" "xy".

  (**
     This time I can't allow searching for an empty string in a string
     because the result would have to be infinity. Otherwise, I just split
     the needle early and do a lot of code duplication on its head and tail
     to ensure descreasing arguments for the fixpoints. This function is a
     lot more verbose and painful than it would be without the decreasing
     requirement.
   *)
  Definition countAllOccurrences (haystack needle : string) : option Z :=
    let fix F s x' xs' :=
      if s is String y ys then
        if (y =? x')%char then
          let fix G hs nd :=
            if nd is String z zs then
              if hs is String w ws then
                if (z =? w)%char then
                  G ws zs
                else
                  F ws x' xs'
              else
                0
            else
              S (F hs x' xs')
          in G ys xs'
        else
          F ys x' xs'
      else
        0
    in if needle is String x xs then
      Some (Z.of_nat (F haystack x xs))
    else
      None
  .

  Compute countAllOccurrences "ababbaba" "ab".

  Definition lengthString (s : string) : Z := Z.of_nat (String.length s).

  (**
     Still missing:

     I can do:
     - findChar(_,_,_)_STRING-COMMON_Int_String_String_Int{}(SortString{}, SortString{}, SortInt{}) : SortInt{}
     - findString(_,_,_)_STRING-COMMON_Int_String_String_Int{}(SortString{}, SortString{}, SortInt{}) : SortInt{}
     - rfindChar(_,_,_)_STRING-COMMON_Int_String_String_Int{}(SortString{}, SortString{}, SortInt{}) : SortInt{}
     - rfindString(_,_,_)_STRING-COMMON_Int_String_String_Int{}(SortString{}, SortString{}, SortInt{}) : SortInt{}
     - substrString(_,_,_)_STRING-COMMON_String_String_Int_Int{}(SortString{}, SortInt{}, SortInt{}) : SortString{}

     I can't do because missing Float carrier:
     - Float2String(_)_STRING-COMMON_String_Float{}(SortFloat{}) : SortString{}
     - FloatFormat{}(SortFloat{}, SortString{}) : SortString{}
     - String2Float(_)_STRING-COMMON_Float_String{}(SortString{}) : SortFloat{}

     I can't do because no documentation and I can't figure them out:
     - categoryChar(_)_STRING-COMMON_String_String{}(SortString{}) : SortString{}
     - directionalityChar(_)_STRING-COMMON_String_String{}(SortString{}) : SortString{}
   *)

  (* Search [is:Definition | is:Fixpoint] in String. *)

End String.
