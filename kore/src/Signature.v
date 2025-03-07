From Coq Require Export ssreflect ssrfun ssrbool String.
From stdpp Require Export
  base
  countable
  infinite.


Set Default Proof Mode "Classic".

Class Sorts := {
    sort : Set;
    sort_eqdec :: EqDecision sort;
    sort_countable :: Countable sort;
(*     subsort : relation sort;
    subsort_po :: PartialOrder subsort; *)
}.

Class Variables {Ss : Sorts} := {
  evar : Set;
  svar : Set;
  evar_eqdec :: EqDecision evar;
  evar_countable :: Countable evar;
  (* evar_infinite :: Infinite evar; *)
  svar_eqdec :: EqDecision svar;
  svar_countable :: Countable svar;
  (* svar_infinite :: Infinite svar; *)

  evar_sort : evar -> sort;
  svar_sort : svar -> sort;

  evar_infinite s ::
    Infinite {x : evar & decide (evar_sort x = s)};
  svar_infinite s ::
    Infinite {x : svar & decide (svar_sort x = s)}
}.

Class Symbols {Ss : Sorts} := {
  symbol : Set;
  sym_eqdec :: EqDecision symbol;
  sym_countable :: Countable symbol;
  arg_sorts : symbol -> list sort ;
  ret_sort : symbol -> sort ;
}.

Class Signature := {
  sorts :: Sorts ;
  variables :: Variables;
  symbols :: Symbols;
}.