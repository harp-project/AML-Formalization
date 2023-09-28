From Coq Require Import ssreflect ssrfun ssrbool.

From stdpp Require Import
  countable
  infinite
.

Class OPMLSorts := {
    opml_sort : Set;
    opml_sort_eqdec :: EqDecision opml_sort;
    opml_sort_countable :: Countable opml_sort;
}.

Class OPMLVariables {Ss : OPMLSorts} := {
  opml_evar : opml_sort -> Set;
  opml_svar : opml_sort -> Set;
  opml_evar_eqdec :: forall s, EqDecision (opml_evar s);
  opml_evar_countable :: forall s, Countable (opml_evar s);
  opml_evar_infinite :: forall s, Infinite (opml_evar s);
  opml_svar_eqdec :: forall s, EqDecision (opml_svar s);
  opml_svar_countable :: forall s, Countable (opml_svar s);
  opml_svar_infinite :: forall s, Infinite (opml_svar s);
}.

Class OPMLSymbols {Ss : OPMLSorts} := {
  opml_symbol : Set;
  opml_sym_eqdec :: EqDecision opml_symbol;
  opml_sym_countable :: Countable opml_symbol;

  opml_arity :
    opml_symbol ->
    ((list opml_sort)*opml_sort)%type;
}.

Class Signature := {
  opml_sorts :: OPMLSorts ;
  opml_variables :: OPMLVariables;
  opml_symbols :: OPMLSymbols;
}.

(* Later we will define signature morphisms in some file *)
