From Coq Require Import ssreflect ssrfun ssrbool.

From Coq.Classes Require Import RelationClasses.

From stdpp Require Import
  countable
  infinite
.


Class OPMLSorts := {
    opml_sort : Set;
    opml_sort_eqdec :: EqDecision opml_sort;
    opml_sort_countable :: Countable opml_sort;
    opml_subsort : relation opml_sort;
    opml_subsort_po :: PartialOrder opml_subsort;
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

  opml_arg_sorts :
    opml_symbol ->
    list opml_sort ;
  
  opml_ret_sort :
    opml_symbol ->
    opml_sort ;
}.

Class OPMLSignature := {
  opml_sorts :: OPMLSorts ;
  opml_variables :: OPMLVariables;
  opml_symbols :: OPMLSymbols;
}.

Record OPMLSignatureMorphism (Σ1 Σ2 : OPMLSignature) := {
  osm_sorts : @opml_sort (@opml_sorts Σ1) -> @opml_sort (@opml_sorts Σ2) ;
  
  osm_evars : forall (s : @opml_sort (@opml_sorts Σ1)),
    @opml_evar (@opml_sorts Σ1) (@opml_variables Σ1) s ->
    @opml_evar (@opml_sorts Σ2) (@opml_variables Σ2) (osm_sorts s);
  
  osm_svars : forall (s : @opml_sort (@opml_sorts Σ1)),
    @opml_svar (@opml_sorts Σ1) (@opml_variables Σ1) s ->
    @opml_svar (@opml_sorts Σ2) (@opml_variables Σ2) (osm_sorts s);
}.


