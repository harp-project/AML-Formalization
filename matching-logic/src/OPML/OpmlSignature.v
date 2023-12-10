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

Class OPMLVariables {Ss : OPMLSorts} := mkOPMLVariables {
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

Record OPMLSignatureExtension
  {_sorts : OPMLSorts}
  {_vars : OPMLVariables} 
:= {
    ose_new_sort : Set ;
    ose_new_sort_eqdec :: EqDecision ose_new_sort;
    ose_new_sort_countable :: Countable ose_new_sort;
    ose_new_subsort : relation ose_new_sort;
    ose_new_subsort_po :: PartialOrder ose_new_subsort;

    ose_new_evar : ose_new_sort -> Set;
    ose_new_svar : ose_new_sort -> Set;
    ose_new_evar_eqdec :: forall s, EqDecision (ose_new_evar s);
    ose_new_evar_countable :: forall s, Countable (ose_new_evar s);
    ose_new_evar_infinite :: forall s, Infinite (ose_new_evar s);
    ose_new_svar_eqdec :: forall s, EqDecision (ose_new_svar s);
    ose_new_svar_countable :: forall s, Countable (ose_new_svar s);
    ose_new_svar_infinite :: forall s, Infinite (ose_new_svar s);

    (* We will ignore subsorting for now *)
    ose_new_symbol : Set;
    ose_new_sym_eqdec :: EqDecision ose_new_symbol;
    ose_new_sym_countable :: Countable ose_new_symbol;

    ose_new_arg_sorts :
      ose_new_symbol ->
      list (ose_new_sort+opml_sort)%type ;
    
    ose_new_ret_sort :
      ose_new_symbol ->
      (ose_new_sort+opml_sort)%type ;
}.

Program Definition opml_signature_extend
  (Σ : OPMLSignature)
  (X : OPMLSignatureExtension)
  : OPMLSignature
:= {|
  OpmlSignature.opml_sorts := {|
    opml_sort := ((ose_new_sort X)+(@opml_sort (@opml_sorts Σ)))%type;
    opml_subsort := fun x y =>
      match x,y with
      | inl x', inl y' => ose_new_subsort X x' y'
      | inr x', inr y' => @opml_subsort (@opml_sorts Σ) x' y'
      | _,_ => False
      end
    ;
  |};
  opml_variables := @mkOPMLVariables (
    (* This is an ugly copy-paste but I do not know how to access the above-defined opml_sorts. *)
    {|
    opml_sort := ((ose_new_sort X)+(@opml_sort (@opml_sorts Σ)))%type;
    |})
    (fun (s : ((ose_new_sort X)+(@opml_sort (@opml_sorts Σ)))%type) =>
      match s with
      | inl s0 => ose_new_evar X s0
      | inr s0 => @opml_evar (@opml_sorts Σ) (@opml_variables Σ) s0
      end
    )
    (fun (s : ((ose_new_sort X)+(@opml_sort (@opml_sorts Σ)))%type) =>
      match s with
      | inl s0 => ose_new_svar X s0
      | inr s0 => @opml_svar (@opml_sorts Σ) (@opml_variables Σ) s0
      end
    )
    _
    _
    _
    _
    _
    _
  ;
  opml_symbols := {|
    opml_symbol := ((ose_new_symbol X)+(@opml_symbol (@opml_sorts Σ) (@opml_symbols Σ)))%type ;
    opml_sym_eqdec := _ ;
    opml_sym_countable := _ ;
    opml_arg_sorts := fun s =>
      match s with
      | inl s' => ose_new_arg_sorts X s'
      | inr s' => let l := @opml_arg_sorts (@opml_sorts Σ) (@opml_symbols Σ) s' in
        inr <$> l
      end
    ;
    opml_ret_sort := fun s =>
      match s with
      | inl s' => ose_new_ret_sort X s'
      | inr s' => let ss := @opml_ret_sort (@opml_sorts Σ) (@opml_symbols Σ) s' in
        inr ss
      end
    ;
  |};
|}.
(*Next Obligation.
  intros. apply _.
Defined.
Next Obligation.
  intros.
  apply sum_countable.
Defined.
*)
Next Obligation.
  intros Σ X x y.
  simpl.
  intros s1 s2.
  split; intros x' y' [HContra1 HContra2].
  { inversion HContra1. }
  { inversion HContra2. }
Qed.
Next Obligation.
  intros Σ X x y.
  simpl.
  intros s1 s2.
  split; intros x' y' [HContra1 HContra2].
  { inversion HContra2. }
  { inversion HContra1. }
Qed.
Next Obligation.
  intros Σ X.
  repeat constructor; simpl.
  {
    intros x.
    destruct x.
    { 
      apply ose_new_subsort_po.
    }
    { apply (opml_subsort_po). }
  }
  {
    intros x y z.
    destruct x,y,z; try (solve [intros; exfalso; assumption]).
    { 
      apply ose_new_subsort_po.
    }
    { apply (opml_subsort_po). }
  }
  {
    intros x y.
    destruct x,y; try (solve [intros; exfalso; assumption]);
      intros H1 H2; apply f_equal.
    { 
      apply ose_new_subsort_po; assumption.
    }
    { apply (opml_subsort_po); assumption. }
  }
Qed.
Next Obligation.
  intros Σ X s.
  destruct s; solve_decision.
Defined.
Next Obligation.
  intros Σ X s.
  destruct s; apply _.
Qed.
Next Obligation.
  intros Σ X s.
  destruct s; apply _.
Qed.
Next Obligation.
  intros Σ X s.
  destruct s; apply _.
Defined.
Next Obligation.
  intros Σ X s.
  destruct s; apply _.
Qed.
Next Obligation.
  intros Σ X s.
  destruct s; apply _.
Qed.
Fail Next Obligation.

Definition opml_signature_extend_morphism
  (Σ : OPMLSignature)
  (X : OPMLSignatureExtension)
  : OPMLSignatureMorphism Σ (opml_signature_extend Σ X)
:= 
  let Σ_sort := @opml_sort (@opml_sorts Σ) in
  let Σ_evar := @opml_evar (@opml_sorts Σ) (@opml_variables Σ) in
  let Σ_svar := @opml_svar (@opml_sorts Σ) (@opml_variables Σ) in
  let Σ' := (opml_signature_extend Σ X) in
  let Σ'_sort := (@opml_sort (@opml_sorts (Σ'))) in
  let Σ'_evar := @opml_evar (@opml_sorts Σ') (@opml_variables Σ') in
  let Σ'_svar := @opml_svar (@opml_sorts Σ') (@opml_variables Σ') in
  {|
  osm_sorts := fun s => (inr s):Σ'_sort ;
  osm_evars := fun (s : Σ_sort) (x : Σ_evar s) => (x):(Σ'_evar (inr s)) ;
  osm_svars := fun (s : Σ_sort) (x : Σ_svar s) => (x):(Σ'_svar (inr s)) ;
|}
.

(*
Definition SignatureFamilyT : Type := forall (I : Type), I -> OPMLSignature.

*)

Program Definition signature_union (Σ1 Σ2 : OPMLSignature) : OPMLSignature := {|
  opml_sorts := {|
    opml_sort := ((@opml_sort (@opml_sorts Σ1))+(@opml_sort (@opml_sorts Σ2)))%type ;
    opml_sort_eqdec := _ ;
    opml_sort_countable := _ ;
    opml_subsort := fun s1 s2 =>
      match s1, s2 with
      | inl s1', inl s2' => @opml_subsort (@opml_sorts Σ1) s1' s2'
      | inr s1', inr s2' => @opml_subsort (@opml_sorts Σ2) s1' s2'
      | _, _ => False
      end ;
  |} ;
  opml_variables := @mkOPMLVariables _
    (fun s =>
      match s with
      | inl s0 => @opml_evar (@opml_sorts Σ1) (@opml_variables Σ1) s0
      | inr s0 => @opml_evar (@opml_sorts Σ2) (@opml_variables Σ2) s0
      end
    )
    (fun s =>
      match s with
      | inl s0 => @opml_svar (@opml_sorts Σ1) (@opml_variables Σ1) s0
      | inr s0 => @opml_svar (@opml_sorts Σ2) (@opml_variables Σ2) s0
      end
    )
    _
    _
    _
    _
    _
    _
  ;
  
  opml_symbols := {|
    opml_symbol := (((@opml_symbol (@opml_sorts Σ1) (@opml_symbols Σ1)))+(@opml_symbol (@opml_sorts Σ2) (@opml_symbols Σ2)))%type ;
    opml_sym_eqdec := _ ;
    opml_sym_countable := _ ;
    opml_arg_sorts := fun s =>
      match s with
      | inl s' =>
        let l := @opml_arg_sorts (@opml_sorts Σ1) (@opml_symbols Σ1) s' in
        inl <$> l
      | inr s' =>
        let l := @opml_arg_sorts (@opml_sorts Σ2) (@opml_symbols Σ2) s' in
        inr <$> l
      end
    ;
    opml_ret_sort := fun s =>
      match s with
      | inl s' =>
        let ss := @opml_ret_sort (@opml_sorts Σ1) (@opml_symbols Σ1) s' in
        inl ss
      | inr s' =>
        let ss := @opml_ret_sort (@opml_sorts Σ2) (@opml_symbols Σ2) s' in
        inr ss
      end
    ;
  |};
|}.
Next Obligation.
  intros.
  split; intros; try naive_solver.
Qed.
Next Obligation.
  intros.
  split; intros; try naive_solver.
Qed.
Next Obligation.
  (* subsorting relation is partially ordered *)
  intros.
  (repeat split).
  {
    intros x. (repeat case_match); simplify_eq/=; apply opml_subsort_po.
  }
  {
    intros x y z Hxy Hyz.
    (repeat case_match); simplify_eq/=; try contradiction; try (solve [eapply transitivity; eassumption]).
  }
  {
    intros x y Hxy Hyx.
    (repeat case_match); simplify_eq/=; try contradiction; try (f_equal; apply opml_subsort_po; assumption).
  }
Qed.
Next Obligation.
  intros. simpl. (repeat case_match); simplify_eq/=; apply _.
Defined.
Next Obligation.
  intros. simpl. (repeat case_match); simplify_eq/=; apply _.
Qed.
Next Obligation.
  intros. simpl. (repeat case_match); simplify_eq/=; apply _.
Qed.
Next Obligation.
  intros. simpl. (repeat case_match); simplify_eq/=; apply _.
Defined.
Next Obligation.
  intros. simpl. (repeat case_match); simplify_eq/=; apply _.
Qed.
Next Obligation.
  intros. simpl. (repeat case_match); simplify_eq/=; apply _.
Qed.
Fail Next Obligation.

