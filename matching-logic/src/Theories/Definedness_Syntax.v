(* In this module we define the definedness symbol and use it to build derived notions
   like totality and equality.
 *)
 From Coq Require Import ssreflect ssrfun ssrbool.
 Set Implicit Arguments.
 Unset Strict Implicit.
 Unset Printing Implicit Defensive.
  
 From Coq Require Import String Setoid.
 Require Import Coq.Program.Equality.
 Require Import Coq.Logic.Classical_Prop.
 From Coq.Logic Require Import FunctionalExtensionality Eqdep_dec.
 From Coq.Classes Require Import Morphisms_Prop.
 From Coq.Unicode Require Import Utf8.
 From Coq.micromega Require Import Lia.
 
 From MatchingLogic Require Import Syntax NamedAxioms DerivedOperators_Syntax IndexManipulation.
 From MatchingLogic.Utils Require Import stdpp_ext.
 
 From stdpp Require Import base fin_sets sets propset proof_irrel option list.
 
 Import extralibrary.
 
 Import MatchingLogic.Syntax.Notations.
 Import MatchingLogic.DerivedOperators_Syntax.Notations.
 Import MatchingLogic.Syntax.BoundVarSugar.

 Open Scope ml_scope.

(* We have only one symbol *)
Inductive Symbols := definedness.

Global Instance Symbols_eqdec : EqDecision Symbols.
Proof. unfold EqDecision. intros x y. unfold Decision. destruct x. decide equality. (*solve_decision.*) Defined.

  Class Syntax {Σ : Signature} :=
    {
    (* 'Symbols' are a 'subset' of all the symbols from the signature *)
    inj: Symbols -> symbols;
    (* TODO make it injective? *)
    (* for convenience *)
    }.

Section definedness.
  
  Context {Σ : Signature}.

  Context {syntax : Syntax}.

  Definition patt_defined (phi : Pattern) : Pattern :=
    patt_sym (inj definedness) $ phi.
  
  Definition patt_total (phi: Pattern) : Pattern :=
    patt_not (patt_defined (patt_not phi)).

  Definition patt_subseteq (phi1 phi2 : Pattern) : Pattern :=
    patt_total (phi1 ---> phi2).
  
  Definition patt_equal (phi1 phi2 : Pattern) : Pattern :=
    patt_total (phi1 <---> phi2).

  Definition patt_in (phi1 phi2 : Pattern) : Pattern :=
    patt_defined (patt_and phi1 phi2).

  Definition AC_patt_defined : Application_context :=
    @ctx_app_r _ (patt_sym (inj definedness)) box ltac:(auto).

  Definition is_predicate_pattern ψ : Pattern :=
    (patt_equal ψ patt_top) or (patt_equal ψ patt_bott).
End definedness.

Module Notations.
  Import Syntax.

  Notation "⌈ p ⌉" := (patt_defined p) : ml_scope.
  Notation "⌊ p ⌋" := (patt_total p) : ml_scope.
  Notation "p =ml q" := (patt_equal p q) (at level 67) : ml_scope.
  Notation "p ⊆ml q" := (patt_subseteq p q) (at level 67) : ml_scope.
  Notation "p ∈ml q" := (patt_in p q) (at level 67) : ml_scope.
  
End Notations.

Import Notations.

Section definedness.
  Context
    {Σ : Signature}
    {syntax : Syntax}
  .

  Lemma well_formed_defined ϕ:
    well_formed ϕ = true ->
    well_formed ⌈ ϕ ⌉ = true.
  Proof.
    intros Hwfϕ.
    unfold patt_defined.
    auto.
  Qed.

  #[local]
   Hint Resolve well_formed_defined : core.

  Lemma well_formed_total ϕ:
    well_formed ϕ = true ->
    well_formed ⌊ ϕ ⌋ = true.
  Proof.
    intros Hwfϕ.
    unfold patt_total.
    auto.
  Qed.

  #[local]
   Hint Resolve well_formed_total : core.
  
  Lemma well_formed_equal (phi1 phi2 : Pattern) :
    well_formed phi1 = true ->
    well_formed phi2 = true ->
    well_formed (phi1 =ml phi2) = true.
  Proof.
    intros wfphi1 wfphi2. unfold "=ml". auto.
  Qed.

  #[local]
   Hint Resolve well_formed_equal : core.
  
  Lemma well_formed_subseteq (phi1 phi2 : Pattern) :
    well_formed phi1 = true ->
    well_formed phi2 = true ->
    well_formed (phi1 ⊆ml phi2) = true.
  Proof.
    intros wfphi1 wfphi2. unfold "⊆ml". auto.
  Qed.

  #[local]
   Hint Resolve well_formed_subseteq : core.

  Lemma well_formed_in (phi1 phi2 : Pattern) :
    well_formed phi1 = true ->
    well_formed phi2 = true ->
    well_formed (phi1 ∈ml phi2) = true.
  Proof.
    intros wfphi1 wfphi2. unfold "∈ml". auto.
  Qed.

  #[local]
   Hint Resolve well_formed_in : core.


  Definition ev_x := (evar_fresh []).
  Definition p_x := patt_free_evar ev_x.
  
  Inductive AxiomName := AxDefinedness.

  Definition axiom(name : AxiomName) : Pattern :=
    match name with
    | AxDefinedness => patt_defined p_x
    end.

  Program Definition named_axioms : NamedAxioms :=
    {| NAName := AxiomName;
      NAAxiom := axiom;
    |}.
  Next Obligation.
    intros name. destruct name; simpl; wf_auto2.
  Qed.

  Definition theory := theory_of_NamedAxioms named_axioms.



  (* defined, total, subseteq, equal, in *)
  Lemma bevar_subst_defined ψ (wfcψ : well_formed_closed ψ) x ϕ :
    bevar_subst (patt_defined ϕ) ψ x = patt_defined (bevar_subst ϕ ψ x).
  Proof. unfold patt_defined. cbn. auto. Qed.
  Lemma bsvar_subst_defined ψ (wfcψ : well_formed_closed ψ) x ϕ :
    bsvar_subst (patt_defined ϕ) ψ x = patt_defined (bsvar_subst ϕ ψ x).
  Proof. unfold patt_defined. cbn. auto. Qed.

  #[global]
   Instance Unary_defined : Unary patt_defined :=
    {| unary_bevar_subst := bevar_subst_defined ;
       unary_bsvar_subst := bsvar_subst_defined ;
    |}.
  

  Lemma bevar_subst_total ψ (wfcψ : well_formed_closed ψ) x ϕ :
    bevar_subst (patt_total ϕ) ψ x = patt_total (bevar_subst ϕ ψ x).
  Proof. unfold patt_total. simpl_bevar_subst. reflexivity. Qed.
  
  Lemma bsvar_subst_total ψ (wfcψ : well_formed_closed ψ) x ϕ :
    bsvar_subst (patt_total ϕ) ψ x = patt_total (bsvar_subst ϕ ψ x).
  Proof. unfold patt_total. simpl_bsvar_subst. reflexivity. Qed.

  #[global]
   Instance Unary_total : Unary patt_total :=
    {| unary_bevar_subst := bevar_subst_total ;
       unary_bsvar_subst := bsvar_subst_total ;
    |}.
  
  
  Lemma bevar_subst_equal ψ (wfcψ : well_formed_closed ψ) x ϕ₁ ϕ₂ :
    bevar_subst (patt_equal ϕ₁ ϕ₂) ψ x = patt_equal (bevar_subst ϕ₁ ψ x) (bevar_subst ϕ₂ ψ x).
  Proof. unfold patt_equal. simpl_bevar_subst. reflexivity. Qed.

  Lemma bsvar_subst_equal ψ (wfcψ : well_formed_closed ψ) x ϕ₁ ϕ₂ :
    bsvar_subst (patt_equal ϕ₁ ϕ₂) ψ x = patt_equal (bsvar_subst ϕ₁ ψ x) (bsvar_subst ϕ₂ ψ x).
  Proof. unfold patt_equal. simpl_bsvar_subst. reflexivity. Qed.

  #[global]
   Instance Binary_equal : Binary patt_equal :=
    {| binary_bevar_subst := bevar_subst_equal ;
       binary_bsvar_subst := bsvar_subst_equal ;
    |}.
  
  Lemma bevar_subst_subseteq ψ (wfcψ : well_formed_closed ψ) x ϕ₁ ϕ₂ :
    bevar_subst (patt_subseteq ϕ₁ ϕ₂) ψ x = patt_subseteq (bevar_subst ϕ₁ ψ x) (bevar_subst ϕ₂ ψ x).
  Proof. unfold patt_subseteq. simpl_bevar_subst. reflexivity. Qed.

  Lemma bsvar_subst_subseteq ψ (wfcψ : well_formed_closed ψ) x ϕ₁ ϕ₂ :
    bsvar_subst (patt_subseteq ϕ₁ ϕ₂) ψ x = patt_subseteq (bsvar_subst ϕ₁ ψ x) (bsvar_subst ϕ₂ ψ x).
  Proof. unfold patt_subseteq. simpl_bsvar_subst. reflexivity. Qed.

  #[global]
   Instance Binary_subseteq : Binary patt_subseteq :=
    {| binary_bevar_subst := bevar_subst_subseteq ;
       binary_bsvar_subst := bsvar_subst_subseteq ;
    |}.
  

  Lemma bevar_subst_in ψ (wfcψ : well_formed_closed ψ) x ϕ₁ ϕ₂ :
    bevar_subst (patt_in ϕ₁ ϕ₂) ψ x = patt_in (bevar_subst ϕ₁ ψ x) (bevar_subst ϕ₂ ψ x).
  Proof. unfold patt_in. simpl_bevar_subst. reflexivity. Qed.

  Lemma bsvar_subst_in ψ (wfcψ : well_formed_closed ψ) x ϕ₁ ϕ₂ :
    bsvar_subst (patt_in ϕ₁ ϕ₂) ψ x = patt_in (bsvar_subst ϕ₁ ψ x) (bsvar_subst ϕ₂ ψ x).
  Proof. unfold patt_in. simpl_bsvar_subst. reflexivity. Qed.

  #[global]
   Instance Binary_in : Binary patt_in :=
    {| binary_bevar_subst := bevar_subst_in ;
       binary_bsvar_subst := bsvar_subst_in ;
    |}.

  (* Defines ϕ₁ to be an inversion of ϕ₂ *)
  (* ∀ x. ϕ₁ x = ∃ y. y ∧ (x ∈ ϕ₂ y)
     This assumes, that bound element variables x and y do not occur in ϕ₁ and ϕ₂ *)
     Definition patt_eq_inversion_of ϕ₁ ϕ₂
     := patt_forall
          (patt_equal
             (patt_app (nest_ex ϕ₁) (patt_bound_evar 0))
             (patt_exists (patt_and (patt_bound_evar 0)
                                    (patt_in (patt_bound_evar 1)
                                             (patt_app (nest_ex (nest_ex ϕ₂)) (patt_bound_evar 0)))))).
 

End definedness.