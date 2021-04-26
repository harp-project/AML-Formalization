From Coq Require Import ssreflect ssrfun ssrbool.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import Setoid.
Require Import List.
Require Import Ensembles.
Require Import Coq.Strings.String.
Require Import extralibrary.

(*From Ltac2 Require Import Ltac2.*)
From Coq Require Import Logic.Classical_Prop.
From stdpp Require Import countable.
From stdpp Require Import pmap gmap mapset fin_sets.
Require Import stdpp_ext.

Class MLVariables := {
  evar : Type;
  svar : Type;
  evar_eqdec : EqDecision evar;
  evar_countable : Countable evar;
  svar_eqdec : EqDecision svar;
  svar_countable : Countable svar;
  (* TODO fresh generator *)
  evar_fresh : list evar -> evar;
  svar_fresh : list svar -> svar;
  evar_fresh_is_fresh : forall l,
      ~List.In (evar_fresh l) l;
  svar_fresh_is_fresh : forall l,
      ~List.In (svar_fresh l) l;
  (* We need a way to build named variables from strings *)
  nevar : string -> evar;
  nsvar : string -> svar;
  nevar_inj : forall (s1 s2 : string), nevar s1 = nevar s2 -> s1 = s2;
  nsvar_inj : forall (s1 s2 : string), nsvar s1 = nsvar s2 -> s1 = s2;
}.

Class Signature := {
  variables : MLVariables;
  symbols : Type;
  sym_eq : forall (s1 s2 : symbols), {s1 = s2} + {s1 <> s2};
}.

(* TODO move to some other file *)
Definition Power (Sigma : Type) := Ensemble Sigma.

(* TODO have different type for element variable and for set variable index *)
Definition db_index := nat.


Section syntax.

  Context {signature : Signature}.
  Existing Instance variables.

  Inductive Pattern : Type :=
  | patt_free_evar (x : evar)
  | patt_free_svar (x : svar)
  | patt_bound_evar (n : db_index)
  | patt_bound_svar (n : db_index)
  | patt_sym (sigma : symbols) :  Pattern
  | patt_app (phi1 phi2 : Pattern)
  | patt_bott
  | patt_imp (phi1 phi2 : Pattern)
  | patt_exists (phi : Pattern)
  | patt_mu (phi : Pattern)
  .

  Instance Pattern_eqdec : EqDecision Pattern.
  Proof.
    unfold EqDecision. intros. unfold Decision. decide equality.
    - apply evar_eqdec.
    - apply svar_eqdec.
    - apply nat_eq_dec.
    - apply nat_eq_dec.
    - apply sym_eq.
  Qed.

  Definition Theory := Ensemble Pattern.
  
  (** There are two substitution operations over types, written
  [vsubst] and [psubst] in Pollack's talk.  
  [vsubst] substitutes a pattern for a bound variable (a de Bruijn index).
  [psubst] substitutes a pattern for a free variable (a name).

  The crucial observation is that variable capture cannot occur
  during either substitution:
  - Types never contain free de Bruijn indices, since these
    indices are used only for representing bound variables.
    Therefore, [vsubst] does not need to
    perform lifting of de Bruijn indices in the substituted type.
  - Types never bind names, only de Bruijn indices.
    Therefore, [psubst] never needs to perform renaming of
    names in the substituted term when descending below a
    binder.
   *)

  (* substitute bound variable x for psi in phi *)
  Fixpoint bevar_subst (phi psi : Pattern) (x : db_index) :=
    match phi with
    | patt_free_evar x' => patt_free_evar x'
    | patt_free_svar x' => patt_free_svar x'
    | patt_bound_evar n => match compare_nat n x with
                           | Nat_less _ _ _ => patt_bound_evar n
                           | Nat_equal _ _ _ => psi
                           | Nat_greater _ _ _ => patt_bound_evar (pred n)
                           end
    | patt_bound_svar n => patt_bound_svar n
    | patt_sym sigma => patt_sym sigma
    | patt_app phi1 phi2 => patt_app (bevar_subst phi1 psi x)
                                     (bevar_subst phi2 psi x)
    | patt_bott => patt_bott
    | patt_imp phi1 phi2 => patt_imp (bevar_subst phi1 psi x) (bevar_subst phi2 psi x)
    | patt_exists phi' => patt_exists (bevar_subst phi' psi (S x))
    | patt_mu phi' => patt_mu (bevar_subst phi' psi x)
    end.

  (* In the Leroy's PoplMark paper (https://xavierleroy.org/publi/POPLmark-locally-nameless.pdf),
     the substitution for bounded variables (called `vsubst` decrements the index of bound variables)
     that are greater than `x`. I have no idea why. Here we want  bsvar_subst to have the property
     that if `x` is not present in the formula, then the substitution is no-op (see the lemma
     `bsvar_subst_not_occur_is_noop`).
     Therefore,
     our version keeps the greater indices intact. If someone needs the original behavior,
     she may write a standalone operation that only decrements high indices.

     The function `bevar_subst` is kept in the original form, since I do not have a use-case
     for the simplified version yet. But feel free to simplify it too.
   *)
  Fixpoint bsvar_subst (phi psi : Pattern) (x : db_index) :=
    match phi with
    | patt_free_evar x' => patt_free_evar x'
    | patt_free_svar x' => patt_free_svar x'
    | patt_bound_evar n => patt_bound_evar n
    | patt_bound_svar n => match compare_nat n x with (* TODO simplify - use nat_eqdec or however it is called. We need only two cases *)
                           | Nat_less _ _ _ => patt_bound_svar n
                           | Nat_equal _ _ _ => psi
                           | Nat_greater _ _ _ => patt_bound_svar n (* (pred n) in Leroy's paper *)
                           end
    | patt_sym sigma => patt_sym sigma
    | patt_app phi1 phi2 => patt_app (bsvar_subst phi1 psi x)
                                     (bsvar_subst phi2 psi x)
    | patt_bott => patt_bott
    | patt_imp phi1 phi2 => patt_imp (bsvar_subst phi1 psi x) (bsvar_subst phi2 psi x)
    | patt_exists phi' => patt_exists (bsvar_subst phi' psi x)
    | patt_mu phi' => patt_mu (bsvar_subst phi' psi (S x))
    end.

  Fixpoint bevar_occur (phi : Pattern) (x : db_index) : bool :=
    match phi with
    | patt_free_evar x' => false
    | patt_free_svar x' => false
    | patt_bound_evar n => (bool_decide (n = x))
    | patt_bound_svar n => false
    | patt_sym sigma => false
    | patt_app phi1 phi2 => orb (bevar_occur phi1 x)
                                (bevar_occur phi2 x)
    | patt_bott => false
    | patt_imp phi1 phi2 => orb (bevar_occur phi1 x) (bevar_occur phi2 x)
    | patt_exists phi' => bevar_occur phi' (S x)
    | patt_mu phi' => bevar_occur phi' x
    end.

    Fixpoint bsvar_occur (phi : Pattern) (x : db_index) : bool :=
    match phi with
    | patt_free_evar x' => false
    | patt_free_svar x' => false
    | patt_bound_evar n => false
    | patt_bound_svar n => (bool_decide (n = x))
    | patt_sym sigma => false
    | patt_app phi1 phi2 => orb (bsvar_occur phi1 x)
                                (bsvar_occur phi2 x)
    | patt_bott => false
    | patt_imp phi1 phi2 => orb (bsvar_occur phi1 x) (bsvar_occur phi2 x)
    | patt_exists phi' => bsvar_occur phi' x
    | patt_mu phi' => bsvar_occur phi' (S x)
    end.
    
  (* substitute free element variable x for psi in phi *)
  Fixpoint free_evar_subst (phi psi : Pattern) (x : evar) :=
    match phi with
    | patt_free_evar x' => if evar_eqdec x x' then psi else patt_free_evar x'
    | patt_free_svar X => patt_free_svar X
    | patt_bound_evar x' => patt_bound_evar x'
    | patt_bound_svar X => patt_bound_svar X
    | patt_sym sigma => patt_sym sigma
    | patt_app phi1 phi2 => patt_app (free_evar_subst phi1 psi x)
                                     (free_evar_subst phi2 psi x)
    | patt_bott => patt_bott
    | patt_imp phi1 phi2 => patt_imp (free_evar_subst phi1 psi x) (free_evar_subst phi2 psi x)
    | patt_exists phi' => patt_exists (free_evar_subst phi' psi x)
    | patt_mu phi' => patt_mu (free_evar_subst phi' psi x)
    end.

  Fixpoint free_svar_subst (phi psi : Pattern) (X : svar) :=
    match phi with
    | patt_free_evar x => patt_free_evar x
    | patt_free_svar X' => if svar_eqdec X X' then psi else patt_free_svar X'
    | patt_bound_evar x => patt_bound_evar x
    | patt_bound_svar X' => patt_bound_svar X'
    | patt_sym sigma => patt_sym sigma
    | patt_app phi1 phi2 => patt_app (free_svar_subst phi1 psi X)
                                     (free_svar_subst phi2 psi X)
    | patt_bott => patt_bott
    | patt_imp phi1 phi2 => patt_imp (free_svar_subst phi1 psi X) (free_svar_subst phi2 psi X)
    | patt_exists phi' => patt_exists (free_svar_subst phi' psi X)
    | patt_mu phi' => patt_mu (free_svar_subst phi' psi X)
    end.

  (* instantiate exists x. p or mu x. p with psi for p *)
  Definition instantiate (phi psi : Pattern) :=
    match phi with
    | patt_exists phi' => bevar_subst phi' psi 0
    | patt_mu phi' => bsvar_subst phi' psi 0
    | _ => phi
    end.

  (** The free names of a type are defined as follow.  Notice the
  [exists] and [mu] cases: they do not bind any name. *)

  Definition EVarSet := (@gset evar evar_eqdec evar_countable).
  Definition SVarSet := (@gset svar svar_eqdec svar_countable).

  Fixpoint free_evars (phi : Pattern)
    : EVarSet :=
    match phi with
    | patt_free_evar x => singleton x
    | patt_free_svar X => empty
    | patt_bound_evar x => empty
    | patt_bound_svar X => empty
    | patt_sym sigma => empty
    | patt_app phi1 phi2 => union (free_evars phi1) (free_evars phi2)
    | patt_bott => empty
    | patt_imp phi1 phi2 => union (free_evars phi1) (free_evars phi2)
    | patt_exists phi => free_evars phi
    | patt_mu phi => free_evars phi
    end.

  Fixpoint free_svars (phi : Pattern)
    : SVarSet :=
    match phi with
    | patt_free_evar x => empty
    | patt_free_svar X => singleton X
    | patt_bound_evar x => empty
    | patt_bound_svar X => empty
    | patt_sym sigma => empty
    | patt_app phi1 phi2 => union (free_svars phi1) (free_svars phi2)
    | patt_bott => empty
    | patt_imp phi1 phi2 => union (free_svars phi1) (free_svars phi2)
    | patt_exists phi => free_svars phi
    | patt_mu phi => free_svars phi
    end.

  Fixpoint evar_quantify (x : evar) (level : db_index)
           (p : Pattern) : Pattern :=
    match p with
    | patt_free_evar x' => if evar_eqdec x x' then patt_bound_evar level else patt_free_evar x'
    | patt_free_svar x' => patt_free_svar x'
    | patt_bound_evar x' => patt_bound_evar x'
    | patt_bound_svar X => patt_bound_svar X
    | patt_sym s => patt_sym s
    | patt_app ls rs => patt_app (evar_quantify x level ls) (evar_quantify x level rs)
    | patt_bott => patt_bott
    | patt_imp ls rs => patt_imp (evar_quantify x level ls) (evar_quantify x level rs)
    | patt_exists p' => patt_exists (evar_quantify x (S level) p')
    | patt_mu p' => patt_mu (evar_quantify x level p')
    end.

  Definition exists_quantify (x : evar)
             (p : Pattern) : Pattern :=
    patt_exists (evar_quantify x 0 p).

  Fixpoint size (p : Pattern) : nat :=
    match p with
    | patt_app ls rs => 1 + (size ls) + (size rs)
    | patt_imp ls rs => 1 + (size ls) + (size rs)
    | patt_exists p' => 1 + size p'
    | patt_mu p' => 1 + size p'
    | _ => 0
    end.

  Fixpoint evar_open (k : db_index) (n : evar)
           (p : Pattern) : Pattern :=
    match p with
    | patt_free_evar x => patt_free_evar x
    | patt_free_svar x => patt_free_svar x
    | patt_bound_evar x => if beq_nat x k then patt_free_evar n else patt_bound_evar x
    | patt_bound_svar X => patt_bound_svar X
    | patt_sym s => patt_sym s
    | patt_app ls rs => patt_app (evar_open k n ls) (evar_open k n rs)
    | patt_bott => patt_bott
    | patt_imp ls rs => patt_imp (evar_open k n ls) (evar_open k n rs)
    | patt_exists p' => patt_exists (evar_open (S k) n p')
    | patt_mu p' => patt_mu (evar_open k n p')
    end.
  
  Lemma evar_open_not_occur n x ϕ :
    bevar_occur ϕ n = false ->
    evar_open n x ϕ = ϕ.
  Proof.
    generalize dependent n.
    induction ϕ; simpl; intros dbi H; auto.
    - case_bool_decide; case: (eqb_reflect n dbi); move => H'.
      + inversion H.
      + contradiction.
      + contradiction.
      + reflexivity.
    - apply orb_false_iff in H. destruct H as [H1 H2].
      rewrite -> IHϕ1 by auto.
      rewrite -> IHϕ2 by auto.
      reflexivity.
    - apply orb_false_iff in H. destruct H as [H1 H2].
      rewrite -> IHϕ1 by auto.
      rewrite -> IHϕ2 by auto.
      reflexivity.
    - rewrite -> IHϕ. 2: { assumption.  } reflexivity.
    - rewrite -> IHϕ by auto. auto.
  Qed.
  
  (* The following lemmas are trivial but useful for autorewrite. *)
  Lemma evar_open_free_evar k n x: evar_open k n (patt_free_evar x) = patt_free_evar x.
  Proof. reflexivity. Qed.
  Lemma evar_open_free_svar k n X: evar_open k n (patt_free_svar X) = patt_free_svar X.
  Proof. reflexivity. Qed.
  Lemma evar_open_bound_evar k n x: evar_open k n (patt_bound_evar x) = if beq_nat x k then patt_free_evar n else patt_bound_evar x.
  Proof. reflexivity. Qed.
  Lemma evar_open_bound_svar k n X: evar_open k n (patt_bound_svar X) = patt_bound_svar X.
  Proof. reflexivity. Qed.
  Lemma evar_open_sym k n s: evar_open k n (patt_sym s) = patt_sym s.
  Proof. reflexivity. Qed.
  Lemma evar_open_app k n ls rs: evar_open k n (patt_app ls rs) = patt_app (evar_open k n ls) (evar_open k n rs).
  Proof. reflexivity. Qed.
  Lemma evar_open_bott k n: evar_open k n patt_bott = patt_bott.
  Proof. reflexivity. Qed.
  Lemma evar_open_imp k n ls rs: evar_open k n (patt_imp ls rs) = patt_imp (evar_open k n ls) (evar_open k n rs).
  Proof. reflexivity. Qed.
  Lemma evar_open_exists k n p': evar_open k n (patt_exists p') = patt_exists (evar_open (S k) n p').
  Proof. reflexivity. Qed.
  Lemma evar_open_mu k n p': evar_open k n (patt_mu p') = patt_mu (evar_open k n p').
  Proof. reflexivity. Qed.  
  

  Fixpoint svar_open (k : db_index) (n : svar)
           (p : Pattern) : Pattern :=
    match p with
    | patt_free_evar x => patt_free_evar x
    | patt_free_svar x => patt_free_svar x
    | patt_bound_evar x => patt_bound_evar x
    | patt_bound_svar X => if beq_nat X k then patt_free_svar n else patt_bound_svar X
    | patt_sym s => patt_sym s
    | patt_app ls rs => patt_app (svar_open k n ls) (svar_open k n rs)
    | patt_bott => patt_bott
    | patt_imp ls rs => patt_imp (svar_open k n ls) (svar_open k n rs)
    | patt_exists p' => patt_exists (svar_open k n p')
    | patt_mu p' => patt_mu (svar_open (S k) n p')
    end.


  Lemma svar_open_free_evar k n x: svar_open k n (patt_free_evar x) = patt_free_evar x.
  Proof. reflexivity. Qed.
  Lemma svar_open_free_svar k n X: svar_open k n (patt_free_svar X) = patt_free_svar X.
  Proof. reflexivity. Qed.
  Lemma svar_open_bound_evar k n x: svar_open k n (patt_bound_evar x) = patt_bound_evar x.
  Proof. reflexivity. Qed.
  Lemma svar_open_bound_svar k n X: svar_open k n (patt_bound_svar X) = if beq_nat X k then patt_free_svar n else patt_bound_svar X.
  Proof. reflexivity. Qed.
  Lemma svar_open_sym k n s: svar_open k n (patt_sym s) = patt_sym s.
  Proof. reflexivity. Qed.
  Lemma svar_open_app k n ls rs: svar_open k n (patt_app ls rs) = patt_app (svar_open k n ls) (svar_open k n rs).
  Proof. reflexivity. Qed.
  Lemma svar_open_bott k n: svar_open k n patt_bott = patt_bott.
  Proof. reflexivity. Qed.
  Lemma svar_open_imp k n ls rs: svar_open k n (patt_imp ls rs) = patt_imp (svar_open k n ls) (svar_open k n rs).
  Proof. reflexivity. Qed.
  Lemma svar_open_exists k n p': svar_open k n (patt_exists p') = patt_exists (svar_open k n p').
  Proof. reflexivity. Qed.
  Lemma svar_open_mu k n p': svar_open k n (patt_mu p') = patt_mu (svar_open (S k) n p').
  Proof. reflexivity. Qed.


  (* TODO free_evars, free_svars *)
Class EBinder (ebinder : Pattern -> Pattern)
      (fevo: db_index -> evar -> Pattern -> Pattern )
      (fsvo: db_index -> svar -> Pattern -> Pattern ) :=
    {
      ebinder_evar_open :
        forall k n ϕ, evar_open k n (ebinder ϕ) = fevo k n ϕ ;
                        (*ebinder (evar_open (k + 1) n ϕ) ;*)
      ebinder_svar_open :
        forall k n ϕ, svar_open k n (ebinder ϕ) = fsvo k n ϕ ; (*ebinder (svo a) (svar_open k n ϕ) ;*)
    }.

  Class SBinder (sbinder : Pattern -> Pattern) :=
    {
      sbinder_evar_open :
        forall k n ϕ, evar_open k n (sbinder ϕ) = sbinder (evar_open k n ϕ) ;
      sbinder_svar_open :
        forall k n ϕ, svar_open k n (sbinder ϕ) = sbinder (svar_open (S k) n ϕ) ;
    }.

  (* Non-variable nullary operation *)
  Class NVNullary (nvnullary : Pattern) :=
    {
      nvnullary_evar_open :
        forall k n, evar_open k n nvnullary = nvnullary ;
      nvnullary_svar_open :
        forall k n, svar_open k n nvnullary = nvnullary ;
    }.

  Class Unary (patt : Pattern -> Pattern) :=
    {
      unary_evar_open :
        forall k n ϕ, evar_open k n (patt ϕ) = patt (evar_open k n ϕ) ;
      unary_svar_open :
        forall k n ϕ, svar_open k n (patt ϕ) = patt (svar_open k n ϕ) ;
    }.

  Class Binary (binary : Pattern -> Pattern -> Pattern) :=
    {
      binary_evar_open :
        forall k n ϕ₁ ϕ₂, evar_open k n (binary ϕ₁ ϕ₂) = binary (evar_open k n ϕ₁) (evar_open k n ϕ₂) ;
      binary_svar_open :
        forall k n ϕ₁ ϕ₂, svar_open k n (binary ϕ₁ ϕ₂) = binary (svar_open k n ϕ₁) (svar_open k n ϕ₂) ;
    }.

  (* TODO the same for svar_open *)
  Definition simpl_evar_open :=
    (@ebinder_evar_open,
     @sbinder_evar_open,
     @nvnullary_evar_open,
     @unary_evar_open,
     @binary_evar_open
    ).

  Definition simpl_svar_open :=
    (@ebinder_svar_open,
     @sbinder_svar_open,
     @nvnullary_svar_open,
     @unary_svar_open,
     @binary_svar_open
    ).
  

  #[global]
  Instance EBinder_exists : EBinder patt_exists _ _ :=
    {|
       ebinder_evar_open := evar_open_exists ;
       ebinder_svar_open := svar_open_exists ;
    |}.

  #[global]
  Instance SBinder_mu : SBinder patt_mu :=
    {|
       sbinder_evar_open := evar_open_mu ;
       sbinder_svar_open := svar_open_mu ;
    |}.


  #[global]
  Instance NVNullary_bott : NVNullary patt_bott :=
    {|
       nvnullary_evar_open := evar_open_bott ;
       nvnullary_svar_open := svar_open_bott ;
    |}.

  #[global]
  Instance NVNullary_sym s : NVNullary (patt_sym s) :=
    {|
       nvnullary_evar_open := λ k n, @evar_open_sym k n s ;
       nvnullary_svar_open := λ k n, @svar_open_sym k n s ;
    |}.

  #[global]
  Instance Binary_app : Binary patt_app :=
    {|
       binary_evar_open := evar_open_app ;
       binary_svar_open := svar_open_app ;
    |}.

  #[global]
  Instance Binary_imp : Binary patt_imp :=
    {|
       binary_evar_open := evar_open_imp ;
       binary_svar_open := svar_open_imp ;
    |}.
  
  Lemma evar_open_size :
    forall (k : db_index) (n : evar) (p : Pattern),
      size p = size (evar_open k n p).
  Proof.
    intros. generalize dependent k.
    induction p; intros; simpl; try reflexivity.
    destruct (n0 =? k); reflexivity.
    rewrite (IHp1 k); rewrite (IHp2 k); reflexivity.
    rewrite (IHp1 k); rewrite (IHp2 k); reflexivity.
    rewrite (IHp (S k)); reflexivity.
    rewrite (IHp k); reflexivity.
  Qed.

  Lemma svar_open_size :
    forall (k : db_index) (n : svar) (p : Pattern),
      size p = size (svar_open k n p).
  Proof.
    intros. generalize dependent k.
    induction p; intros; simpl; try reflexivity.
    destruct (n0 =? k); reflexivity.
    rewrite (IHp1 k); rewrite (IHp2 k); reflexivity.
    rewrite (IHp1 k); rewrite (IHp2 k); reflexivity.
    rewrite (IHp k); reflexivity.
    rewrite (IHp (S k)); reflexivity.
  Qed.

  Inductive positive_occurrence_named : svar -> Pattern -> Prop :=
  | po_free_evar (x : evar) (sv : svar) : positive_occurrence_named sv (patt_free_evar x)
  | po_free_svar (x : svar) (sv : svar) : positive_occurrence_named sv (patt_free_svar x)
  | po_bound_evar (m : db_index) (sv : svar) : positive_occurrence_named sv (patt_bound_evar m)
  | po_bound_svar (m : db_index) (sv : svar) : positive_occurrence_named sv (patt_bound_svar m)
  | po_const (sigma : symbols) (sv : svar) :
      positive_occurrence_named sv (patt_sym sigma)
  | po_app (phi1 phi2 : Pattern) (sv : svar) :
      positive_occurrence_named sv phi1 -> positive_occurrence_named sv phi2 ->
      positive_occurrence_named sv (patt_app phi1 phi2)
  | po_bott (sv : svar) : positive_occurrence_named sv patt_bott
  | po_impl (phi1 phi2 : Pattern) (sv : svar) :
      negative_occurrence_named sv phi1 -> positive_occurrence_named sv phi2 ->
      positive_occurrence_named sv (patt_imp phi1 phi2)
  | po_exists (phi : Pattern) (sv : svar) :
      positive_occurrence_named sv phi ->
      positive_occurrence_named sv (patt_exists phi)
  | po_mu (phi : Pattern) (sv : svar) :
      positive_occurrence_named sv phi ->
      positive_occurrence_named sv (patt_mu phi)
  with negative_occurrence_named : svar -> Pattern -> Prop :=
  | no_free_evar (x : evar) (sv : svar) : negative_occurrence_named sv (patt_free_evar x)
  | no_free_svar (x : svar) (sv : svar) : x <> sv -> negative_occurrence_named sv (patt_free_svar x)
  | no_bound_evar (m : db_index) (sv : svar) :  negative_occurrence_named sv (patt_bound_evar m)
  | no_bound_svar (m : db_index) (sv : svar) :  negative_occurrence_named sv (patt_bound_svar m)
  | no_const (sigma : symbols) (sv : svar) :
      negative_occurrence_named sv (patt_sym sigma)
  | no_app (phi1 phi2 : Pattern) (sv : svar) :
      negative_occurrence_named sv phi1 -> negative_occurrence_named sv phi2 ->
      negative_occurrence_named sv (patt_app phi1 phi2)
  | no_bott (sv : svar) :  negative_occurrence_named sv patt_bott
  | no_impl (phi1 phi2 : Pattern) (sv : svar) :
      positive_occurrence_named sv phi1 ->  negative_occurrence_named sv phi2 ->
      negative_occurrence_named sv (patt_imp phi1 phi2)
  | no_exists (phi : Pattern) (sv : svar) :
      negative_occurrence_named sv phi ->
      negative_occurrence_named sv (patt_exists phi)
  | no_mu (phi : Pattern) (sv : svar) :
      negative_occurrence_named sv phi ->
      negative_occurrence_named sv (patt_mu phi)
  .
  (* Cares only about set variables *)
  Inductive positive_occurrence_db : db_index -> Pattern -> Prop :=
  | podb_free_evar (x : evar) (n : db_index) : positive_occurrence_db n (patt_free_evar x)
  | podb_free_svar (x : svar) (n : db_index) : positive_occurrence_db n (patt_free_svar x)
  | podb_bound_evar (m : db_index) (n : db_index) : positive_occurrence_db n (patt_bound_evar m)
  | podb_bound_svar (m : db_index) (n : db_index) : positive_occurrence_db n (patt_bound_svar m)
  | podb_const (sigma : symbols) (n : db_index) :
      positive_occurrence_db n (patt_sym sigma)
  | podb_app (phi1 phi2 : Pattern) (n : db_index) :
      positive_occurrence_db n phi1 -> positive_occurrence_db n phi2 ->
      positive_occurrence_db n (patt_app phi1 phi2)
  | podb_bott (n : db_index) : positive_occurrence_db n patt_bott
  | podb_impl (phi1 phi2 : Pattern) (n : db_index) :
      negative_occurrence_db n phi1 -> positive_occurrence_db n phi2 ->
      positive_occurrence_db n (patt_imp phi1 phi2)
  | podb_exists (phi : Pattern) (n : db_index) :
      positive_occurrence_db n phi ->
      positive_occurrence_db n (patt_exists phi)
  | podb_mu (phi : Pattern) (n : db_index) :
      positive_occurrence_db (S n) phi ->
      positive_occurrence_db n (patt_mu phi)
  with negative_occurrence_db : db_index -> Pattern -> Prop :=
  | nodb_free_evar (x : evar) (n : db_index) : negative_occurrence_db n (patt_free_evar x)
  | nodb_free_svar (x : svar) (n : db_index) : negative_occurrence_db n (patt_free_svar x)
  | nodb_bound_evar (m : db_index) (n : db_index) : negative_occurrence_db n (patt_bound_evar m)
  | nodb_bound_svar (m : db_index) (n : db_index) : n <> m -> negative_occurrence_db n (patt_bound_svar m)
  | nodb_const (sigma : symbols) (n : db_index) :
      negative_occurrence_db n (patt_sym sigma)
  | nodb_app (phi1 phi2 : Pattern) (n : db_index) :
      negative_occurrence_db n phi1 -> negative_occurrence_db n phi2 ->
      negative_occurrence_db n (patt_app phi1 phi2)
  | nodb_bott (n : db_index) :  negative_occurrence_db n patt_bott
  | nodb_impl (phi1 phi2 : Pattern) (n : db_index) :
      positive_occurrence_db n phi1 ->  negative_occurrence_db n phi2 ->
      negative_occurrence_db n (patt_imp phi1 phi2)
  | nodb_exists (phi : Pattern) (n : db_index) :
      negative_occurrence_db n phi ->
      negative_occurrence_db n (patt_exists phi)
  | nodb_mu (phi : Pattern) (n : db_index) :
      negative_occurrence_db (S n) phi ->
      negative_occurrence_db n (patt_mu phi)
  .

  (* for bound set variables *)
  Fixpoint no_negative_occurrence_db_b (dbi : db_index) (ϕ : Pattern) : bool :=
    match ϕ with
    | patt_free_evar _ | patt_free_svar _ | patt_bound_evar _ | patt_sym _ | patt_bott => true
    | patt_bound_svar n => true
    | patt_app ϕ₁ ϕ₂ => no_negative_occurrence_db_b dbi ϕ₁ && no_negative_occurrence_db_b dbi ϕ₂
    | patt_imp ϕ₁ ϕ₂ => no_positive_occurrence_db_b dbi ϕ₁ && no_negative_occurrence_db_b dbi ϕ₂
    | patt_exists ϕ' => no_negative_occurrence_db_b dbi ϕ'
    | patt_mu ϕ' => no_negative_occurrence_db_b (S dbi) ϕ'
    end
  with
  no_positive_occurrence_db_b (dbi : db_index) (ϕ : Pattern) : bool :=
    match ϕ with
    | patt_free_evar _ | patt_free_svar _ | patt_bound_evar _ | patt_sym _ | patt_bott => true
    | patt_bound_svar n => negb (n =? dbi)
    | patt_app ϕ₁ ϕ₂ => no_positive_occurrence_db_b dbi ϕ₁ && no_positive_occurrence_db_b dbi ϕ₂
    | patt_imp ϕ₁ ϕ₂ => no_negative_occurrence_db_b dbi ϕ₁ && no_positive_occurrence_db_b dbi ϕ₂
    | patt_exists ϕ' => no_positive_occurrence_db_b dbi ϕ'
    | patt_mu ϕ' => no_positive_occurrence_db_b (S dbi) ϕ'                                  
    end.

  Lemma Private_no_negative_positive_occurrence_P dbi ϕ :
    prod (reflect (positive_occurrence_db dbi ϕ) (no_negative_occurrence_db_b dbi ϕ))
         (reflect (negative_occurrence_db dbi ϕ) (no_positive_occurrence_db_b dbi ϕ)).
  Proof.
    move: dbi.
    induction ϕ; intros dbi; simpl; constructor;
      try (apply ReflectT; subst; constructor);
      try (
          destruct (fst (IHϕ1 dbi)), (snd (IHϕ1 dbi)), (fst (IHϕ2 dbi)), (snd (IHϕ2 dbi)); simpl;
          try (apply ReflectT; subst; constructor; auto);
          try (apply ReflectF; intros Contra; inversion Contra; subst; contradiction)
        ).
    1: {  destruct (Nat.eqb_spec n dbi); simpl.
      + apply ReflectF. intros Contra. inversion Contra. subst. contradiction.
      + apply ReflectT. constructor. apply nesym.  assumption.  }
    1,2: (
          destruct (fst (IHϕ dbi)), (snd (IHϕ dbi)); simpl;
          try (apply ReflectT; subst; constructor; auto);
          try (apply ReflectF; intros Contra; inversion Contra; subst; contradiction)
         ).

    1,2: (  destruct (fst (IHϕ (S dbi))), (snd (IHϕ (S dbi))); simpl;
            assert (Heq: dbi+1 = S dbi); try lia;
           try (apply ReflectT; subst; try constructor; try rewrite -> Heq in *; auto);
           try (apply ReflectF; intros Contra; inversion Contra; subst; try rewrite -> Heq in *; contradiction)
         ).
  Qed.

  Lemma no_negative_occurrence_P dbi ϕ :
    reflect (positive_occurrence_db dbi ϕ) (no_negative_occurrence_db_b dbi ϕ).
  Proof.
    apply Private_no_negative_positive_occurrence_P.
  Qed.

  Lemma no_positive_occurrence_P dbi ϕ :
    reflect (negative_occurrence_db dbi ϕ) (no_positive_occurrence_db_b dbi ϕ).
  Proof.
    apply Private_no_negative_positive_occurrence_P.
  Qed.

  (* Lemmas about opening and positive occurrence *)
  Lemma positive_negative_occurrence_db_evar_open : forall (phi : Pattern) (db1 db2 : db_index) (x : evar),
      (*le db1 db2 ->*)
      (positive_occurrence_db db1 phi -> positive_occurrence_db db1 (evar_open db2 x phi))
      /\ (negative_occurrence_db db1 phi -> negative_occurrence_db db1 (evar_open db2 x phi)).
  Proof.
    induction phi; intros; simpl; split; intros; try constructor; try inversion H; subst; try firstorder.
    * destruct (n =? db2); intros. constructor. assumption.
    * destruct (n =? db2); intros. constructor. assumption.
  Qed.

  Lemma positive_occurrence_db_evar_open : forall (phi : Pattern) (db1 db2 : db_index) (x : evar),
      positive_occurrence_db db1 phi -> positive_occurrence_db db1 (evar_open db2 x phi).
  Proof.
    intros.
    pose proof (H' := positive_negative_occurrence_db_evar_open phi db1 db2 x).
    firstorder.
  Qed.

  Lemma negative_occurrence_db_evar_open : forall (phi : Pattern) (db1 db2 : db_index) (x : evar),
      negative_occurrence_db db1 phi -> negative_occurrence_db db1 (evar_open db2 x phi).
  Proof.
    intros.
    pose proof (H' := positive_negative_occurrence_db_evar_open phi db1 db2 x).
    firstorder.
  Qed.

  Lemma no_negative_occurrence_evar_open phi db1 db2 x:
    no_negative_occurrence_db_b db1 phi ->
    no_negative_occurrence_db_b db1 (evar_open db2 x phi).
  Proof.
    intros H.
    eapply elimT in H.
    2: apply no_negative_occurrence_P.
    eapply introT.
    apply no_negative_occurrence_P.
    apply positive_occurrence_db_evar_open.
    apply H.
  Qed.

  Lemma no_positive_occurrence_evar_open phi db1 db2 x:
    no_positive_occurrence_db_b db1 phi ->
    no_positive_occurrence_db_b db1 (evar_open db2 x phi).
  Proof.
    intros H.
    eapply elimT in H.
    2: apply no_positive_occurrence_P.
    eapply introT.
    apply no_positive_occurrence_P.
    apply negative_occurrence_db_evar_open.
    apply H.
  Qed.

  (* TODO replace with a boolean version - that enables us to prove by computation. *)
  Fixpoint well_formed_positive (phi : Pattern) : bool :=
    match phi with
    | patt_free_evar _ => true
    | patt_free_svar _ => true
    | patt_bound_evar _ => true
    | patt_bound_svar _ => true
    | patt_sym _ => true
    | patt_app psi1 psi2 => well_formed_positive psi1 && well_formed_positive psi2
    | patt_bott => true
    | patt_imp psi1 psi2 => well_formed_positive psi1 && well_formed_positive psi2
    | patt_exists psi => well_formed_positive psi
    | patt_mu psi => no_negative_occurrence_db_b 0 psi && well_formed_positive psi
    end.
  
  Fixpoint well_formed_closed_aux (phi : Pattern) (max_ind_evar : db_index) (max_ind_svar : db_index) : bool :=
    match phi with
    | patt_free_evar _ => true
    | patt_free_svar _ => true
    | patt_bound_evar n => n <? max_ind_evar
    | patt_bound_svar n => n <? max_ind_svar
    | patt_sym _ => true
    | patt_app psi1 psi2 => well_formed_closed_aux psi1 max_ind_evar max_ind_svar &&
                            well_formed_closed_aux psi2 max_ind_evar max_ind_svar
    | patt_bott => true
    | patt_imp psi1 psi2 => well_formed_closed_aux psi1 max_ind_evar max_ind_svar &&
                            well_formed_closed_aux psi2 max_ind_evar max_ind_svar
    | patt_exists psi => well_formed_closed_aux psi (S max_ind_evar) max_ind_svar
    | patt_mu psi => well_formed_closed_aux psi max_ind_evar (S max_ind_svar)
    end.
  Definition well_formed_closed (phi : Pattern) := well_formed_closed_aux phi 0 0.

  Lemma well_formed_closed_aux_ind (phi : Pattern) (ind_evar1 ind_evar2 ind_svar1 ind_svar2: db_index) :
    ind_evar1 <= ind_evar2 -> ind_svar1 <= ind_svar2  
    -> well_formed_closed_aux phi ind_evar1 ind_svar1 
    -> well_formed_closed_aux phi ind_evar2 ind_svar2.
  Proof.
    intros.
    generalize dependent ind_evar1. generalize dependent ind_evar2.
    generalize dependent ind_svar1. generalize dependent ind_svar2.
    induction phi; intros ind_svar_2 ind_svar_1 Hleqsvar ind_evar_2 ind_evar_1 Heqevar H;
      simpl in *; try lia; auto. Search "<?" "<".
    - apply Nat.ltb_lt in H. apply Nat.ltb_lt. lia.
    - apply Nat.ltb_lt in H. apply Nat.ltb_lt. lia.
    - apply andb_true_iff in H. destruct H as [H1 H2].
      erewrite IHphi1. erewrite IHphi2. reflexivity. eassumption. eassumption. rewrite H2. reflexivity.
      eassumption. eassumption. rewrite H1. reflexivity.
    - apply andb_true_iff in H. destruct H as [H1 H2].
      erewrite IHphi1. 2,3: eassumption. erewrite IHphi2. 2,3: eassumption.
      2,3: assumption. reflexivity.
    - eapply (IHphi ind_svar_2 ind_svar_1 _  (S ind_evar_2) (S ind_evar_1)).
      + lia.
      + assumption.
    - eapply (IHphi (S ind_svar_2) (S ind_svar_1) _  ind_evar_2 ind_evar_1).
      + lia.
      + assumption.
        Unshelve.
        lia. lia.
  Qed.

  Definition well_formed (phi : Pattern) := well_formed_positive phi && well_formed_closed phi.

  (* From https://www.chargueraud.org/research/2009/ln/main.pdf in 3.3 (body def.) *)
  Definition wfc_body_ex phi  := forall x, 
      ~ elem_of x (free_evars phi) -> well_formed_closed (evar_open 0 x phi).

  (*Helper lemma for wf_ex_to_wf_body *)
  Lemma wfc_aux_body_ex_imp1:
    forall phi n n' x,
      well_formed_closed_aux phi (S n) n'
      ->
      well_formed_closed_aux (evar_open n x phi) n n'.
  Proof using .
    - induction phi; intros; try lia; auto.
      * simpl. inversion H. apply Nat.ltb_lt in H1. destruct (n=?n0) eqn:Heq.
        -- reflexivity.
        -- simpl. apply Nat.ltb_lt. apply beq_nat_false in Heq. lia.
      * simpl. simpl in H. apply andb_true_iff in H. destruct H as [H1 H2].
        rewrite IHphi1. apply H1. rewrite IHphi2. apply H2. reflexivity.
      * simpl. simpl in H. apply andb_true_iff in H. destruct H as [H1 H2].
        rewrite IHphi1. apply H1. rewrite IHphi2. apply H2. reflexivity.
      * simpl. simpl in H. rewrite IHphi. apply H. reflexivity.
      * simpl. simpl in H. rewrite IHphi. apply H. reflexivity.
  Qed.

  (*Helper lemma for wf_body_to_wf_ex*)
  Lemma wfc_aux_body_ex_imp2:
    forall phi n n' x,
      well_formed_closed_aux (evar_open n x phi) n n'
      ->
      well_formed_closed_aux phi (S n) n'.
  Proof using .
    induction phi; firstorder.
    - simpl. simpl in H. destruct (n =? n0) eqn:P.
      + apply beq_nat_true in P. rewrite P. apply Nat.ltb_lt. lia.
      + simpl in H. apply Nat.ltb_lt. apply Nat.ltb_lt in H.
        apply beq_nat_false in P. lia.
    - simpl in H. simpl.
      apply andb_true_iff in H. destruct H as [H1 H2].
      erewrite IHphi1. 2: apply H1.
      erewrite IHphi2. 2: apply H2.
      reflexivity.
    - simpl in H. simpl.
      apply andb_true_iff in H. destruct H as [H1 H2].
      erewrite IHphi1. 2: apply H1.
      erewrite IHphi2. 2: apply H2.
      reflexivity.
  Qed.

  Lemma wfc_aux_body_iff: 
    forall phi n n' x,
      well_formed_closed_aux phi (S n) n'
      <->
      well_formed_closed_aux (evar_open n x phi) n n'.
  Proof.
    split.
    apply wfc_aux_body_ex_imp1.
    apply wfc_aux_body_ex_imp2.
  Qed.

  (*If (ex, phi) is closed, then its body is closed too*)
  Lemma wfc_ex_to_wfc_body:
    forall phi, well_formed_closed (patt_exists phi) -> wfc_body_ex phi.
  Proof.
    intros.
    unfold wfc_body_ex. intros.
    unfold well_formed_closed in *. simpl in H.
    apply wfc_aux_body_ex_imp1. auto.
  Qed.



  Definition fresh_evar ϕ := evar_fresh (elements (free_evars ϕ)).
  Definition fresh_svar ϕ := svar_fresh (elements (free_svars ϕ)).

  Definition evar_is_fresh_in x ϕ := x ∉ free_evars ϕ.
  Definition svar_is_fresh_in x ϕ := x ∉ free_svars ϕ.

  Lemma set_evar_fresh_is_fresh' (S : EVarSet) : evar_fresh (elements S) ∉ S.
  Proof.
    intros H.
    pose proof (Hf := @evar_fresh_is_fresh _ (elements S)).
    unfold elements in H. unfold gset_elements in H.
    apply gset_to_list_elem_of in H.
    unfold elements in Hf. unfold gset_elements in Hf.
    apply elem_of_list_In in H. contradiction.
  Qed.
  
  Lemma set_evar_fresh_is_fresh ϕ : evar_is_fresh_in (fresh_evar ϕ) ϕ.
  Proof.
    unfold evar_is_fresh_in.
    unfold fresh_evar.
    apply set_evar_fresh_is_fresh'.
  Qed.

  Hint Resolve set_evar_fresh_is_fresh : core.

  Lemma set_svar_fresh_is_fresh' (S : SVarSet) : svar_fresh (elements S) ∉ S.
  Proof.
    intros H.
    pose proof (Hf := @svar_fresh_is_fresh _ (elements S)).
    unfold elements in H. unfold gset_elements in H.
    apply gset_to_list_elem_of in H.
    unfold elements in Hf. unfold gset_elements in Hf.
    apply elem_of_list_In in H. contradiction.
  Qed.
  
  Lemma set_svar_fresh_is_fresh ϕ : svar_is_fresh_in (fresh_svar ϕ) ϕ.
  Proof.
    unfold svar_is_fresh_in.
    unfold fresh_svar.
    apply set_svar_fresh_is_fresh'.
  Qed.

  Hint Resolve set_svar_fresh_is_fresh : core.

  Lemma evar_is_fresh_in_richer' x ϕ B:
    free_evars ϕ ⊆ B ->
    x ∉ B ->
    evar_is_fresh_in x ϕ.
  Proof.
    intros Hsub.
    unfold evar_is_fresh_in.
    intros Hnotin.
    pose proof (Hsub' := (iffLR (elem_of_subseteq _ B) Hsub)).
    auto.
  Qed.
  
  Lemma evar_is_fresh_in_richer x ϕ₁ ϕ₂:
    free_evars ϕ₁ ⊆ free_evars ϕ₂ ->
    evar_is_fresh_in x ϕ₂ ->
    evar_is_fresh_in x ϕ₁.
  Proof.
    intros Hsub Hnotin.
    eapply evar_is_fresh_in_richer'; auto.
  Qed.

  Lemma svar_is_fresh_in_richer' X ϕ B:
    free_svars ϕ ⊆ B ->
    X ∉ B ->
    svar_is_fresh_in X ϕ.
  Proof.
    intros Hsub.
    unfold svar_is_fresh_in.
    intros Hnotin.
    pose proof (Hsub' := (iffLR (elem_of_subseteq _ B) Hsub)).
    auto.
  Qed.

  Lemma svar_is_fresh_in_richer X ϕ₁ ϕ₂:
    free_svars ϕ₁ ⊆ free_svars ϕ₂ ->
    svar_is_fresh_in X ϕ₂ ->
    svar_is_fresh_in X ϕ₁.
  Proof.
    intros Hsub Hnotin.
    eapply svar_is_fresh_in_richer'; auto.
  Qed.
  
  (*
  Lemma fresh_neq_fresh_l ϕ₁ ϕ₂ :
    (*~ evar_is_fresh_in (fresh_evar ϕ₁) ϕ₂ ->*)
    free_evars ϕ₁ ⊈
    fresh_evar ϕ₁ ≠ fresh_evar ϕ₂.
  Proof.
    intros H.
    unfold fresh_evar at 2.
   *)
  
  Hint Resolve evar_is_fresh_in_richer : core.

  Lemma evar_is_fresh_in_evar_quantify x n phi:
    evar_is_fresh_in x (evar_quantify x n phi).
  Proof.
    move: n.
    unfold evar_is_fresh_in.
    induction phi; intros n'; simpl; try apply not_elem_of_empty.
    - destruct (evar_eqdec x x0); simpl.
      + apply not_elem_of_empty.
      + apply not_elem_of_singleton_2. assumption.
    - apply not_elem_of_union.
      split; auto.
    - apply not_elem_of_union.
      split; auto.
    - auto.
    - auto.
  Qed.
  
      
                     

  
  (*If phi is a closed body, then (ex, phi) is closed too*)
  Lemma wfc_body_to_wfc_ex:
    forall phi, wfc_body_ex phi -> well_formed_closed (patt_exists phi).
  Proof.
    intros. unfold wfc_body_ex in H. unfold well_formed_closed. simpl.
    unfold well_formed_closed in H.
    apply (@wfc_aux_body_ex_imp2 phi 0 0 (fresh_evar phi)) in H. exact H.
    clear H.
    apply set_evar_fresh_is_fresh.
  Qed.

  (* From https://www.chargueraud.org/research/2009/ln/main.pdf in 3.4 (lc_abs_iff_body) *)
  (*Conclusion*)
  Lemma wfc_body_wfc_ex_iff: 
    forall phi,
      well_formed_closed (patt_exists phi) <-> wfc_body_ex phi.
  Proof.
    split.
    - apply wfc_ex_to_wfc_body.
    - apply wfc_body_to_wfc_ex.
  Qed.

  (*Similarly to the section above but with mu*)
  Definition wfc_body_mu phi := forall X, 
      X ∉ (free_svars phi) -> well_formed_closed (svar_open 0 X phi).

  (*Helper for wfc_mu_to_wfc_body*)
  Lemma wfc_aux_body_mu_imp1:
    forall phi n n' X,
      well_formed_closed_aux phi n (S n')
      ->
      well_formed_closed_aux (svar_open n' X phi) n n'.
  Proof.
    - induction phi; intros; try lia; auto.
      * simpl. inversion H. apply Nat.ltb_lt in H1. destruct (n=?n') eqn:Heq.
        -- reflexivity.
        -- simpl. apply Nat.ltb_lt. apply beq_nat_false in Heq. lia.
      * simpl. simpl in H. apply andb_true_iff in H. destruct H as [H1 H2].
        rewrite IHphi1. apply H1. rewrite IHphi2. apply H2. reflexivity.
      * simpl. simpl in H. apply andb_true_iff in H. destruct H as [H1 H2].
        rewrite IHphi1. apply H1. rewrite IHphi2. apply H2. reflexivity.
      * simpl. simpl in H. rewrite IHphi. apply H. reflexivity.
      * simpl. simpl in H. rewrite IHphi. apply H. reflexivity.
  Qed.

  (*Helper for *)
  Lemma wfc_aux_body_mu_imp2:
    forall phi n n' X,
      well_formed_closed_aux (svar_open n' X phi) n n'
      ->
      well_formed_closed_aux phi n (S n').
  Proof.
    induction phi; firstorder.
    - simpl. simpl in H. destruct (n =? n') eqn:P; simpl in H.
      + apply beq_nat_true in P. rewrite P. apply Nat.ltb_lt. lia.
      + apply Nat.ltb_lt. apply Nat.ltb_lt in H. lia.
    - simpl in H. simpl.
      apply andb_true_iff in H. destruct H as [H1 H2].
      erewrite IHphi1. 2: apply H1.
      erewrite IHphi2. 2: apply H2.
      reflexivity.
    -  simpl in H. simpl.
       apply andb_true_iff in H. destruct H as [H1 H2].
       erewrite IHphi1. 2: apply H1.
       erewrite IHphi2. 2: apply H2.
       reflexivity.
  Qed.

    Lemma wfc_aux_extend:
    forall phi n n' m m',
      well_formed_closed_aux phi n m
      -> n <= n' -> m <= m'
      -> well_formed_closed_aux phi n' m'.
  Proof.
    intros.
    generalize dependent n. generalize dependent n'.
    generalize dependent m. generalize dependent m'.
    induction phi; intros; try lia; auto.
    * simpl. inversion H. apply Nat.ltb_lt. apply Nat.ltb_lt in H3. lia.
    * simpl. inversion H. apply Nat.ltb_lt. apply Nat.ltb_lt in H3. lia.
    * simpl. simpl in H. apply andb_true_iff in H. destruct H as [H2 H3].
      apply andb_true_iff. split. erewrite IHphi1; eauto. erewrite IHphi2; eauto.
    * simpl. simpl in H. apply andb_true_iff in H. destruct H as [H2 H3].
      apply andb_true_iff. split. erewrite IHphi1; eauto. erewrite IHphi2; eauto.
    * simpl. simpl in H. erewrite IHphi with (n := S n) (m := m); eauto. lia.
    * simpl. simpl in H. erewrite IHphi with (n := n) (m := S m); eauto. lia.
  Qed.

  Lemma wfc_aux_body_mu_imp_bsvar_subst:
    forall phi psi n n',
      well_formed_closed_aux phi n (S n')
      -> well_formed_closed_aux psi n n'
      -> well_formed_closed_aux (bsvar_subst phi psi n') n n'.
  Proof.
    - intros. generalize dependent n. generalize dependent n'. generalize dependent psi.
      induction phi; intros; try lia; auto.
      * simpl. inversion H. apply Nat.ltb_lt in H2. destruct (compare_nat n n').
        -- simpl. apply Nat.ltb_lt. assumption.
        -- assumption.
        -- simpl. apply Nat.ltb_lt. lia.
      * simpl. simpl in H. apply andb_true_iff in H. destruct H as [H1 H2].
        rewrite IHphi1. apply H1. assumption. rewrite IHphi2. apply H2. assumption.
        reflexivity.
      * simpl. simpl in H. apply andb_true_iff in H. destruct H as [H1 H2].
        rewrite IHphi1. apply H1. assumption. rewrite IHphi2. apply H2. assumption.
        reflexivity.
      * simpl. simpl in H. rewrite IHphi. assumption.
        eapply wfc_aux_extend; eauto. auto.
      * simpl. simpl in H.
        rewrite IHphi. apply H.
        eapply wfc_aux_extend; eauto. reflexivity.
  Qed.

  (*If (mu, phi) is closed, then its body is closed too*)
  Lemma wfc_mu_to_wfc_body:
    forall phi, well_formed_closed (patt_mu phi) -> wfc_body_mu phi.
  Proof.
    intros. 
    unfold wfc_body_mu. intros.
    unfold well_formed_closed in *. simpl in H.
    apply wfc_aux_body_mu_imp1. auto.
  Qed.

  (*If phi is a closed body, then (mu, phi) is closed too*)
  Lemma wfc_body_to_wfc_mu:
    forall phi, wfc_body_mu phi -> well_formed_closed (patt_mu phi).
  Proof.
    intros. unfold wfc_body_mu in H. unfold well_formed_closed. simpl.
    unfold well_formed_closed in H.
    apply wfc_aux_body_mu_imp2 with (X := fresh_svar phi) in H. exact H.
    apply set_svar_fresh_is_fresh.
  Qed.

  (* From https://www.chargueraud.org/research/2009/ln/main.pdf in 3.4 (lc_abs_iff_body) *)
  (*Conclusion*)
  Lemma wfc_body_wfc_mu_iff: 
    forall phi (X : svar),
      well_formed_closed (patt_mu phi) <-> wfc_body_mu phi.
  Proof.
    split.
    - apply wfc_mu_to_wfc_body.
    - apply wfc_body_to_wfc_mu.
  Qed.

  (* Similarly with positiveness *)
  Definition wfp_body_ex phi := forall x,
      x ∉ (free_evars phi) -> well_formed_positive (evar_open 0 x phi).

  Lemma wfp_evar_open : forall phi x n,
      well_formed_positive phi ->
      well_formed_positive (evar_open n x phi).
  Proof.
    induction phi; simpl in *; intros x' n' H; auto.
    - intros. simpl. destruct (n =? n') eqn:P.
      + simpl. trivial.
      + simpl. trivial.
    - apply andb_prop in H.
      destruct H as [H1 H2].
      apply andb_true_iff.
      split.
      + apply IHphi1. apply H1.
      + apply IHphi2. apply H2.
    - apply andb_true_iff in H.
      destruct H as [H1 H2].
      apply andb_true_iff.
      split.
      * apply IHphi1,H1.
      * apply IHphi2,H2.
    - apply andb_true_iff in H.
      destruct H as [H1 H2].
      apply andb_true_iff.
      split.
      eapply introT.
      apply no_negative_occurrence_P.      
      apply positive_occurrence_db_evar_open.
      eapply elimT.
      apply no_negative_occurrence_P.
      apply H1.
      apply IHphi. apply H2.
  Qed.

  Lemma wfp_ex_to_wfp_body: forall phi,
      well_formed_positive (patt_exists phi) ->
      wfp_body_ex phi.
  Proof.
    unfold wfp_body_ex. intros. apply wfp_evar_open. simpl in H. assumption.
  Qed.

  (* Connection between bodies and well-formedness *)
  Definition wf_body_ex phi := forall x, 
      x ∉ (free_evars phi) -> well_formed (evar_open 0 x phi).

  (* This might be useful in soundness cases prop_ex_left/right *)
  Lemma wf_ex_to_wf_body: forall phi,
      well_formed (patt_exists phi) ->
      wf_body_ex phi.
  Proof.
    unfold wf_body_ex. intros. unfold well_formed in *.
    apply andb_true_iff in H.
    destruct H as [H1 H2].
    rewrite (@wfp_ex_to_wfp_body phi H1). assumption.
    rewrite (@wfc_ex_to_wfc_body phi H2). assumption.
    reflexivity.
  Qed.

  Inductive well_formed_closed_induc : Pattern -> Prop :=
  | wfc_free_evar : forall (x : evar), well_formed_closed_induc (patt_free_evar x)
  | wfc_free_svar : forall (X : svar), well_formed_closed_induc (patt_free_svar X)
  | wfc_sym       : forall (sym : symbols), well_formed_closed_induc (patt_sym sym)
  | wfc_app       : forall (phi psi : Pattern), well_formed_closed_induc phi 
                                                -> well_formed_closed_induc psi -> well_formed_closed_induc (patt_app phi psi)
  | wfc_bott      : well_formed_closed_induc patt_bott
  | wfc_imp       : forall (phi psi : Pattern), well_formed_closed_induc phi 
                                                -> well_formed_closed_induc psi -> well_formed_closed_induc (patt_imp phi psi)
  | wfc_ex        : forall phi : Pattern, 
      (forall (x : evar), 
          x ∉ (free_evars phi) ->
          well_formed_closed_induc (evar_open 0 x phi))
      -> 
      well_formed_closed_induc (patt_exists phi)
  | wfc_mu        : forall phi : Pattern, 
      (forall (X : svar),
          X ∉ (free_svars phi) ->
          well_formed_closed_induc (svar_open 0 X phi)) 
      -> well_formed_closed_induc (patt_mu phi).

  Lemma wfc_wfc_ind_helper : forall sz phi, 
      well_formed_closed phi ->
      le (size phi) sz
      ->
      well_formed_closed_induc phi.
  Proof.
    induction sz; destruct phi; intros Hwf Hsz ; simpl in *; try inversion Hsz; auto. 1, 2, 5, 6 : constructor.
    - inversion Hwf.
    - inversion Hwf.
    - unfold well_formed_closed in Hwf.
      simpl in Hwf. apply andb_true_iff in Hwf. destruct Hwf as [Hwf1 Hwf2].
      constructor.
      { apply IHsz. apply Hwf1. lia. }
      { apply IHsz. apply Hwf2. lia. }
    - unfold well_formed_closed in Hwf.
      simpl in Hwf. apply andb_true_iff in Hwf. destruct Hwf as [Hwf1 Hwf2].
      constructor.
      { apply IHsz. apply Hwf1. lia. }
      { apply IHsz. apply Hwf2. lia. }
    - unfold well_formed_closed in Hwf. simpl in Hwf.
      constructor. apply wfc_ex_to_wfc_body in Hwf. unfold wfc_body_ex in Hwf. intros. 
      apply (IHsz (evar_open 0 x phi)). apply Hwf. assumption. erewrite evar_open_size in Hsz.  apply Peano.le_S_n in Hsz. exact Hsz.
    - unfold well_formed_closed in Hwf. simpl in Hwf.
      constructor. apply wfc_mu_to_wfc_body in Hwf. unfold wfc_body_mu in Hwf. intros. 
      apply (IHsz (svar_open 0 X phi)). apply Hwf. assumption. erewrite svar_open_size in Hsz. apply Peano.le_S_n in Hsz. exact Hsz.
  Qed.

  Lemma wfc_wfc_ind phi: well_formed_closed phi -> well_formed_closed_induc phi.
  Proof.
    intros H.
    apply wfc_wfc_ind_helper with (sz := size phi).
    auto. lia.
  Qed.

  Lemma wfc_ind_wfc: forall phi, 
      well_formed_closed_induc phi 
      ->
      well_formed_closed phi.
  Proof.
    intros. induction H; simpl; auto.
    - unfold well_formed_closed. simpl. unfold well_formed_closed in *.
      rewrite IHwell_formed_closed_induc1.
      rewrite IHwell_formed_closed_induc2. reflexivity.
    - unfold well_formed_closed. simpl. unfold well_formed_closed in *.
      rewrite IHwell_formed_closed_induc1.
      rewrite IHwell_formed_closed_induc2. reflexivity. 
    - apply wfc_body_to_wfc_ex. unfold wfc_body_ex. assumption.
    - apply wfc_body_to_wfc_mu. unfold wfc_body_mu. assumption.
  Qed.

  Lemma evar_open_evar_quantify x n n' phi:
    well_formed_closed_aux phi n n' ->
    (evar_open n x (evar_quantify x n phi)) = phi.
  Proof.
    intros H.
    (*apply wfc_wfc_ind in H.*)
    move: n n' H.
    induction phi; intros n' n'' H; simpl; auto.
    - destruct (evar_eqdec x x0); simpl.
      + rewrite Nat.eqb_refl. subst. reflexivity.
      + reflexivity.
    - simpl in *. apply Nat.ltb_lt in H.
      destruct (n =? n') eqn:Heq.
      + apply Nat.eqb_eq in Heq. lia.
      + reflexivity.
    - simpl in H.
      apply andb_true_iff in H.
      destruct H as [H1 H2].
      erewrite -> IHphi1, IHphi2 by eassumption.
      reflexivity.
    - simpl in H.
      apply andb_true_iff in H.
      destruct H as [H1 H2].
      erewrite -> IHphi1, IHphi2 by eassumption.
      reflexivity.
    - simpl in H.
      erewrite -> IHphi by eassumption. reflexivity.
    - simpl in H. apply IHphi in H. rewrite H. reflexivity.
  Qed.

  
  Lemma evar_open_last: forall phi i u j v,
      (i <> j) -> evar_open i u (evar_open j v phi) = evar_open j v phi
      ->
      (evar_open i u phi) = phi.
  Proof.
    induction phi; firstorder.
    - simpl in H. destruct (n=?j) eqn:D.
      + simpl. destruct (n =? i) eqn:D1.
        * apply Nat.eqb_eq in D1. subst. apply Nat.eqb_eq in D. lia.
        * auto.
      + simpl. destruct (n =? i) eqn:D1.
        * apply Nat.eqb_eq in D1. subst. simpl in H0. rewrite D in H0. simpl in H0. rewrite Nat.eqb_refl in H0. congruence.
        * auto.
    - simpl. erewrite IHphi1, IHphi2. reflexivity. exact H. inversion H0. exact H3. exact H.  inversion H0. exact H2.
    - simpl. erewrite IHphi1, IHphi2. reflexivity. exact H. inversion H0. exact H3. exact H.  inversion H0. exact H2.
    - simpl in H0. inversion H0. simpl. erewrite (IHphi (S i) _ (S j)). reflexivity. lia. exact H2.
    - simpl in H0. inversion H0. simpl. erewrite (IHphi (i) _ (j)). reflexivity. lia. exact H2.
  Qed.

  Lemma svar_open_last: forall phi i u j v,
      evar_open i u (svar_open j v phi) = svar_open j v phi
      ->
      (evar_open i u phi) = phi.
  Proof.
    induction phi; firstorder.
    - simpl. erewrite IHphi1, IHphi2. reflexivity. inversion H. exact H2. inversion H. exact H1.
    - simpl. erewrite IHphi1, IHphi2. reflexivity. inversion H. exact H2. inversion H. exact H1.
    - simpl in H. inversion H. simpl. erewrite (IHphi (S i) _ (j)). reflexivity. exact H1.
    - simpl in H. inversion H. simpl. erewrite (IHphi (i) _ (S j)). reflexivity.  exact H1.
  Qed.
  
  Lemma svar_open_last2: forall phi i u j v,
      svar_open i u (evar_open j v phi) = evar_open j v phi
      ->
      (svar_open i u phi) = phi.
  Proof.
    induction phi; firstorder.
    - simpl. erewrite IHphi1, IHphi2. reflexivity. inversion H. exact H2. inversion H. exact H1.
    - simpl. erewrite IHphi1, IHphi2. reflexivity. inversion H. exact H2. inversion H. exact H1.
    - simpl in H. inversion H. simpl. erewrite (IHphi (i) _ (S j)). reflexivity. exact H1.
    - simpl in H. inversion H. simpl. erewrite (IHphi (S i) _ (j)). reflexivity.  exact H1.
  Qed.
  
  Lemma svar_open_last3: forall phi i u j v,
      (i <> j) -> svar_open i u (svar_open j v phi) = svar_open j v phi
      ->
      (svar_open i u phi) = phi.
  Proof.
    induction phi; firstorder.
    - simpl in H. destruct (n=?j) eqn:D.
      + simpl. destruct (n =? i) eqn:D1.
        * apply Nat.eqb_eq in D1. subst. apply Nat.eqb_eq in D. lia.
        * auto.
      + simpl. destruct (n =? i) eqn:D1.
        * apply Nat.eqb_eq in D1. subst. simpl in H0. rewrite D in H0. simpl in H0. rewrite Nat.eqb_refl in H0. congruence.
        * auto.
    - simpl. erewrite IHphi1, IHphi2. reflexivity. exact H. inversion H0. exact H3. exact H.  inversion H0. exact H2.
    - simpl. erewrite IHphi1, IHphi2. reflexivity. exact H. inversion H0. exact H3. exact H.  inversion H0. exact H2.
    - simpl in H0. inversion H0. simpl. erewrite (IHphi (i) _ (j)). reflexivity. lia. exact H2.
    - simpl in H0. inversion H0. simpl. erewrite (IHphi (S i) _ (S j)). reflexivity. lia. exact H2.
  Qed.

  (* evar_open of fresh name does not change in a well-formed pattern*)
  Lemma evar_open_fresh :
    forall phi,
      well_formed_closed phi ->
      forall n v,
        evar_open n v phi = phi.
  Proof.
    intros phi IHwf. apply (wfc_wfc_ind) in IHwf.
    induction IHwf; firstorder.
    - simpl. rewrite IHIHwf1. rewrite IHIHwf2. reflexivity.
    - simpl. rewrite IHIHwf1. rewrite IHIHwf2. reflexivity.
    - simpl. eapply (@evar_open_last _ _ _ _ (fresh_evar phi))in H0. erewrite H0. reflexivity. lia.
      apply set_evar_fresh_is_fresh.
    - simpl. eapply svar_open_last in H0. erewrite H0. reflexivity. 
      instantiate (1 := fresh_svar phi). apply set_svar_fresh_is_fresh.
  Qed.
  
    Lemma svar_open_fresh :
    forall phi,
      well_formed_closed phi ->
      forall n v,
        svar_open n v phi = phi.
  Proof.
    intros phi IHwf. apply (wfc_wfc_ind) in IHwf.
    induction IHwf; firstorder.
    - simpl. rewrite IHIHwf1. rewrite IHIHwf2. reflexivity.
    - simpl. rewrite IHIHwf1. rewrite IHIHwf2. reflexivity.
    - simpl. eapply (@svar_open_last2 _ _ _ _ (fresh_evar phi)) in H0. erewrite H0. reflexivity.
      apply set_evar_fresh_is_fresh.
    - simpl. eapply svar_open_last3 in H0. erewrite H0. reflexivity. lia.
      instantiate (1 := fresh_svar phi). apply set_svar_fresh_is_fresh.
  Qed. 

  Lemma evar_open_comm:
    forall n m,
      n <> m 
      ->
      forall x y phi,
        evar_open n x (evar_open m y phi) = evar_open m y (evar_open n x phi).
  Proof.
    intros n m Hneqnm x y phi.
    move: n m Hneqnm.
    induction phi; intros n' m' Hneqnm; simpl; try reflexivity.
    - destruct (eqb_reflect n m'), (eqb_reflect n n'); subst; simpl.
      + contradiction.
      + destruct (eqb_reflect m' m').
        * reflexivity.
        * contradiction.
      + rewrite Nat.eqb_refl. reflexivity.
      + destruct (eqb_reflect n n'),(eqb_reflect n m'); subst.
        * contradiction.
        * contradiction.
        * contradiction.
        * reflexivity.
    - rewrite IHphi1. assumption.  rewrite IHphi2. assumption. reflexivity.
    - rewrite IHphi1. assumption. rewrite IHphi2. assumption. reflexivity.
    - rewrite IHphi. lia. reflexivity.
    - rewrite IHphi. lia. reflexivity.
  Qed.

  Lemma svar_open_comm:
    forall n m,
      n <> m 
      ->
      forall X Y phi,
        svar_open n X (svar_open m Y phi) = svar_open m Y (svar_open n X phi).
  Proof.
    intros n m Hneqnm x y phi.
    move: n m Hneqnm.
    induction phi; intros n' m' Hneqnm; simpl; try reflexivity.
    - destruct (eqb_reflect n m'), (eqb_reflect n n'); subst; simpl.
      + contradiction.
      + destruct (eqb_reflect m' m').
        * reflexivity.
        * contradiction.
      + rewrite Nat.eqb_refl. reflexivity.
      + destruct (eqb_reflect n n'),(eqb_reflect n m'); subst.
        * contradiction.
        * contradiction.
        * contradiction.
        * reflexivity.
    - rewrite IHphi1. assumption.  rewrite IHphi2. assumption. reflexivity.
    - rewrite IHphi1. assumption. rewrite IHphi2. assumption. reflexivity.
    - rewrite IHphi. lia. reflexivity.
    - rewrite IHphi. lia. reflexivity.
  Qed.
  
  (* TODO make a wrapper that does not have the 'sz' variable *)
  Lemma fresh_notin: 
    forall sz phi v w,
      le (size phi) sz ->
      v ∉ (free_evars phi) ->
      w ∉ (free_evars phi) ->
      (v <> w) ->
      forall n,
        v ∉ (free_evars (evar_open n w phi)).
  Proof.
    induction sz; destruct phi; intros v w Hsz Hlsv Hlsw Hneq n0; simpl in *; try inversion Hsz; auto.
    - destruct (n =? n0) eqn:P.
      + simpl. apply not_elem_of_singleton_2. assumption.
      + simpl. trivial.
    - destruct (n =? n0) eqn:P.
      + simpl. apply not_elem_of_singleton_2. assumption.
      + simpl. trivial.
    - rewrite elem_of_union.
      apply and_not_or. 
      rewrite -> elem_of_union in Hlsv.
      rewrite -> elem_of_union in Hlsw.
      apply not_or_and in Hlsv.
      apply not_or_and in Hlsw.
      destruct Hlsv, Hlsw.
      split.
      + apply IHsz. lia. assumption. assumption. assumption.
      + apply IHsz. lia. assumption. assumption. assumption.
    - rewrite elem_of_union.
      apply and_not_or. 
      rewrite -> elem_of_union in Hlsv.
      rewrite -> elem_of_union in Hlsw.
      apply not_or_and in Hlsv.
      apply not_or_and in Hlsw.
      destruct Hlsv, Hlsw.
      split.
      + apply IHsz. lia. assumption. assumption. assumption.
      + apply IHsz. lia. assumption. assumption. assumption.
    - rewrite -> elem_of_union.
      apply and_not_or. 
      rewrite -> elem_of_union in Hlsv.
      rewrite -> elem_of_union in Hlsw.
      apply not_or_and in Hlsv.
      apply not_or_and in Hlsw.
      destruct Hlsv, Hlsw.
      split.
      + apply IHsz. lia. assumption. assumption. assumption.
      + apply IHsz. lia. assumption. assumption. assumption.
    - rewrite elem_of_union.
      apply and_not_or. 
      rewrite -> elem_of_union in Hlsv.
      rewrite -> elem_of_union in Hlsw.
      apply not_or_and in Hlsv.
      apply not_or_and in Hlsw.
      destruct Hlsv, Hlsw.
      split.
      + apply IHsz. lia. assumption. assumption. assumption.
      + apply IHsz. lia. assumption. assumption. assumption.
    - apply IHsz. lia. assumption. assumption. assumption.
    - apply IHsz. lia. assumption. assumption. assumption.
    - apply IHsz. lia. assumption. assumption. assumption.
    - apply IHsz. lia. assumption. assumption. assumption.
  Qed.

  (* TODO make a wrapper that does not have the 'sz' variable *)
  Lemma svar_fresh_notin: 
    forall sz phi v w,
      le (size phi) sz ->
      v ∉ (free_svars phi) ->
      w ∉ (free_svars phi) ->
      (v <> w) ->
      forall n,
        v ∉ (free_svars (svar_open n w phi)).
  Proof.
    induction sz; destruct phi; intros v w Hsz Hlsv Hlsw Hneq n0; simpl in *; try inversion Hsz; auto.
    - destruct (n =? n0) eqn:P.
      + simpl. apply not_elem_of_singleton_2. assumption.
      + simpl. trivial.
    - destruct (n =? n0) eqn:P.
      + simpl. apply not_elem_of_singleton_2. assumption.
      + simpl. trivial.
    - rewrite elem_of_union.
      apply and_not_or. 
      rewrite -> elem_of_union in Hlsv.
      rewrite -> elem_of_union in Hlsw.
      apply not_or_and in Hlsv.
      apply not_or_and in Hlsw.
      destruct Hlsv, Hlsw.
      split.
      + apply IHsz. lia. assumption. assumption. assumption.
      + apply IHsz. lia. assumption. assumption. assumption.
    - rewrite elem_of_union.
      apply and_not_or. 
      rewrite -> elem_of_union in Hlsv.
      rewrite -> elem_of_union in Hlsw.
      apply not_or_and in Hlsv.
      apply not_or_and in Hlsw.
      destruct Hlsv, Hlsw.
      split.
      + apply IHsz. lia. assumption. assumption. assumption.
      + apply IHsz. lia. assumption. assumption. assumption.
    - rewrite -> elem_of_union.
      apply and_not_or. 
      rewrite -> elem_of_union in Hlsv.
      rewrite -> elem_of_union in Hlsw.
      apply not_or_and in Hlsv.
      apply not_or_and in Hlsw.
      destruct Hlsv, Hlsw.
      split.
      + apply IHsz. lia. assumption. assumption. assumption.
      + apply IHsz. lia. assumption. assumption. assumption.
    - rewrite elem_of_union.
      apply and_not_or. 
      rewrite -> elem_of_union in Hlsv.
      rewrite -> elem_of_union in Hlsw.
      apply not_or_and in Hlsv.
      apply not_or_and in Hlsw.
      destruct Hlsv, Hlsw.
      split.
      + apply IHsz. lia. assumption. assumption. assumption.
      + apply IHsz. lia. assumption. assumption. assumption.
    - apply IHsz. lia. assumption. assumption. assumption.
    - apply IHsz. lia. assumption. assumption. assumption.
    - apply IHsz. lia. assumption. assumption. assumption.
    - apply IHsz. lia. assumption. assumption. assumption.
  Qed.

  
  Lemma free_evars_svar_open : forall (psi : Pattern) (dbi :db_index) (X : svar),
      free_evars (svar_open dbi X psi) = free_evars psi.
  Proof.
    induction psi; intros; simpl; try reflexivity.
    * destruct (n =? dbi); reflexivity.
    * rewrite -> IHpsi1. rewrite -> IHpsi2. reflexivity.
    * rewrite -> IHpsi1. rewrite -> IHpsi2. reflexivity.
    * rewrite -> IHpsi. reflexivity.
    * rewrite -> IHpsi. reflexivity.
  Qed.

  Lemma not_free_implies_positive_negative_occurrence :
    forall (phi : Pattern) (X : svar),
      X ∉ (free_svars phi) ->
      positive_occurrence_named X phi /\ negative_occurrence_named X phi.
  Proof.
    induction phi; simpl; intros Y H; split; try constructor. (* try firstorder.*)
    * unfold not. intros. apply H. apply elem_of_singleton_2. symmetry. assumption.
    * apply IHphi1. unfold not. intros H0.
      assert (H': Y ∈ (union (free_svars phi1) (free_svars phi2))).
      { apply elem_of_union_l. assumption. }
      auto.
    * apply IHphi2. unfold not. intros H0.
      assert (H': Y ∈ (union (free_svars phi1) (free_svars phi2))).
      { apply elem_of_union_r. assumption. }
      auto.
    * apply IHphi1. unfold not. intros H0. apply H. apply elem_of_union_l. auto.
    * apply IHphi2. unfold not. intros H0. apply H. apply elem_of_union_r. auto.
    * apply IHphi1. unfold not. intros H0. apply H. apply elem_of_union_l. auto.
    * apply IHphi2. unfold not. intros H0. apply H. apply elem_of_union_r. auto.
    * apply IHphi1. unfold not. intros H0. apply H. apply elem_of_union_l. auto.
    * apply IHphi2. unfold not. intros H0. apply H. apply elem_of_union_r. auto.
    * apply IHphi. auto.
    * apply IHphi. auto.
    * apply IHphi. auto.
    * apply IHphi. auto.
  Qed.

  Lemma positive_negative_occurrence_db_named :
    forall (phi : Pattern) (dbi : db_index) (X : svar),
      (positive_occurrence_db dbi phi ->
       positive_occurrence_named X phi ->
       positive_occurrence_named X (svar_open dbi X phi))
      /\ (negative_occurrence_db dbi phi ->
          negative_occurrence_named X phi ->
          negative_occurrence_named X (svar_open dbi X phi)).
  Proof.
    induction phi; intros; split; simpl; try firstorder.
    + destruct ( n =? dbi). constructor. constructor.
    + destruct (eqb_reflect n dbi).
      { inversion H. subst. lia. }
      { constructor. }
    + inversion H; subst. inversion H0; subst.
      constructor. firstorder. firstorder.
    + inversion H. inversion H0. subst.
      constructor. firstorder. firstorder.
    + inversion H. inversion H0. subst.
      constructor. firstorder. firstorder.
    + inversion H. inversion H0. subst.
      constructor. firstorder. firstorder.
    + inversion H. inversion H0. subst.
      constructor. apply IHphi. firstorder. assumption.
    + inversion H. inversion H0. subst.
      constructor. firstorder.
    + inversion H. inversion H0. subst.
      constructor. firstorder.
    + inversion H. inversion H0. subst.
      constructor. firstorder.
  Qed.

  Lemma well_formed_app_1 : forall (phi1 phi2 : Pattern),
      well_formed (patt_app phi1 phi2) -> well_formed phi1.
  Proof.
    unfold well_formed. simpl. intros phi1 phi2 H.
    apply andb_true_iff in H.
    destruct H as [Hpos Hclos].
    apply andb_true_iff in Hpos. destruct Hpos as [Hpos1 Hpos2].
    rewrite Hpos1. simpl. apply wfc_wfc_ind in Hclos. inversion Hclos. subst.
    apply wfc_ind_wfc. apply H1.
  Qed.

  Lemma well_formed_app_2 : forall (phi1 phi2 : Pattern),
      well_formed (patt_app phi1 phi2) -> well_formed phi2.
  Proof.
    unfold well_formed. simpl. intros phi1 phi2 H.
    apply andb_true_iff in H.
    destruct H as [Hpos Hclos].
    apply andb_true_iff in Hpos. destruct Hpos as [Hpos1 Hpos2].
    rewrite Hpos2. simpl. apply wfc_wfc_ind in Hclos. inversion Hclos. subst.
    apply wfc_ind_wfc. apply H2.
  Qed.

  Lemma free_svars_evar_open : forall (ϕ : Pattern) (dbi :db_index) (x : evar),
      free_svars (evar_open dbi x ϕ) = free_svars ϕ.
  Proof.
    induction ϕ; intros; simpl; try reflexivity.
    * destruct (n =? dbi); reflexivity.
    * rewrite -> IHϕ1. rewrite -> IHϕ2. reflexivity.
    * rewrite -> IHϕ1. rewrite -> IHϕ2. reflexivity.
    * rewrite -> IHϕ. reflexivity.
    * rewrite -> IHϕ. reflexivity.
  Qed.

  Lemma free_svars_exists : forall (ϕ : Pattern),
      free_svars (patt_exists ϕ) = free_svars ϕ.
  Proof. done. Qed.
  
  Lemma svar_open_evar_open_comm
    : forall (phi : Pattern) (dbi1 : db_index)(x : evar)(dbi2 : db_index)(X : svar),
      evar_open dbi1 x (svar_open dbi2 X phi) = svar_open dbi2 X (evar_open dbi1 x phi).
  Proof.
    induction phi; intros; simpl; try reflexivity.
    * destruct (n =? dbi1); reflexivity.
    * destruct (n =? dbi2); reflexivity.
    * rewrite -> IHphi1. rewrite -> IHphi2. reflexivity.
    * rewrite -> IHphi1. rewrite -> IHphi2. reflexivity.
    * rewrite -> IHphi. reflexivity.
    * rewrite -> IHphi. reflexivity.
  Qed.

  Lemma positive_negative_occurrence_evar_open : forall (ϕ : Pattern) (X : svar) (dbi : db_index) (x : evar),
      (positive_occurrence_named X (evar_open dbi x ϕ) <-> positive_occurrence_named X ϕ)
      /\ (negative_occurrence_named X (evar_open dbi x ϕ) <-> negative_occurrence_named X ϕ).
  Proof.
    induction ϕ; intros; simpl; split; try reflexivity.
    + destruct (n =? dbi).
      split; intros H; inversion H; constructor. reflexivity.
    + destruct (n =? dbi).
      split; intros H; inversion H; constructor. reflexivity.
    + split; intros H; inversion H; subst; constructor; firstorder.
    + split; intros H; inversion H; subst; constructor; firstorder.
    + split; intros H; inversion H; subst; constructor; firstorder.
    + split; intros H; inversion H; subst; constructor; firstorder.
    + split; intros H; inversion H; subst; constructor; firstorder.
    + split; intros H; inversion H; subst; constructor; firstorder.
    + split; intros H; inversion H; subst; constructor; firstorder.
    + split; intros H; inversion H; subst; constructor; firstorder.
  Qed.

  Lemma positive_occurrence_evar_open : forall (ϕ : Pattern) (X : svar) (dbi : db_index) (x : evar),
      positive_occurrence_named X (evar_open dbi x ϕ) <-> positive_occurrence_named X ϕ.
  Proof.
    intros.
    pose proof (P := positive_negative_occurrence_evar_open ϕ X dbi x).
    destruct P as [P _]. exact P.
  Qed.

  Lemma negative_occurrence_evar_open : forall (ϕ : Pattern) (X : svar) (dbi : db_index) (x : evar),
      negative_occurrence_named X (evar_open dbi x ϕ) <-> negative_occurrence_named X ϕ.
  Proof.
    intros.
    pose proof (P := positive_negative_occurrence_evar_open ϕ X dbi x).
    destruct P as [_ P]. exact P.
  Qed.

  Lemma evar_open_wfp : forall (sz : nat) (phi : Pattern),
      le (size phi) sz ->
      forall(n : db_index) (x : evar),
        well_formed_positive phi -> well_formed_positive (evar_open n x phi).
  Proof.
    induction sz; destruct phi; intros Hsz dbi e Hwfp; simpl in *; auto; try inversion Hsz; subst.
    + destruct (n =? dbi). constructor. assumption.
    + destruct (n =? dbi). constructor. assumption.
    + apply andb_true_iff in Hwfp.
      destruct Hwfp as [Hwfp1 Hwfp2].
      apply andb_true_iff.
      split; apply IHsz. lia. assumption. lia. assumption.
    + apply andb_true_iff in Hwfp.
      destruct Hwfp as [Hwfp1 Hwfp2].
      apply andb_true_iff.
      split; apply IHsz. lia. assumption. lia. assumption.
    + apply andb_true_iff in Hwfp.
      destruct Hwfp as [Hwfp1 Hwfp2].
      apply andb_true_iff.
      split; apply IHsz. lia. assumption. lia. assumption.
    + apply andb_true_iff in Hwfp.
      destruct Hwfp as [Hwfp1 Hwfp2].
      apply andb_true_iff.
      split; apply IHsz. lia. assumption. lia. assumption.
    + apply IHsz. lia. assumption.
    + apply IHsz. lia. assumption.
    + apply andb_true_iff.
      apply andb_true_iff in Hwfp.
      destruct Hwfp as [Hwfp1 Hwfp2].
      split.
      * apply no_negative_occurrence_evar_open. assumption.
      * apply IHsz. lia. firstorder.
    + apply andb_true_iff.
      apply andb_true_iff in Hwfp.
      destruct Hwfp as [Hwfp1 Hwfp2].
      split.
      * apply no_negative_occurrence_evar_open. assumption.
      * apply IHsz. lia. firstorder.
  Qed.

  Lemma positive_occurrence_db_svar_open : forall (phi : Pattern) (dbi : db_index) (X : svar),
      (positive_occurrence_db dbi phi ->
       positive_occurrence_db dbi (svar_open dbi X phi))
      /\ (negative_occurrence_db dbi phi -> negative_occurrence_db dbi (svar_open dbi X phi)).
  Proof.
    induction phi; intros; simpl; split; intros; try constructor; try inversion H; try firstorder.
    + destruct (n =? dbi); constructor.
    + destruct (n =? dbi).
      * constructor.
      * subst. constructor. assumption.
  Qed.

  
  Lemma positive_negative_occurrence_db_svar_open_le : forall (phi : Pattern) (dbi1 dbi2 : db_index) (X : svar),
      dbi1 < dbi2 ->
      (
        positive_occurrence_db dbi1 phi ->
        positive_occurrence_db dbi1 (svar_open dbi2 X phi)
      )
      /\ (negative_occurrence_db dbi1 phi -> negative_occurrence_db dbi1 (svar_open dbi2 X phi)).
  Proof.
    induction phi; intros dbi1 dbi2 X Hneq; split; intros H; inversion H; subst; intros; simpl in *; auto.
    + destruct (n =? dbi2); constructor.
    + destruct (n =? dbi2); constructor. auto.
    + constructor; firstorder.
    + constructor; firstorder.
    + constructor; firstorder.
    + constructor; firstorder.
    + constructor. apply IHphi. lia. assumption.
    + constructor. apply IHphi. lia. assumption.
    + constructor. apply IHphi. lia. assumption.
    + constructor. apply IHphi. lia. assumption.
  Qed.

  Lemma wfp_svar_open : forall (phi : Pattern) (dbi : db_index) (X : svar),
      well_formed_positive phi ->
      well_formed_positive (svar_open dbi X phi).
  Proof.
    induction phi; simpl; intros.
    + constructor.
    + constructor.
    + constructor.
    + simpl. destruct (n =? dbi); constructor.
    + constructor.
    + inversion H. apply andb_true_iff in H1. destruct H1 as [H1 H2].
      rewrite IHphi1. assumption. rewrite IHphi2. assumption. reflexivity.
    + constructor.
    + apply andb_true_iff in H. destruct H as [H1 H2]. rewrite IHphi1. apply H1. rewrite IHphi2. apply H2.
      reflexivity.
    + simpl in H. simpl. auto.
    + simpl in H. simpl. apply andb_true_iff in H. destruct H as [H1 H2].
      rewrite IHphi. apply H2. rewrite andb_true_r.
      eapply introT. apply no_negative_occurrence_P.
      apply positive_negative_occurrence_db_svar_open_le. lia.
      eapply elimT. apply no_negative_occurrence_P.
      apply H1.
  Qed.


  Lemma positive_negative_occurrence_named_svar_open :
    forall (phi : Pattern) (X Y : svar) (dbi : db_index),
      X <> Y ->
      (
        negative_occurrence_named X phi ->
        negative_occurrence_named X (svar_open dbi Y phi)
      ) /\ (
        positive_occurrence_named X phi ->
        positive_occurrence_named X (svar_open dbi Y phi)
      ).
  Proof.
    induction phi; intros X Y dbi XneY; split; intros Hneg; inversion Hneg; subst;
      simpl in *; try constructor; try firstorder.
    - destruct (n =? dbi); constructor. 
      unfold not. intros. assert (X = Y). symmetry. assumption.
      unfold not in XneY. destruct (XneY H0).
    - destruct (n =? dbi); constructor.
  Qed.

  Lemma evar_open_wfc_aux db1 db2 dbs X phi :
    db1 <= db2 ->
    well_formed_closed_aux phi db1 dbs ->
    evar_open db2 X phi = phi.
  Proof.
    generalize dependent dbs. generalize dependent db2. generalize dependent db1.
    induction phi; intros db1 db2 dbs Hle Hwfca; simpl; simpl in Hwfca; auto.
    * destruct (eqb_reflect n db2). apply Nat.ltb_lt in Hwfca. lia. auto.
    * apply andb_true_iff in Hwfca. destruct Hwfca as [Hwfca1 Hwfca2].
      rewrite -> IHphi1 with (dbs := dbs)(db1 := db1). 3: auto. 2: auto. 
      rewrite -> IHphi2 with (dbs := dbs)(db1 := db1). 3: auto. 2: auto.
      auto.
    * apply andb_true_iff in Hwfca. destruct Hwfca as [Hwfca1 Hwfca2].
      rewrite -> IHphi1 with (dbs := dbs)(db1 := db1). 3: auto. 2: auto.
      rewrite -> IHphi2 with (dbs := dbs)(db1 := db1). 3: auto. 2: auto.
      auto.
    * apply f_equal.
      rewrite -> IHphi with (dbs := dbs)(db1 := S db1). 3: auto. 2: lia. auto.
    * apply f_equal. rewrite -> IHphi with (dbs := S dbs)(db1 := db1). auto. auto. auto.
  Qed.

  Lemma evar_open_wfc m X phi : well_formed_closed phi -> evar_open m X phi = phi.
  Proof.
    intros.
    unfold well_formed_closed in H.
    apply evar_open_wfc_aux with (X := X)(db2 := m) in H.
    2: lia.
    auto.
  Qed.

  Lemma evar_open_bsvar_subst m phi1 phi2 dbi X
    : well_formed_closed phi2 ->
      evar_open m X (bsvar_subst phi1 phi2 dbi)
      = bsvar_subst (evar_open m X phi1) phi2 dbi.
  Proof.
    generalize dependent dbi. generalize dependent m. induction phi1; intros m dbi Hwfc; auto.
    - simpl. destruct (n =? m) eqn:Heq, (compare_nat n (S dbi)) eqn:Hdbi; simpl; auto.
    - simpl. destruct (compare_nat n dbi); simpl; auto. auto using evar_open_wfc.
    - simpl. rewrite -> IHphi1_1. rewrite -> IHphi1_2. auto. auto. auto.
    - simpl. rewrite -> IHphi1_1. rewrite -> IHphi1_2. auto. auto. auto.
    - simpl. apply f_equal. rewrite -> IHphi1. auto. auto.
    - simpl. rewrite -> IHphi1. auto. auto.
  Qed.

  (* TODO!! *)
  Lemma svar_open_bsvar_subst m phi1 phi2 dbi X
    : well_formed_closed phi2 ->
      m <> dbi ->
      svar_open m X (bsvar_subst phi1 phi2 dbi)
      = bsvar_subst (svar_open m X phi1) phi2 dbi.
  Proof.
  Admitted.

  Lemma evar_open_bevar_subst m phi1 phi2 dbi X
    : well_formed_closed phi2 ->
      m <> dbi ->
      evar_open m X (bevar_subst phi1 phi2 dbi)
      = bevar_subst (evar_open m X phi1) phi2 dbi.
  Proof.
  Admitted.
  
  
  Lemma fresh_evar_svar_open dbi X phi :
    fresh_evar (svar_open dbi X phi) = fresh_evar phi.
  Proof.
    unfold fresh_evar.
    apply f_equal.
    apply f_equal.
    apply free_evars_svar_open.
  Qed.

  Lemma fresh_svar_evar_open dbi x phi :
    fresh_svar (evar_open dbi x phi) = fresh_svar phi.
  Proof.
    unfold fresh_svar.
    apply f_equal.
    apply f_equal.
    apply free_svars_evar_open.
  Qed.
  
  Lemma free_svars_svar_open ϕ X dbi :
    free_svars (svar_open dbi X ϕ) ⊆ union (singleton X) (free_svars ϕ).
  Proof.
    generalize dependent dbi.
    induction ϕ; intros dbi; simpl; try apply empty_subseteq.
    - apply union_subseteq_r.
    - destruct (n =? dbi).
      + simpl. apply union_subseteq_l.
      + simpl. apply union_subseteq_r.
    - apply union_least.
      + eapply PreOrder_Transitive. apply IHϕ1.
        apply union_mono_l. apply union_subseteq_l.
      + eapply PreOrder_Transitive. apply IHϕ2.
        apply union_mono_l. apply union_subseteq_r.
    - apply union_least.
      + eapply PreOrder_Transitive. apply IHϕ1.
        apply union_mono_l. apply union_subseteq_l.
      + eapply PreOrder_Transitive. apply IHϕ2.
        apply union_mono_l. apply union_subseteq_r.
    - auto.
    - auto.
  Qed.

  Lemma free_evars_evar_open ϕ x dbi :
    free_evars (evar_open dbi x ϕ) ⊆ union (singleton x) (free_evars ϕ).
  Proof.
    generalize dependent dbi.
    induction ϕ; intros dbi; simpl; try apply empty_subseteq.
    - apply union_subseteq_r.
    - destruct (n =? dbi).
      + simpl. apply union_subseteq_l.
      + simpl. apply union_subseteq_r.
    - apply union_least.
      + eapply PreOrder_Transitive. apply IHϕ1.
        apply union_mono_l. apply union_subseteq_l.
      + eapply PreOrder_Transitive. apply IHϕ2.
        apply union_mono_l. apply union_subseteq_r.
    - apply union_least.
      + eapply PreOrder_Transitive. apply IHϕ1.
        apply union_mono_l. apply union_subseteq_l.
      + eapply PreOrder_Transitive. apply IHϕ2.
        apply union_mono_l. apply union_subseteq_r.
    - auto.
    - auto.
  Qed.

  Lemma svar_is_fresh_in_svar_open X Y dbi ϕ:
    X <> Y ->
    svar_is_fresh_in X ϕ ->
    svar_is_fresh_in X (svar_open dbi Y ϕ).
  Proof.
    unfold svar_is_fresh_in.
    move=> Hneq Hfr.
    pose proof (H := @free_svars_svar_open ϕ Y dbi).
    intros Contra.
    rewrite -> elem_of_subseteq in H.
    specialize (H X Contra). clear Contra.
    apply elem_of_union in H.
    destruct H.
    - apply elem_of_singleton_1 in H.
      contradiction.
    - contradiction.
  Qed.
  
  Lemma evar_is_fresh_in_evar_open x y dbi ϕ:
    x <> y ->
    evar_is_fresh_in x ϕ ->
    evar_is_fresh_in x (evar_open dbi y ϕ).
  Proof.
    unfold evar_is_fresh_in.
    move=> Hneq Hfr.
    pose proof (H := @free_evars_evar_open ϕ y dbi).
    intros Contra.
    rewrite -> elem_of_subseteq in H.
    specialize (H x Contra). clear Contra.
    apply elem_of_union in H.
    destruct H.
    - apply elem_of_singleton_1 in H.
      contradiction.
    - contradiction.
  Qed.
  
  
  Inductive Application_context : Type :=
  | box
  | ctx_app_l (cc : Application_context) (p : Pattern) (Prf : well_formed p)
  | ctx_app_r (p : Pattern) (cc : Application_context) (Prf : well_formed p)
  .

  Fixpoint subst_ctx (C : Application_context) (p : Pattern)
    : Pattern :=
    match C with
    | box => p
    | @ctx_app_l C' p' prf => patt_app (subst_ctx C' p) p'
    | @ctx_app_r p' C' prf => patt_app p' (subst_ctx C' p)
    end.

  Fixpoint free_evars_ctx (C : Application_context)
    : (EVarSet) :=
    match C with
    | box => empty
    | @ctx_app_l cc p prf => union (free_evars_ctx cc) (free_evars p)
    | @ctx_app_r p cc prf => union (free_evars p) (free_evars_ctx cc)
    end.


  Inductive is_subformula_of_ind : Pattern -> Pattern -> Prop :=
  | sub_eq ϕ₁ ϕ₂ : ϕ₁ = ϕ₂ -> is_subformula_of_ind ϕ₁ ϕ₂
  | sub_app_l ϕ₁ ϕ₂ ϕ₃ : is_subformula_of_ind ϕ₁ ϕ₂ -> is_subformula_of_ind ϕ₁ (patt_app ϕ₂ ϕ₃)
  | sub_app_r ϕ₁ ϕ₂ ϕ₃ : is_subformula_of_ind ϕ₁ ϕ₃ -> is_subformula_of_ind ϕ₁ (patt_app ϕ₂ ϕ₃)
  | sub_imp_l ϕ₁ ϕ₂ ϕ₃ : is_subformula_of_ind ϕ₁ ϕ₂ -> is_subformula_of_ind ϕ₁ (patt_imp ϕ₂ ϕ₃)
  | sub_imp_r ϕ₁ ϕ₂ ϕ₃ : is_subformula_of_ind ϕ₁ ϕ₃ -> is_subformula_of_ind ϕ₁ (patt_imp ϕ₂ ϕ₃)
  | sub_exists ϕ₁ ϕ₂ : is_subformula_of_ind ϕ₁ ϕ₂ -> is_subformula_of_ind ϕ₁ (patt_exists ϕ₂)
  | sub_mu ϕ₁ ϕ₂ : is_subformula_of_ind ϕ₁ ϕ₂ -> is_subformula_of_ind ϕ₁ (patt_mu ϕ₂)
  .

  Fixpoint is_subformula_of ϕ₁ ϕ₂ : bool :=
    (decide_rel (=) ϕ₁ ϕ₂)
    || match ϕ₂ with
       | patt_app l r | patt_imp l r => is_subformula_of ϕ₁ l || is_subformula_of ϕ₁ r
       | patt_exists phi | patt_mu phi => is_subformula_of ϕ₁ phi
       | _ => false
       end.

  Lemma is_subformula_of_P ϕ₁ ϕ₂ : reflect (is_subformula_of_ind ϕ₁ ϕ₂) (is_subformula_of ϕ₁ ϕ₂).
  Proof.
    unfold is_subformula_of.
    remember ϕ₂. revert p Heqp.

    (* TODO *)
    induction ϕ₂; move=> p Heqp; destruct (decide_rel (=) ϕ₁ p) eqn:Heq2;
                           rewrite Heqp; rewrite -Heqp; rewrite Heq2; simpl; rewrite Heqp;
                             try (apply ReflectT; subst; apply sub_eq; reflexivity);
                             try (apply ReflectF; intros Contra; inversion Contra; subst; contradiction).
    all: fold is_subformula_of in *.
    - destruct (IHϕ₂1 ϕ₂1),(IHϕ₂2 ϕ₂2); simpl; try reflexivity.
      + apply ReflectT. apply sub_app_l. assumption.
      + apply ReflectT. apply sub_app_l. assumption.
      + apply ReflectT. apply sub_app_r. assumption.
      + apply ReflectF. intros Contra. inversion Contra; subst; contradiction.
    - destruct (IHϕ₂1 ϕ₂1),(IHϕ₂2 ϕ₂2); simpl; try reflexivity.
      + apply ReflectT. apply sub_imp_l. assumption.
      + apply ReflectT. apply sub_imp_l. assumption.
      + apply ReflectT. apply sub_imp_r. assumption.
      + apply ReflectF. intros Contra. inversion Contra; subst; contradiction.
    - destruct (IHϕ₂ ϕ₂). reflexivity.
      + apply ReflectT. apply sub_exists. assumption.
      + apply ReflectF. intros Contra. inversion Contra; subst; contradiction.
    - destruct (IHϕ₂ ϕ₂). reflexivity.
      + apply ReflectT. apply sub_mu. assumption.
      + apply ReflectF. intros Contra. inversion Contra; subst; contradiction.
  Qed.

  Lemma is_subformula_of_refl ϕ:
    is_subformula_of ϕ ϕ = true.
  Proof.
    destruct (is_subformula_of_P ϕ ϕ).
    - reflexivity.
    - assert (H: is_subformula_of_ind ϕ ϕ).
      apply sub_eq. reflexivity. contradiction.
  Qed.
  

  Lemma bsvar_subst_contains_subformula ϕ₁ ϕ₂ dbi :
    bsvar_occur ϕ₁ dbi = true ->
    is_subformula_of_ind ϕ₂ (bsvar_subst ϕ₁ ϕ₂ dbi).
  Proof.
    generalize dependent dbi.
    induction ϕ₁; intros dbi H; simpl; simpl in H; try inversion H.
    - case_bool_decide; destruct (compare_nat n dbi); try inversion H1.
      + lia.
      + constructor. reflexivity.
      + lia.
    - specialize (IHϕ₁1 dbi). specialize (IHϕ₁2 dbi).
      move: H H1 IHϕ₁1 IHϕ₁2.
      case: (bsvar_occur ϕ₁1 dbi); case: (bsvar_occur ϕ₁2 dbi); move=> H H1 IHϕ₁₁ IHϕ₁₂.
      + apply sub_app_l. auto.
      + apply sub_app_l. auto.
      + apply sub_app_r. auto.
      + done.
    - specialize (IHϕ₁1 dbi). specialize (IHϕ₁2 dbi).
      move: H H1 IHϕ₁1 IHϕ₁2.
      case: (bsvar_occur ϕ₁1 dbi); case: (bsvar_occur ϕ₁2 dbi); move=> H H1 IHϕ₁₁ IHϕ₁₂.
      + apply sub_imp_l. auto.
      + apply sub_imp_l. auto.
      + apply sub_imp_r. auto.
      + done.
    - apply sub_exists. auto.
    - apply sub_mu. apply IHϕ₁. auto.
  Qed.

  Lemma Private_bsvar_occur_evar_open sz dbi1 dbi2 X phi:
    size phi <= sz ->
    bsvar_occur phi dbi1 = false ->
    bsvar_occur (evar_open dbi2 X phi) dbi1 = false.
  Proof.
    move: phi dbi1 dbi2.
    induction sz; move=> phi; destruct phi; simpl; move=> dbi1 dbi2 Hsz H; try rewrite !IHsz; auto; try lia; try apply orb_false_elim in H; firstorder.
    1,2: (destruct (n=? dbi2); reflexivity).
  Qed.

  Lemma bsvar_occur_evar_open dbi1 dbi2 X phi:
    bsvar_occur phi dbi1 = false ->
    bsvar_occur (evar_open dbi2 X phi) dbi1 = false.
  Proof.
    apply Private_bsvar_occur_evar_open with (sz := size phi). lia.
  Qed.  
  
  Lemma free_evars_subformula ϕ₁ ϕ₂ :
    is_subformula_of_ind ϕ₁ ϕ₂ -> free_evars ϕ₁ ⊆ free_evars ϕ₂.
  Proof.
    intros H. induction H.
    * subst. apply PreOrder_Reflexive.
    * simpl. eapply PreOrder_Transitive.
      apply IHis_subformula_of_ind.
      apply union_subseteq_l.
    * simpl. eapply PreOrder_Transitive.
      apply IHis_subformula_of_ind.
      apply union_subseteq_r.
    * simpl. eapply PreOrder_Transitive.
      apply IHis_subformula_of_ind.
      apply union_subseteq_l.
    * simpl. eapply PreOrder_Transitive.
      apply IHis_subformula_of_ind.
      apply union_subseteq_r.
    * simpl. auto.
    * simpl. auto.
  Qed.

  Lemma evar_fresh_svar_open x X dbi ϕ:
    evar_is_fresh_in x ϕ ->
    evar_is_fresh_in x (svar_open dbi X ϕ).
  Proof.
    unfold evar_is_fresh_in.
      by rewrite free_evars_svar_open.
  Qed.

  Lemma svar_fresh_evar_open x X dbi ϕ:
    svar_is_fresh_in X ϕ ->
    svar_is_fresh_in X (evar_open dbi x ϕ).
  Proof.
    unfold svar_is_fresh_in.
      by rewrite free_svars_evar_open.
  Qed.

  Lemma evar_fresh_in_subformula x ϕ₁ ϕ₂ :
    is_subformula_of_ind ϕ₁ ϕ₂ ->
    evar_is_fresh_in x ϕ₂ ->
    evar_is_fresh_in x ϕ₁.
  Proof.
    unfold evar_is_fresh_in.
    intros Hsub Hfresh.
    apply free_evars_subformula in Hsub.
    auto.
  Qed.

  Lemma evar_fresh_in_subformula' x ϕ₁ ϕ₂ :
    is_subformula_of ϕ₁ ϕ₂ ->
    evar_is_fresh_in x ϕ₂ ->
    evar_is_fresh_in x ϕ₁.
  Proof.
    intros Hsub Hfr.
    pose proof (H := elimT (is_subformula_of_P ϕ₁ ϕ₂) Hsub).
    eapply evar_fresh_in_subformula. eauto. auto.
  Qed.

  Lemma free_svars_subformula ϕ₁ ϕ₂ :
    is_subformula_of_ind ϕ₁ ϕ₂ -> free_svars ϕ₁ ⊆ free_svars ϕ₂.
  Proof.
    intros H. induction H.
    * subst. apply PreOrder_Reflexive.
    * simpl. eapply PreOrder_Transitive.
      apply IHis_subformula_of_ind.
      apply union_subseteq_l.
    * simpl. eapply PreOrder_Transitive.
      apply IHis_subformula_of_ind.
      apply union_subseteq_r.
    * simpl. eapply PreOrder_Transitive.
      apply IHis_subformula_of_ind.
      apply union_subseteq_l.
    * simpl. eapply PreOrder_Transitive.
      apply IHis_subformula_of_ind.
      apply union_subseteq_r.
    * simpl. auto.
    * simpl. auto.
  Qed.
  
  Lemma svar_fresh_in_subformula x ϕ₁ ϕ₂ :
    is_subformula_of_ind ϕ₁ ϕ₂ ->
    svar_is_fresh_in x ϕ₂ ->
    svar_is_fresh_in x ϕ₁.
  Proof.
    unfold svar_is_fresh_in.
    intros Hsub Hfresh.
    apply free_svars_subformula in Hsub.
    auto.
  Qed.

  Lemma free_evars_bsvar_subst ϕ₁ ϕ₂ dbi:
    free_evars (bsvar_subst ϕ₁ ϕ₂ dbi) ⊆ free_evars ϕ₁ ∪ free_evars ϕ₂.
  Proof.
    generalize dependent dbi.
    induction ϕ₁; intros db; simpl.
    - apply union_subseteq_l.
    - apply empty_subseteq.
    - apply empty_subseteq.
    - destruct (compare_nat n db); simpl.
      + apply empty_subseteq.
      + apply union_subseteq_r.
      +  apply empty_subseteq.
    - apply empty_subseteq.
    - specialize (IHϕ₁1 db).
      specialize (IHϕ₁2 db).
      remember (free_evars (bsvar_subst ϕ₁1 ϕ₂ db)) as A1.
      remember (free_evars (bsvar_subst ϕ₁2 ϕ₂ db)) as A2.
      remember (free_evars ϕ₁1) as B1.
      remember (free_evars ϕ₁2) as B2.
      remember (free_evars ϕ₂) as C.
      rewrite <- union_assoc_L.
      rewrite {1}[B2 ∪ C]union_comm_L.
      rewrite -{1}[C]union_idemp_L.
      rewrite -[C ∪ C ∪ B2]union_assoc_L.
      rewrite [B1 ∪ _]union_assoc_L.
      rewrite [C ∪ B2]union_comm_L.
      apply union_mono; auto.
    - apply empty_subseteq.
    - specialize (IHϕ₁1 db).
      specialize (IHϕ₁2 db).
      remember (free_evars (bsvar_subst ϕ₁1 ϕ₂ db)) as A1.
      remember (free_evars (bsvar_subst ϕ₁2 ϕ₂ db)) as A2.
      remember (free_evars ϕ₁1) as B1.
      remember (free_evars ϕ₁2) as B2.
      remember (free_evars ϕ₂) as C.
      rewrite <- union_assoc_L.
      rewrite {1}[B2 ∪ C]union_comm_L.
      rewrite -{1}[C]union_idemp_L.
      rewrite -[C ∪ C ∪ B2]union_assoc_L.
      rewrite [B1 ∪ _]union_assoc_L.
      rewrite [C ∪ B2]union_comm_L.
      apply union_mono; auto.
    - auto.
    - auto.
  Qed.

  Lemma free_evars_bsvar_subst_1 ϕ₁ ϕ₂ dbi:
    free_evars ϕ₁ ⊆ free_evars (bsvar_subst ϕ₁ ϕ₂ dbi).
  Proof.
    generalize dependent dbi.
    induction ϕ₁; intros dbi; simpl; try apply reflexivity.
    - apply empty_subseteq.
    - apply union_mono; auto.
    - apply union_mono; auto.
    - auto.
    - auto.
  Qed.

  Lemma free_evars_bsvar_subst_eq ϕ₁ ϕ₂ dbi:
    bsvar_occur ϕ₁ dbi ->
    free_evars (bsvar_subst ϕ₁ ϕ₂ dbi) = free_evars ϕ₁ ∪ free_evars ϕ₂.
  Proof.
    intros H.
    apply (anti_symm subseteq).
    - apply free_evars_bsvar_subst.
    - apply union_least.
      + apply free_evars_bsvar_subst_1.
      + pose proof (Hsub := @bsvar_subst_contains_subformula ϕ₁ ϕ₂ dbi H).
        apply free_evars_subformula. auto.
  Qed.

  Lemma bsvar_subst_not_occur_is_noop ϕ₁ ϕ₂ dbi:
    bsvar_occur ϕ₁ dbi = false ->
    bsvar_subst ϕ₁ ϕ₂ dbi = ϕ₁.
  Proof.
    generalize dependent dbi.
    induction ϕ₁; intros dbi H; simpl; simpl in H; auto.
    - case_bool_decide; case: (compare_nat n dbi); move=> H'.
      + inversion H.
      + inversion H.
      + inversion H.
      + auto.
      + contradiction.
      + auto.
    - apply orb_false_iff in H. destruct H as [H1 H2].
      rewrite -> IHϕ₁1. 2: auto.
      rewrite -> IHϕ₁2. 2: auto.
      auto.
    - apply orb_false_iff in H. destruct H as [H1 H2].
      rewrite -> IHϕ₁1. 2: auto.
      rewrite -> IHϕ₁2. 2: auto.
      auto.
    - rewrite -> IHϕ₁. 2: auto. auto.
    - rewrite -> IHϕ₁. 2: auto. auto.
  Qed.

  Lemma svar_open_not_occur_is_noop ϕ₁ X dbi:
    bsvar_occur ϕ₁ dbi = false ->
    svar_open dbi X ϕ₁ = ϕ₁.
  Proof.
    generalize dependent dbi.
    induction ϕ₁; intros dbi H; simpl; simpl in H; auto.
    - case_bool_decide; case: (compare_nat n dbi); move=> H'.
      + inversion H.
      + inversion H.
      + inversion H.
      + rewrite <- Nat.eqb_neq in H0. rewrite -> H0. auto.
      + contradiction.
      + rewrite <- Nat.eqb_neq in H0. rewrite -> H0. auto.
    - apply orb_false_iff in H. destruct H as [H1 H2].
      rewrite -> IHϕ₁1. 2: auto.
      rewrite -> IHϕ₁2. 2: auto.
      auto.
    - apply orb_false_iff in H. destruct H as [H1 H2].
      rewrite -> IHϕ₁1. 2: auto.
      rewrite -> IHϕ₁2. 2: auto.
      auto.
    - rewrite -> IHϕ₁. 2: auto. auto.
    - rewrite -> IHϕ₁. 2: auto. auto.
  Qed.

  Lemma wfc_aux_implies_not_bsvar_occur phi ne ns :
    well_formed_closed_aux phi ne ns ->
    ~ bsvar_occur phi ns.
  Proof.
    move: ne ns.
    induction phi; intros ne ns Hwfc; simpl; simpl in Hwfc; auto.
    - intros Hcontra.
      apply bool_decide_eq_true in Hcontra. apply Nat.ltb_lt in Hwfc. lia.
    - apply andb_true_iff in Hwfc.
      destruct Hwfc as [Hwfc1 Hwfc2].
      destruct (bsvar_occur phi1 ns) eqn:Heq1, (bsvar_occur phi2 ns) eqn:Heq2; simpl; intros Hcontra.
      + eapply IHphi1. apply Hwfc1. apply Heq1.
      + eapply IHphi1. apply Hwfc1. apply Heq1.
      + eapply IHphi2. apply Hwfc2. apply Heq2.
      + auto.
    - apply andb_true_iff in Hwfc.
      destruct Hwfc as [Hwfc1 Hwfc2].
      destruct (bsvar_occur phi1 ns) eqn:Heq1, (bsvar_occur phi2 ns) eqn:Heq2; simpl; intros Hcontra.
      + eapply IHphi1. apply Hwfc1. apply Heq1.
      + eapply IHphi1. apply Hwfc1. apply Heq1.
      + eapply IHphi2. apply Hwfc2. apply Heq2.
      + auto.
    - eapply IHphi. apply Hwfc.
    - eapply IHphi. apply Hwfc.
  Qed.
  
  Lemma wfc_implies_not_bsvar_occur phi n :
    well_formed_closed phi ->
    ~ bsvar_occur phi n.
  Proof.
    intros.
    eapply wfc_aux_implies_not_bsvar_occur.
    unfold well_formed_closed in H.
    eapply well_formed_closed_aux_ind.
    3: apply H.
    2: lia.
    constructor.
  Qed.

  Lemma not_bsvar_occur_bsvar_subst phi psi n:
    well_formed_closed psi ->
    ~ bsvar_occur (bsvar_subst phi psi n) n.
  Proof.
    move: n.
    induction phi; intros n' H; simpl; auto.
    - destruct (compare_nat n n') eqn:Heq.
      + simpl. destruct (bool_decide (n=n')) eqn:Heq'.
        apply bool_decide_eq_true in Heq'.
        lia. unfold not. apply ssrbool.not_false_is_true.
      + subst. apply wfc_implies_not_bsvar_occur. apply H.
      + simpl. destruct (bool_decide (n=n')) eqn:Heq'.
        apply bool_decide_eq_true in Heq'.
        lia. unfold not. apply ssrbool.not_false_is_true.
    - intros Hcontra.
      destruct (bsvar_occur (bsvar_subst phi1 psi n') n') eqn:Heq1, (bsvar_occur (bsvar_subst phi2 psi n') n') eqn:Heq2.
      + eapply IHphi2. apply H. apply Heq2.
      + eapply IHphi1. apply H. apply Heq1.
      + eapply IHphi2. apply H. apply Heq2.
      + simpl in Hcontra. apply notF in Hcontra. exact Hcontra.
    - intros Hcontra.
      destruct (bsvar_occur (bsvar_subst phi1 psi n') n')
               eqn:Heq1, (bsvar_occur (bsvar_subst phi2 psi n') n') eqn:Heq2.
      + eapply IHphi1. apply H. apply Heq1.
      + eapply IHphi1. apply H. apply Heq1.
      + eapply IHphi2. apply H. apply Heq2.
      + simpl in Hcontra. apply notF in Hcontra. exact Hcontra.
  Qed.

  Lemma not_bsvar_occur_impl_no_neg_occ_and_no_pos_occ phi n:
    ~ bsvar_occur phi n ->
    no_negative_occurrence_db_b n phi && no_positive_occurrence_db_b n phi.
  Proof.
    move: n.
    induction phi; intros n' H; simpl; simpl in H; auto.
    - unfold not in H.
      destruct (n =? n') eqn:Heq1, (bool_decide (n = n')) eqn:Heq2; simpl; auto.
      + apply beq_nat_true in Heq1. subst. rewrite -Heq2.
        apply bool_decide_eq_true. reflexivity.
    - destruct (bsvar_occur phi1 n') eqn: Heq3;
        destruct (bsvar_occur phi2 n') eqn:Heq4;
        simpl; auto.
      specialize (IHphi1 n'). specialize (IHphi2 n').
      rewrite Heq3 in IHphi1. rewrite Heq4 in IHphi2. clear Heq3 Heq4.
      specialize (IHphi1 ssrbool.not_false_is_true).
      specialize (IHphi2 ssrbool.not_false_is_true).
      apply andb_true_iff in IHphi1.
      apply andb_true_iff in IHphi2.
      destruct IHphi1 as [H1n H1p].
      destruct IHphi2 as [H2n H2p].
      rewrite H1n. rewrite H1p. rewrite H2n. rewrite H2p.
      simpl. reflexivity.
    - destruct (bsvar_occur phi1 n') eqn: Heq3;
        destruct (bsvar_occur phi2 n') eqn:Heq4;
        simpl; auto.
      specialize (IHphi1 n'). specialize (IHphi2 n').
      rewrite Heq3 in IHphi1. rewrite Heq4 in IHphi2. clear Heq3 Heq4.
      specialize (IHphi1 ssrbool.not_false_is_true).
      specialize (IHphi2 ssrbool.not_false_is_true).
      apply andb_true_iff in IHphi1.
      apply andb_true_iff in IHphi2.
      destruct IHphi1 as [H1n H1p].
      destruct IHphi2 as [H2n H2p].
      rewrite H1n. rewrite H1p. rewrite H2n. rewrite H2p.
      simpl. reflexivity.
  Qed.
  
  Lemma not_bsvar_occur_impl_pos_occ_db phi n:
    ~ bsvar_occur phi n ->
    positive_occurrence_db n phi.
  Proof.
    intros H.
    eapply elimT.
    apply (no_negative_occurrence_P n phi).
    pose proof (H1 := not_bsvar_occur_impl_no_neg_occ_and_no_pos_occ H).
    apply andb_true_iff in H1.
    destruct H1 as [H1 H2].
    apply H1.
  Qed.

  Lemma not_bsvar_occur_impl_neg_occ_db phi n:
    ~ bsvar_occur phi n ->
    negative_occurrence_db n phi.
  Proof.
    intros H.
    eapply elimT.
    apply (no_positive_occurrence_P n phi).
    pose proof (H1 := not_bsvar_occur_impl_no_neg_occ_and_no_pos_occ H).
    apply andb_true_iff in H1.
    destruct H1 as [H1 H2].
    apply H2.
  Qed.

  Lemma Private_wfc_impl_no_neg_pos_occ psi maxevar maxsvar dbi:
    well_formed_closed_aux psi maxevar maxsvar = true ->
    maxsvar <=? dbi ->
    no_negative_occurrence_db_b dbi psi = true
  /\ no_positive_occurrence_db_b dbi psi = true.
  Proof.
    move: dbi maxevar maxsvar.
    induction psi; intros dbi maxevar maxsvar Hwfc Hleq; simpl; auto.
    - split.
      { auto. }
      simpl in Hwfc.
      eapply introT.
      apply negP.
      intros Hcontra.
      eapply elimT in Hwfc.
      2: apply Nat.ltb_spec0.
      eapply elimT in Hcontra.
      2: apply Nat.eqb_spec.
      eapply elimT in Hleq.
      2: apply Nat.leb_spec0.
      lia.
    - split.
      + simpl in Hwfc.
        apply andb_prop in Hwfc. destruct Hwfc as [Hwfc1 Hwfc2].
        specialize (IHpsi1 dbi maxevar maxsvar Hwfc1 Hleq).
        specialize (IHpsi2 dbi maxevar maxsvar Hwfc2 Hleq).
        destruct IHpsi1 as [IHpsi11 IHpsi12].
        destruct IHpsi2 as [IHpsi21 IHpsi22].
        rewrite IHpsi11.
        rewrite IHpsi21.
        auto.
      + simpl in Hwfc.
        apply andb_prop in Hwfc. destruct Hwfc as [Hwfc1 Hwfc2].
        specialize (IHpsi1 dbi maxevar maxsvar Hwfc1 Hleq).
        specialize (IHpsi2 dbi maxevar maxsvar Hwfc2 Hleq).
        destruct IHpsi1 as [IHpsi11 IHpsi12].
        destruct IHpsi2 as [IHpsi21 IHpsi22].
        rewrite IHpsi12.
        rewrite IHpsi22.
        auto.
    - split.
      + simpl in Hwfc.
        apply andb_prop in Hwfc. destruct Hwfc as [Hwfc1 Hwfc2].
        specialize (IHpsi1 dbi maxevar maxsvar Hwfc1 Hleq).
        specialize (IHpsi2 dbi maxevar maxsvar Hwfc2 Hleq).
        destruct IHpsi1 as [IHpsi11 IHpsi12].
        destruct IHpsi2 as [IHpsi21 IHpsi22].
        rewrite IHpsi12.
        rewrite IHpsi21.
        auto.
      + simpl in Hwfc.
        apply andb_prop in Hwfc. destruct Hwfc as [Hwfc1 Hwfc2].
        specialize (IHpsi1 dbi maxevar maxsvar Hwfc1 Hleq).
        specialize (IHpsi2 dbi maxevar maxsvar Hwfc2 Hleq).
        destruct IHpsi1 as [IHpsi11 IHpsi12].
        destruct IHpsi2 as [IHpsi21 IHpsi22].
        rewrite IHpsi11.
        rewrite IHpsi22.
        auto.
    - simpl in Hwfc.
      specialize (IHpsi dbi (S maxevar) maxsvar Hwfc Hleq).
      destruct IHpsi.
      rewrite H. rewrite H0. auto.
    - simpl in Hwfc.
      specialize (IHpsi (S dbi) maxevar (S maxsvar)).
      assert (HS: S maxsvar <=? S dbi).
      { eapply elimT in Hleq.
        2: apply Nat.leb_spec0.
        eapply introT.
        apply Nat.leb_spec0.
        lia.
      }
      specialize (IHpsi Hwfc HS).
      apply IHpsi.
  Qed.
  

  Lemma wfc_impl_no_neg_occ psi dbi:
    well_formed_closed psi = true ->
    no_negative_occurrence_db_b dbi psi = true.
  Proof.
    intros H.
    unfold well_formed_closed in H.
    pose proof (HX := Private_wfc_impl_no_neg_pos_occ).
    specialize (HX psi 0 0 dbi H).
    simpl in HX.
    specialize (HX isT).
    destruct HX as [HX1 HX2].
    apply HX1.
  Qed.

  Lemma wfc_impl_no_pos_occ psi dbi:
    well_formed_closed psi = true ->
    no_positive_occurrence_db_b dbi psi = true.
  Proof.
    intros H.
    unfold well_formed_closed in H.
    pose proof (HX := Private_wfc_impl_no_neg_pos_occ).
    specialize (HX psi 0 0 dbi H).
    simpl in HX.
    specialize (HX isT).
    destruct HX as [HX1 HX2].
    apply HX2.
  Qed.
  
  
  Lemma no_neg_occ_db_bsvar_subst phi psi dbi1 dbi2:
    well_formed_closed psi = true ->
    (no_negative_occurrence_db_b dbi1 phi = true ->
    no_negative_occurrence_db_b dbi1 (bsvar_subst phi psi dbi2) = true)
  /\ (no_positive_occurrence_db_b dbi1 phi = true ->
    no_positive_occurrence_db_b dbi1 (bsvar_subst phi psi dbi2) = true).
  Proof.
    intros Hwfcpsi.
    move: dbi1 dbi2.

    induction phi; intros dbi1 dbi2; simpl; auto.
    - destruct (compare_nat n dbi2); auto.
      split; intros H.
      + apply wfc_impl_no_neg_occ. apply Hwfcpsi.
      + apply wfc_impl_no_pos_occ. apply Hwfcpsi.
    - specialize (IHphi1 dbi1 dbi2).
      specialize (IHphi2 dbi1 dbi2).
      destruct IHphi1 as [IHphi11 IHphi12].
      destruct IHphi2 as [IHphi21 IHphi22].
      split; intro H.
      + eapply elimT in H.
        2: apply andP.
        destruct H as [H1 H2].
        specialize (IHphi11 H1).
        specialize (IHphi21 H2).
        rewrite IHphi11 IHphi21. reflexivity.
      + eapply elimT in H.
        2: apply andP.
        destruct H as [H1 H2].
        specialize (IHphi12 H1).
        specialize (IHphi22 H2).
        rewrite IHphi12 IHphi22. reflexivity.
    - specialize (IHphi1 dbi1 dbi2).
      specialize (IHphi2 dbi1 dbi2).
      destruct IHphi1 as [IHphi11 IHphi12].
      destruct IHphi2 as [IHphi21 IHphi22].
      split; intro H.
      + eapply elimT in H.
        2: apply andP.
        destruct H as [H1 H2].
        specialize (IHphi12 H1).
        specialize (IHphi21 H2).
        rewrite IHphi12 IHphi21. reflexivity.
      + eapply elimT in H.
        2: apply andP.
        destruct H as [H1 H2].
        specialize (IHphi11 H1).
        specialize (IHphi22 H2).
        rewrite IHphi11 IHphi22. reflexivity.
  Qed.
  

  Lemma Private_wfp_bsvar_subst (phi psi : Pattern) (n : nat) :
    well_formed_positive psi ->
    well_formed_closed psi ->
    well_formed_positive phi ->
    (
    no_negative_occurrence_db_b n phi ->
    well_formed_positive (bsvar_subst phi psi n) )
    /\ (no_positive_occurrence_db_b n phi ->
        forall phi',
          well_formed_positive phi' ->
          well_formed_positive (patt_imp (bsvar_subst phi psi n) phi')
       )
  .
  Proof.
    intros Hwfppsi Hwfcpsi.
    move: n.
    induction phi; intros n' Hwfpphi; simpl in *; auto.
    - split.
      + intros _. destruct (compare_nat n n'); auto.
      + intros H phi' Hwfphi'.
        destruct (compare_nat n n'); auto. rewrite Hwfppsi. rewrite Hwfphi'.
        auto.
    - split.
      + intros Hnoneg.
        apply andb_prop in Hnoneg. destruct Hnoneg as [Hnoneg1 Hnoneg2].
        apply andb_prop in Hwfpphi. destruct Hwfpphi as [Hwfpphi1 Hwfpphi2].
        
        specialize (IHphi1 n' Hwfpphi1).
        destruct IHphi1 as [IHphi11 IHphi12].
        specialize (IHphi11 Hnoneg1).
        rewrite IHphi11.

        specialize (IHphi2 n' Hwfpphi2).
        destruct IHphi2 as [IHphi21 IHphi22].
        specialize (IHphi21 Hnoneg2).
        rewrite IHphi21.
        auto.
        
      + intros Hnopos.
        apply andb_prop in Hnopos. destruct Hnopos as [Hnopos1 Hnopos2].
        apply andb_prop in Hwfpphi. destruct Hwfpphi as [Hwfpphi1 Hwfpphi2].
        intros phi' Hwfpphi'.

        specialize (IHphi1 n' Hwfpphi1).
        specialize (IHphi2 n' Hwfpphi2).
        destruct IHphi1 as [IHphi11 IHphi12].
        destruct IHphi2 as [IHphi21 IHphi22].
        rewrite IHphi12.
        { rewrite Hnopos1. auto. }
        specialize (IHphi22 Hnopos2 phi' Hwfpphi').
        apply andb_prop in IHphi22. destruct IHphi22 as [IHphi221 IHphi222].
        rewrite IHphi221. auto.
        rewrite Hwfpphi'. auto.

    - split.
      + intros Hnoposneg.
        apply andb_prop in Hnoposneg. destruct Hnoposneg as [Hnopos1 Hnoneg2].
        apply andb_prop in Hwfpphi. destruct Hwfpphi as [Hwfpphi1 Hwfpphi2].
        specialize (IHphi1 n' Hwfpphi1).
        specialize (IHphi2 n' Hwfpphi2).
        destruct IHphi1 as [IHphi11 IHphi12].
        destruct IHphi2 as [IHphi21 IHphi22].
        specialize (IHphi12 Hnopos1). clear IHphi11.
        specialize (IHphi21 Hnoneg2). clear IHphi22.
        rewrite IHphi21.

        specialize (IHphi12 patt_bott). simpl in IHphi12.
        assert (Htrue: is_true true).
        { auto. }
        specialize (IHphi12 Htrue).
        rewrite IHphi12.
        auto.
      + intros Hnoposneg phi' Hwfpphi'.
        apply andb_prop in Hnoposneg. destruct Hnoposneg as [Hnopos1 Hnoneg2].
        apply andb_prop in Hwfpphi. destruct Hwfpphi as [Hwfpphi1 Hwfpphi2].
        specialize (IHphi1 n' Hwfpphi1).
        specialize (IHphi2 n' Hwfpphi2).
        destruct IHphi1 as [IHphi11 IHphi12].
        destruct IHphi2 as [IHphi21 IHphi22].
        specialize (IHphi11 Hnopos1). clear IHphi12.
        specialize (IHphi22 Hnoneg2). clear IHphi21.
        rewrite IHphi11. rewrite IHphi22; auto.
    -
      apply andb_prop in Hwfpphi. destruct Hwfpphi as [Hwfpphi1 Hwfpphi2].
      pose proof (IHphi' := IHphi (S n') Hwfpphi2).
      destruct IHphi' as [IHphi1' IHphi2'].
      assert (H: no_negative_occurrence_db_b 0 (bsvar_subst phi psi (S n'))).
      { clear IHphi1' IHphi2'.
        apply no_neg_occ_db_bsvar_subst; auto.
      }
      split.
      + intros Hnonegphi.
        specialize (IHphi1' Hnonegphi).
        rewrite IHphi1'.
        rewrite H.
        auto.
      + intros Hnopos phi' Hwfpphi'.
        rewrite H.
        rewrite IHphi2'.
        rewrite Hnopos.
        2: rewrite Hwfpphi'.
        1,2,3: auto.
  Qed.

  
  Lemma wfp_bsvar_subst (phi psi : Pattern) :
    well_formed_positive (patt_mu phi) ->
    well_formed_positive psi ->
    well_formed_closed psi ->
    well_formed_positive (bsvar_subst phi psi 0).
  Proof.
    intros H1 H2 H3.
    simpl in H1.
    eapply elimT in H1. 2: apply andP.
    destruct H1 as [Hnonegphi Hwfpphi].
    pose proof (H4 := Private_wfp_bsvar_subst).
    specialize (H4 phi psi 0 H2 H3 Hwfpphi).
    destruct H4 as [H41 H42].
    apply H41.
    apply Hnonegphi.
 Qed.


  (* Section: nest_ex, nest_mu *)

  Fixpoint nest_ex_aux level ϕ {struct ϕ} : Pattern :=
    match ϕ with
    | patt_free_evar _ => ϕ
    | patt_free_svar _ => ϕ
    | patt_bound_evar n => patt_bound_evar (if (level <=? n) then (S n) else n)
    | patt_bound_svar _ => ϕ
    | patt_sym _ => ϕ
    | patt_bott => ϕ
    | patt_app ϕ₁ ϕ₂ => patt_app (nest_ex_aux level ϕ₁) (nest_ex_aux level ϕ₂)
    | patt_imp ϕ₁ ϕ₂ => patt_imp (nest_ex_aux level ϕ₁) (nest_ex_aux level ϕ₂)
    | patt_exists ϕ' => patt_exists (nest_ex_aux (S level) ϕ')
    | patt_mu ϕ' => patt_mu (nest_ex_aux level ϕ')
    end.

  Fixpoint nest_mu_aux level ϕ {struct ϕ} : Pattern :=
    match ϕ with
    | patt_free_evar _ => ϕ
    | patt_free_svar _ => ϕ
    | patt_bound_evar _ => ϕ
    | patt_bound_svar n => patt_bound_svar (if (level <=? n) then (S n) else n)
    | patt_sym _ => ϕ
    | patt_bott => ϕ
    | patt_app ϕ₁ ϕ₂ => patt_app (nest_mu_aux level ϕ₁) (nest_mu_aux level ϕ₂)
    | patt_imp ϕ₁ ϕ₂ => patt_imp (nest_mu_aux level ϕ₁) (nest_mu_aux level ϕ₂)
    | patt_exists ϕ' => patt_exists (nest_mu_aux level ϕ')
    | patt_mu ϕ' => patt_mu (nest_mu_aux (S level) ϕ')
    end.

  Lemma not_bevar_occur_level_nest_ex_aux level ϕ :
    bevar_occur (nest_ex_aux level ϕ) level = false.
  Proof.
    move: ϕ level.
    induction ϕ; move=> level; simpl; auto.
    - case_bool_decide. 2: reflexivity.
      destruct (PeanoNat.Nat.leb_spec0 level n); lia.
    - rewrite IHϕ1. rewrite IHϕ2. simpl. reflexivity.
    - rewrite IHϕ1. rewrite IHϕ2. simpl. reflexivity.
  Qed.

  Lemma not_bsvar_occur_level_nest_mu_aux level ϕ :
    bsvar_occur (nest_mu_aux level ϕ) level = false.
  Proof.
    move: ϕ level.
    induction ϕ; move=> level; simpl; auto.
    - case_bool_decide. 2: reflexivity.
      destruct (PeanoNat.Nat.leb_spec0 level n); lia.
    - rewrite IHϕ1. rewrite IHϕ2. simpl. reflexivity.
    - rewrite IHϕ1. rewrite IHϕ2. simpl. reflexivity.
  Qed.

  Lemma svar_open_nest_ex_aux_comm level ϕ dbi X:
    svar_open dbi X (nest_ex_aux level ϕ) = nest_ex_aux level (svar_open dbi X ϕ).
  Proof.
    move: level dbi.
    induction ϕ; move=> level dbi; simpl; auto.
    - case (n =? dbi); reflexivity.
    - rewrite IHϕ1. rewrite IHϕ2. reflexivity.
    - rewrite IHϕ1. rewrite IHϕ2. reflexivity.
    - rewrite IHϕ. reflexivity.
    - rewrite IHϕ. reflexivity.
  Qed.

  Lemma evar_open_nest_mu_aux_comm level ϕ dbi X:
    evar_open dbi X (nest_mu_aux level ϕ) = nest_mu_aux level (evar_open dbi X ϕ).
  Proof.
    move: level dbi.
    induction ϕ; move=> level dbi; simpl; auto.
    - case (n =? dbi); reflexivity.
    - rewrite IHϕ1. rewrite IHϕ2. reflexivity.
    - rewrite IHϕ1. rewrite IHϕ2. reflexivity.
    - rewrite IHϕ. reflexivity.
    - rewrite IHϕ. reflexivity.
  Qed.

  Lemma evar_open_nest_ex_aux_comm level ϕ dbi X:
    evar_open dbi X (nest_ex_aux level ϕ)
    = match (compare_nat dbi level) with
      | Nat_less _ _ _ => nest_ex_aux level (evar_open dbi X ϕ)
      | Nat_equal _ _ _ => nest_ex_aux level ϕ
      | Nat_greater _ _ _ => nest_ex_aux level (evar_open (dbi-1) X ϕ)
      end.
  Proof.
    move: level dbi.
    induction ϕ; move=> level dbi; destruct (compare_nat dbi level); simpl; auto.
    1: {destruct (Nat.leb_spec0 level n); simpl;
      destruct dbi; simpl;
        destruct (Nat.leb_spec0 level n); simpl;
          try destruct (eqb_reflect n dbi),(eqb_reflect n (S dbi)); simpl;
            try reflexivity; try lia;
              destruct (Nat.leb_spec0 level n); simpl; try reflexivity; try lia.
      1,2: destruct (eqb_reflect n 0); simpl; try lia; try reflexivity.
      1,2: destruct (Nat.leb_spec0 level n); try lia; try reflexivity.
      }
    1: {destruct (Nat.leb_spec level n); simpl.
      + destruct dbi.
        * reflexivity.
        * destruct (eqb_reflect n dbi); try lia. reflexivity.
      + destruct (eqb_reflect n dbi); try lia. reflexivity.
    }
    
    1: {destruct (Nat.leb_spec0 level n); simpl;
        destruct (eqb_reflect n (dbi - 1)).
      1,2: destruct dbi; try lia.
      1,2,3,4: destruct (eqb_reflect n dbi); simpl; try reflexivity; try lia.
      1,2: destruct (eqb_reflect level n); simpl;
        destruct (Nat.leb_spec0 level n); try reflexivity; try lia.
    }
    1,2,3,4,5,6: (rewrite IHϕ1; rewrite IHϕ2;
                  destruct (compare_nat dbi level); simpl; try reflexivity; try lia).
    
    4,5,6: (rewrite IHϕ; destruct (compare_nat dbi level); simpl; try reflexivity; try lia).
    1,2,3: (rewrite IHϕ; destruct (compare_nat (S dbi) (S level)); simpl; try reflexivity; try lia).
    assert (Hdbi1: dbi - 0 = dbi). lia.
    assert (Hdbi2: S (dbi - 1) = dbi). lia.
    rewrite Hdbi1. rewrite Hdbi2. reflexivity.
  Qed.

  Lemma svar_open_nest_mu_aux_comm level ϕ dbi X:
    svar_open dbi X (nest_mu_aux level ϕ)
    = match (compare_nat dbi level) with
      | Nat_less _ _ _ => nest_mu_aux level (svar_open dbi X ϕ)
      | Nat_equal _ _ _ => nest_mu_aux level ϕ
      | Nat_greater _ _ _ => nest_mu_aux level (svar_open (dbi-1) X ϕ)
      end.
  Proof.
    move: level dbi.
    induction ϕ; move=> level dbi; destruct (compare_nat dbi level); simpl; auto.
    1: {destruct (Nat.leb_spec0 level n); simpl;
      destruct dbi; simpl;
        destruct (Nat.leb_spec0 level n); simpl;
          try destruct (eqb_reflect n dbi),(eqb_reflect n (S dbi)); simpl;
            try reflexivity; try lia;
              destruct (Nat.leb_spec0 level n); simpl; try reflexivity; try lia.
      1,2: destruct (eqb_reflect n 0); simpl; try lia; try reflexivity.
      1,2: destruct (Nat.leb_spec0 level n); try lia; try reflexivity.
      }
    1: {destruct (Nat.leb_spec level n); simpl.
      + destruct dbi.
        * reflexivity.
        * destruct (eqb_reflect n dbi); try lia. reflexivity.
      + destruct (eqb_reflect n dbi); try lia. reflexivity.
    }
    
    1: {destruct (Nat.leb_spec0 level n); simpl;
        destruct (eqb_reflect n (dbi - 1)).
      1,2: destruct dbi; try lia.
      1,2,3,4: destruct (eqb_reflect n dbi); simpl; try reflexivity; try lia.
      1,2: destruct (eqb_reflect level n); simpl;
        destruct (Nat.leb_spec0 level n); try reflexivity; try lia.
    }
    1,2,3,4,5,6: (rewrite IHϕ1; rewrite IHϕ2;
                  destruct (compare_nat dbi level); simpl; try reflexivity; try lia).
    
    1,2,3: (rewrite IHϕ; destruct (compare_nat dbi level); simpl; try reflexivity; try lia).
    1,2,3: (rewrite IHϕ; destruct (compare_nat (S dbi) (S level)); simpl; try reflexivity; try lia).
    assert (Hdbi1: dbi - 0 = dbi). lia.
    assert (Hdbi2: S (dbi - 1) = dbi). lia.
    rewrite Hdbi1. rewrite Hdbi2. reflexivity.
  Qed.

  
  Lemma free_svars_nest_ex_aux dbi ϕ:
    free_svars (nest_ex_aux dbi ϕ) = free_svars ϕ.
  Proof.
    move: dbi. induction ϕ; move=> dbi; simpl; try reflexivity.
    - rewrite IHϕ1. rewrite IHϕ2. reflexivity.
    - rewrite IHϕ1. rewrite IHϕ2. reflexivity.
    - rewrite IHϕ. reflexivity.
    - rewrite IHϕ. reflexivity.
  Qed.

  Lemma free_evars_nest_mu_aux dbi ϕ:
    free_evars (nest_mu_aux dbi ϕ) = free_evars ϕ.
  Proof.
    move: dbi. induction ϕ; move=> dbi; simpl; try reflexivity.
    - rewrite IHϕ1. rewrite IHϕ2. reflexivity.
    - rewrite IHϕ1. rewrite IHϕ2. reflexivity.
    - rewrite IHϕ. reflexivity.
    - rewrite IHϕ. reflexivity.
  Qed.
  
  Lemma free_evars_nest_ex_aux dbi ϕ:
    free_evars (nest_ex_aux dbi ϕ) = free_evars ϕ.
  Proof.
    move: dbi. induction ϕ; move=> dbi; simpl; try reflexivity.
    - rewrite IHϕ1. rewrite IHϕ2. reflexivity.
    - rewrite IHϕ1. rewrite IHϕ2. reflexivity.
    - rewrite IHϕ. reflexivity.
    - rewrite IHϕ. reflexivity.
  Qed.

  Lemma free_svars_nest_mu_aux dbi ϕ:
    free_svars (nest_mu_aux dbi ϕ) = free_svars ϕ.
  Proof.
    move: dbi. induction ϕ; move=> dbi; simpl; try reflexivity.
    - rewrite IHϕ1. rewrite IHϕ2. reflexivity.
    - rewrite IHϕ1. rewrite IHϕ2. reflexivity.
    - rewrite IHϕ. reflexivity.
    - rewrite IHϕ. reflexivity.
  Qed.

  Lemma fresh_svar_nest_ex_aux dbi ϕ:
    fresh_svar (nest_ex_aux dbi ϕ) = fresh_svar ϕ.
  Proof.
    unfold fresh_svar.
      by rewrite free_svars_nest_ex_aux.
  Qed.

  Lemma fresh_evar_nest_mu_aux dbi ϕ:
    fresh_evar (nest_mu_aux dbi ϕ) = fresh_evar ϕ.
  Proof.
    unfold fresh_evar.
      by rewrite free_evars_nest_mu_aux.
  Qed.

  Lemma fresh_evar_nest_ex_aux dbi ϕ:
    fresh_evar (nest_ex_aux dbi ϕ) = fresh_evar ϕ.
  Proof.
    unfold fresh_evar.
      by rewrite free_evars_nest_ex_aux.
  Qed.

  Lemma fresh_svar_nest_mu_aux dbi ϕ:
    fresh_svar (nest_mu_aux dbi ϕ) = fresh_svar ϕ.
  Proof.
    unfold fresh_svar.
      by rewrite free_svars_nest_mu_aux.
  Qed.
  

  Definition nest_ex ϕ := nest_ex_aux 0 ϕ.
  Definition nest_mu ϕ := nest_mu_aux 0 ϕ.

  Lemma not_bevar_occur_0_nest_ex ϕ :
    bevar_occur (nest_ex ϕ) 0 = false.
  Proof.
    exact (not_bevar_occur_level_nest_ex_aux 0 ϕ).
  Qed.

  Lemma not_bsvar_occur_0_nest_mu ϕ :
    bsvar_occur (nest_mu ϕ) 0 = false.
  Proof.
    exact (not_bsvar_occur_level_nest_mu_aux 0 ϕ).
  Qed.

  Lemma svar_open_nest_ex_comm ϕ dbi X:
    svar_open dbi X (nest_ex ϕ) = nest_ex (svar_open dbi X ϕ).
  Proof.
    exact (svar_open_nest_ex_aux_comm 0 ϕ dbi X).
  Qed.

  Lemma evar_open_nest_mu_comm ϕ dbi X:
    evar_open dbi X (nest_mu ϕ) = nest_mu (evar_open dbi X ϕ).
  Proof.
    exact (evar_open_nest_mu_aux_comm 0 ϕ dbi X).
  Qed.

  Lemma evar_is_fresh_in_app_l x ϕ₁ ϕ₂ :
    evar_is_fresh_in x (patt_app ϕ₁ ϕ₂) -> evar_is_fresh_in x ϕ₁.
  Proof.
    unfold evar_is_fresh_in. simpl.
    move/not_elem_of_union => [H1 H2].
    done.
  Qed.

  (*Hint Resolve evar_is_fresh_in_app_l : core.*)

  Lemma evar_is_fresh_in_app_r x ϕ₁ ϕ₂ :
    evar_is_fresh_in x (patt_app ϕ₁ ϕ₂) -> evar_is_fresh_in x ϕ₂.
  Proof.
    unfold evar_is_fresh_in. simpl.
    move/not_elem_of_union => [H1 H2].
    done.
  Qed.

  (*Hint Resolve evar_is_fresh_in_app_r : core.*)

  Lemma evar_is_fresh_in_imp_l x ϕ₁ ϕ₂ :
    evar_is_fresh_in x (patt_imp ϕ₁ ϕ₂) -> evar_is_fresh_in x ϕ₁.
  Proof.
    unfold evar_is_fresh_in. simpl.
    move/not_elem_of_union => [H1 H2].
    done.
  Qed.

  (*Hint Resolve evar_is_fresh_in_imp_l : core.*)

  Lemma evar_is_fresh_in_imp_r x ϕ₁ ϕ₂ :
    evar_is_fresh_in x (patt_imp ϕ₁ ϕ₂) -> evar_is_fresh_in x ϕ₂.
  Proof.
    unfold evar_is_fresh_in. simpl.
    move/not_elem_of_union => [H1 H2].
    done.
  Qed.

  (*Hint Resolve evar_is_fresh_in_imp_r : core.*)

  Lemma evar_is_fresh_in_exists x ϕ :
    evar_is_fresh_in x (patt_exists ϕ) -> evar_is_fresh_in x ϕ.
  Proof.
    unfold evar_is_fresh_in. simpl. done.
  Qed.

  (*Hint Resolve evar_is_fresh_in_exists : core.*)

  Lemma evar_is_fresh_in_mu x ϕ :
    evar_is_fresh_in x (patt_mu ϕ) -> evar_is_fresh_in x ϕ.
  Proof.
    unfold evar_is_fresh_in. simpl. done.
  Qed.

  (*Hint Resolve evar_is_fresh_in_mu : core.*)

  (**)
  Lemma svar_is_fresh_in_app_l x ϕ₁ ϕ₂ :
    svar_is_fresh_in x (patt_app ϕ₁ ϕ₂) -> svar_is_fresh_in x ϕ₁.
  Proof.
    unfold svar_is_fresh_in. simpl.
    move/not_elem_of_union => [H1 H2].
    done.
  Qed.

  Lemma svar_is_fresh_in_app_r x ϕ₁ ϕ₂ :
    svar_is_fresh_in x (patt_app ϕ₁ ϕ₂) -> svar_is_fresh_in x ϕ₂.
  Proof.
    unfold svar_is_fresh_in. simpl.
    move/not_elem_of_union => [H1 H2].
    done.
  Qed.

  Lemma svar_is_fresh_in_imp_l x ϕ₁ ϕ₂ :
    svar_is_fresh_in x (patt_imp ϕ₁ ϕ₂) -> svar_is_fresh_in x ϕ₁.
  Proof.
    unfold svar_is_fresh_in. simpl.
    move/not_elem_of_union => [H1 H2].
    done.
  Qed.

  Lemma svar_is_fresh_in_imp_r x ϕ₁ ϕ₂ :
    svar_is_fresh_in x (patt_imp ϕ₁ ϕ₂) -> svar_is_fresh_in x ϕ₂.
  Proof.
    unfold svar_is_fresh_in. simpl.
    move/not_elem_of_union => [H1 H2].
    done.
  Qed.

  Lemma svar_is_fresh_in_exists x ϕ :
    svar_is_fresh_in x (patt_exists ϕ) -> svar_is_fresh_in x ϕ.
  Proof.
    unfold svar_is_fresh_in. simpl. done.
  Qed.

  Lemma svar_is_fresh_in_mu x ϕ :
    svar_is_fresh_in x (patt_mu ϕ) -> svar_is_fresh_in x ϕ.
  Proof.
    unfold svar_is_fresh_in. simpl. done.
  Qed.

    Definition simpl_free_evars :=
  (
    (@left_id_L EVarSet  ∅ (@union _ _)),
    (@right_id_L EVarSet ∅ (@union _ _)),
    @free_evars_nest_ex_aux,
    @evar_open_nest_ex_aux_comm,
    @free_evars_nest_ex_aux
  ).

    Lemma x_eq_fresh_impl_x_notin_free_evars x ϕ:
      x = fresh_evar ϕ ->
      x ∉ free_evars ϕ.
    Proof.
      intros H.
      rewrite H.
      unfold fresh_evar.
      apply set_evar_fresh_is_fresh'.
    Qed.

    Hint Resolve x_eq_fresh_impl_x_notin_free_evars : core.

    Definition simpl_free_svars :=
      (
        (@left_id_L SVarSet  ∅ (@union _ _)),
        (@right_id_L SVarSet ∅ (@union _ _)),
        @free_svars_nest_mu_aux,
        @svar_open_nest_mu_aux_comm,
        @free_svars_nest_mu_aux
      ).
    
    Lemma X_eq_fresh_impl_X_notin_free_svars X ϕ:
      X = fresh_svar ϕ ->
      X ∉ free_svars ϕ.
    Proof.
      intros H.
      rewrite H.
      unfold fresh_svar.
      apply set_svar_fresh_is_fresh'.
    Qed.

    Lemma X_eq_evar_fresh_impl_X_notin_S X (S:EVarSet):
      X = evar_fresh (elements S) ->
      X ∉ S.
    Proof.
      intros H.
      rewrite H.
      apply set_evar_fresh_is_fresh'.
    Qed.
    
    Lemma X_eq_svar_fresh_impl_X_notin_S X (S:SVarSet):
      X = svar_fresh (elements S) ->
      X ∉ S.
    Proof.
      intros H.
      rewrite H.
      apply set_svar_fresh_is_fresh'.
    Qed.

    Hint Resolve X_eq_fresh_impl_X_notin_free_svars : core.

    Lemma Private_positive_negative_occurrence_db_nest_mu_aux dbi level ϕ:
      (no_negative_occurrence_db_b dbi (nest_mu_aux level ϕ)
      = match (compare_nat dbi level) with
          | Nat_less _ _ _ => no_negative_occurrence_db_b dbi ϕ
          | Nat_equal _ _ _ => true
          | Nat_greater _ _ _ => no_negative_occurrence_db_b (dbi-1) ϕ
          end
      ) /\ (
      no_positive_occurrence_db_b dbi (nest_mu_aux level ϕ)
      = match (compare_nat dbi level) with
          | Nat_less _ _ _ => no_positive_occurrence_db_b dbi ϕ
          | Nat_equal _ _ _ => true
          | Nat_greater _ _ _ => no_positive_occurrence_db_b (dbi-1) ϕ
          end
      ).
    Proof.
      move: dbi level.
      induction ϕ; intros dbi level; simpl;
        destruct (compare_nat dbi level); auto;
      repeat (
          match goal with
          | |- context G [?x <=? ?y] => destruct (Nat.leb_spec0 x y)
          | |- context G [?x =? ?y] => destruct (Nat.eqb_spec x y)
          end
        ); simpl; try lia; auto;
        try rewrite (proj1 (IHϕ1 _ _));
        try rewrite (proj2 (IHϕ1 _ _));
        try rewrite (proj1 (IHϕ2 _ _));
        try rewrite (proj2 (IHϕ2 _ _));
        try rewrite (proj1 (IHϕ _ _));
        try rewrite (proj2 (IHϕ _ _));
        simpl;
        destruct (compare_nat dbi level),(compare_nat (S dbi) (S level)); simpl; try lia; auto.
      assert (Harith1: dbi - 0 = dbi). lia. rewrite !Harith1.
      assert (Harith2: S (dbi - 1) = dbi). lia. rewrite !Harith2.
      auto.
    Qed.

    Lemma no_negative_occurrence_db_nest_mu_aux dbi level ϕ:
      no_negative_occurrence_db_b dbi (nest_mu_aux level ϕ)
      = match (compare_nat dbi level) with
          | Nat_less _ _ _ => no_negative_occurrence_db_b dbi ϕ
          | Nat_equal _ _ _ => true
          | Nat_greater _ _ _ => no_negative_occurrence_db_b (dbi-1) ϕ
        end.
    Proof.
      apply Private_positive_negative_occurrence_db_nest_mu_aux.
    Qed.

    Lemma no_positive_occurrence_db_nest_mu_aux dbi level ϕ:
      no_positive_occurrence_db_b dbi (nest_mu_aux level ϕ)
      = match (compare_nat dbi level) with
          | Nat_less _ _ _ => no_positive_occurrence_db_b dbi ϕ
          | Nat_equal _ _ _ => true
          | Nat_greater _ _ _ => no_positive_occurrence_db_b (dbi-1) ϕ
        end.
    Proof.
      apply Private_positive_negative_occurrence_db_nest_mu_aux.
    Qed.

    Lemma well_formed_positive_nest_mu_aux level ϕ:
      well_formed_positive (nest_mu_aux level ϕ) = well_formed_positive ϕ.
    Proof.
      move: level.
      induction ϕ; intros level; simpl; auto.
      - rewrite IHϕ1. rewrite IHϕ2. auto.
      - rewrite IHϕ1. rewrite IHϕ2. auto.
      - rewrite IHϕ.
        rewrite no_negative_occurrence_db_nest_mu_aux. simpl.
        reflexivity.
    Qed.
    
Lemma evar_open_inj : ∀ phi psi x n,
  evar_is_fresh_in x phi → evar_is_fresh_in x psi →
  evar_open n x phi =
    evar_open n x psi
    → phi = psi.
Proof.
  induction phi; destruct psi; intros; try (simpl in H1; congruence); try (simpl in H1; destruct (n =? n0) eqn:P; congruence); auto.
  - simpl in H1. destruct (n =? n0) eqn:P.
    + inversion H1. subst. unfold evar_is_fresh_in in H. simpl in H. apply not_elem_of_singleton_1 in H.
      congruence.
    + congruence.
  - simpl in H1. destruct (n =? n0) eqn:P.
    + inversion H1. subst. unfold evar_is_fresh_in in H0. simpl in H0. apply not_elem_of_singleton_1 in H0.
      congruence.
    + congruence.
  - simpl in H1. destruct (n =? n1) eqn:P; destruct (n0 =? n1) eqn:P2.
    + apply Nat.eqb_eq in P. apply Nat.eqb_eq in P2. subst. reflexivity.
    + congruence.
    + congruence.
    + inversion H1. reflexivity.
  - simpl in H1. destruct (n =? n1) eqn:P.
    + inversion H1.
    + congruence.
  - inversion H1. destruct (n0 =? n1) eqn:P.
    + inversion H3.
    + assumption.
  - inversion H1. apply IHphi1 in H3. apply IHphi2 in H4. subst. reflexivity.
    apply evar_is_fresh_in_app_r in H. assumption.
    apply evar_is_fresh_in_app_r in H0. assumption.
    apply evar_is_fresh_in_app_l in H. assumption.
    apply evar_is_fresh_in_app_l in H0. assumption.
  - inversion H1. apply IHphi1 in H3. apply IHphi2 in H4. subst. reflexivity.
    apply evar_is_fresh_in_imp_r in H. assumption.
    apply evar_is_fresh_in_imp_r in H0. assumption.
    apply evar_is_fresh_in_imp_l in H. assumption.
    apply evar_is_fresh_in_imp_l in H0. assumption.
  - inversion H1. apply IHphi in H3. subst. reflexivity.
    apply evar_is_fresh_in_exists in H. assumption.
    apply evar_is_fresh_in_exists in H0. assumption.
  - inversion H1. apply IHphi in H3. subst. reflexivity.
    apply evar_is_fresh_in_mu in H. assumption.
    apply evar_is_fresh_in_mu in H0. assumption.
Qed.

Lemma svar_open_inj : ∀ phi psi X n,
  svar_is_fresh_in X phi → svar_is_fresh_in X psi →
  svar_open n X phi =
    svar_open n X psi
    → phi = psi.
Proof.
  induction phi; destruct psi; intros; try (simpl in H1; congruence); try (simpl in H1; destruct (n =? n0) eqn:P; congruence); auto.
  - simpl in H1. destruct (n =? n0) eqn:P.
    + inversion H1. subst. unfold svar_is_fresh_in in H. simpl in H. apply not_elem_of_singleton_1 in H.
      congruence.
    + congruence.
  - inversion H1. destruct (n0 =? n1) eqn:P.
    + inversion H3.
    + assumption.
  - simpl in H1. destruct (n =? n0) eqn:P.
    + inversion H1. subst. unfold svar_is_fresh_in in H0. simpl in H0. apply not_elem_of_singleton_1 in H0.
      congruence.
    + congruence.
  - simpl in H1. destruct (n =? n1) eqn:P; destruct (n0 =? n1) eqn:P2.
    + inversion H1. 
    + congruence.
    + congruence.
    + inversion H1.
  - simpl in H1. destruct (n =? n1) eqn:P; destruct (n0 =? n1) eqn:P2.
    + apply Nat.eqb_eq in P. apply Nat.eqb_eq in P2. subst. reflexivity.
    + congruence.
    + congruence.
    + inversion H1. reflexivity.
  - inversion H1. apply IHphi1 in H3. apply IHphi2 in H4. subst. reflexivity.
    apply svar_is_fresh_in_app_r in H. assumption.
    apply svar_is_fresh_in_app_r in H0. assumption.
    apply svar_is_fresh_in_app_l in H. assumption.
    apply svar_is_fresh_in_app_l in H0. assumption.
  - inversion H1. apply IHphi1 in H3. apply IHphi2 in H4. subst. reflexivity.
    apply svar_is_fresh_in_imp_r in H. assumption.
    apply svar_is_fresh_in_imp_r in H0. assumption.
    apply svar_is_fresh_in_imp_l in H. assumption.
    apply svar_is_fresh_in_imp_l in H0. assumption.
  - inversion H1. apply IHphi in H3. subst. reflexivity.
    apply svar_is_fresh_in_exists in H. assumption.
    apply svar_is_fresh_in_exists in H0. assumption.
  - inversion H1. apply IHphi in H3. subst. reflexivity.
    apply svar_is_fresh_in_mu in H. assumption.
    apply svar_is_fresh_in_mu in H0. assumption.
Qed.

Lemma Private_evar_open_free_svar_subst_comm: ∀ sz phi psi fresh n X,
  (le (size phi) sz) → (well_formed_closed psi) → evar_is_fresh_in fresh phi →
  evar_is_fresh_in fresh (free_svar_subst phi psi X)
  →
  (evar_open n fresh (free_svar_subst phi psi X)) = (free_svar_subst (evar_open n fresh phi) psi X).
Proof.
  induction sz; destruct phi; intros psi fresh n0 X Hsz Hwf Hfresh1 Hfresh2; try inversion Hsz; auto.
  - simpl. destruct (ssrbool.is_left (svar_eqdec X x)) eqn:P.
    + rewrite -> evar_open_fresh. reflexivity. assumption.
    + simpl. reflexivity.
  - simpl. destruct (n =? n0) eqn:P.
    + reflexivity.
    + reflexivity.
  - simpl. rewrite -> IHsz; try lia; try assumption. rewrite -> IHsz; try lia; try assumption.
    reflexivity. apply (evar_is_fresh_in_app_r Hfresh1). simpl in Hfresh2.
    apply (evar_is_fresh_in_app_r Hfresh2). apply (evar_is_fresh_in_app_l Hfresh1).
    apply (evar_is_fresh_in_app_l Hfresh2).
  - simpl. rewrite -> IHsz; try lia; try assumption. rewrite -> IHsz; try lia; try assumption.
    reflexivity. apply (evar_is_fresh_in_imp_r Hfresh1).
    apply (evar_is_fresh_in_imp_r Hfresh2). apply (evar_is_fresh_in_imp_l Hfresh1).
    apply (evar_is_fresh_in_imp_l Hfresh2).
  - simpl. rewrite -> IHsz. reflexivity. lia. assumption.
    apply evar_is_fresh_in_exists in Hfresh1. assumption.
    simpl in Hfresh2. apply evar_is_fresh_in_exists in Hfresh1. assumption.
  - simpl. rewrite -> IHsz. reflexivity.
    lia. assumption. apply evar_is_fresh_in_mu in Hfresh1. assumption.
    simpl in Hfresh2. apply evar_is_fresh_in_mu in Hfresh2. assumption.
Qed.

Lemma evar_open_free_svar_subst_comm: ∀ phi psi fresh n X,
  (well_formed_closed psi) → evar_is_fresh_in fresh phi →
  evar_is_fresh_in fresh (free_svar_subst phi psi X)
  →
  (evar_open n fresh (free_svar_subst phi psi X)) = (free_svar_subst (evar_open n fresh phi) psi X).
Proof.
 intros. apply Private_evar_open_free_svar_subst_comm with (sz := (size phi)); try lia; try assumption.
Qed.

Lemma Private_svar_open_free_svar_subst_comm : ∀ sz phi psi fresh n X,
  (le (size phi) sz) → (well_formed_closed psi) (* → well_formed_closed (svar_open n fresh phi)  *)→  
  svar_is_fresh_in fresh phi → svar_is_fresh_in fresh (free_svar_subst phi psi X) → (fresh ≠ X) 
  →
  (svar_open n fresh (free_svar_subst phi psi X)) = 
  (free_svar_subst (svar_open n fresh phi) psi X).
Proof.
  induction sz; destruct phi; intros psi fresh n0 X Hsz Hwf (* Hwfc *) Hfresh1 Hfresh2 Hneq; try inversion Hsz; auto.
  - simpl. destruct (ssrbool.is_left (svar_eqdec X x)) eqn:P.
    + rewrite -> svar_open_fresh. reflexivity. assumption.
    + simpl. reflexivity.
  - (* simpl in Hwfc. *) simpl. destruct (n =? n0) eqn:P.
    + simpl. destruct (svar_eqdec X fresh) eqn:D.
      * rewrite -> e in Hneq. assert (fresh = fresh). reflexivity. contradiction.
      * reflexivity.
    + simpl. reflexivity.
  - simpl. (* simpl in Hwfc. apply wfc_wfc_ind in Hwfc. inversion Hwfc. *)
    rewrite -> IHsz; try lia; try assumption. rewrite -> IHsz; try lia; try assumption.
    reflexivity. (* apply wfc_ind_wfc. assumption. *)
    simpl in Hfresh1. apply svar_is_fresh_in_app_r in Hfresh1. assumption.
    simpl in Hfresh2. apply svar_is_fresh_in_app_r in Hfresh2. assumption.
    (*apply wfc_ind_wfc. assumption. *)
    simpl in Hfresh1. apply svar_is_fresh_in_app_l in Hfresh1. assumption.
    simpl in Hfresh2. apply svar_is_fresh_in_app_l in Hfresh2. assumption.
  - simpl. (*  simpl in Hwfc. apply wfc_wfc_ind in Hwfc. inversion Hwfc. *)
    rewrite -> IHsz; try lia; try assumption. rewrite -> IHsz; try lia; try assumption.
    reflexivity. 
    (* apply wfc_ind_wfc. assumption. *)
    simpl in Hfresh1. apply svar_is_fresh_in_app_r in Hfresh1. assumption.
    simpl in Hfresh2. apply svar_is_fresh_in_app_r in Hfresh2. assumption.
    (* apply wfc_ind_wfc. assumption. *)
    simpl in Hfresh1. apply svar_is_fresh_in_app_l in Hfresh1. assumption.
    simpl in Hfresh2. apply svar_is_fresh_in_app_l in Hfresh2. assumption.
  - remember ((free_evars (svar_open n0 fresh (free_svar_subst phi psi X))) ∪
      (free_evars (free_svar_subst (svar_open n0 fresh phi) psi X))) as B.
    simpl. remember (@evar_fresh (@variables signature) (elements B)) as x.
    assert(x ∉ B).
      {
        subst. apply set_evar_fresh_is_fresh'.
      }
      subst B.  apply not_elem_of_union in H. destruct H.
    (*magic happens*)
    erewrite (@evar_open_inj (svar_open n0 fresh (free_svar_subst phi psi X)) (free_svar_subst (svar_open n0 fresh phi) psi X) x 0 _ _ ).
    reflexivity.
    (*x needs to be fresh in ...*)
     rewrite -> IHsz. reflexivity. lia. assumption. simpl in Hfresh2. apply svar_is_fresh_in_exists in Hfresh1. assumption.
     apply svar_is_fresh_in_exists in Hfresh2. assumption. assumption.
  - remember ((free_svars (svar_open (S n0) fresh (free_svar_subst phi psi X)) ∪
      (free_svars (free_svar_subst (svar_open (S n0) fresh phi) psi X)))) as B.
    simpl. remember (@svar_fresh (@variables signature) (elements B)) as X'.
    assert(X' ∉ B).
      {
        subst. apply set_svar_fresh_is_fresh'.
      }
      subst B.  apply not_elem_of_union in H. destruct H.
    simpl.
    (*magic happens*)
    erewrite (@svar_open_inj (svar_open (S n0) fresh (free_svar_subst phi psi X)) (free_svar_subst (svar_open (S n0) fresh phi) psi X) X' 0 _ _ ).
    reflexivity.
    (*x needs to be fresh in ...*)
     rewrite -> IHsz. reflexivity. lia. assumption. simpl in Hfresh2. assumption. assumption. assumption.
     Unshelve.
     {
      unfold evar_is_fresh_in. assumption.
     }
     {
      unfold evar_is_fresh_in. assumption.
     }
     {
      unfold evar_is_fresh_in. assumption.
     }
     {
      unfold evar_is_fresh_in. assumption.
     }
Qed.

Lemma svar_open_free_svar_subst_comm : ∀ phi psi fresh n X,
  (well_formed_closed psi) (* → well_formed_closed (svar_open n fresh phi)  *)→  
  svar_is_fresh_in fresh phi → svar_is_fresh_in fresh (free_svar_subst phi psi X) → (fresh ≠ X) 
  →
  (svar_open n fresh (free_svar_subst phi psi X)) = 
  (free_svar_subst (svar_open n fresh phi) psi X).
Proof.
  intros. apply (Private_svar_open_free_svar_subst_comm) with (sz := (size phi)); try lia; try assumption.
Qed.

End syntax.

Hint Rewrite ->
     @evar_open_free_evar
     @evar_open_free_svar
     @evar_open_bound_evar
     @evar_open_bound_svar
     @evar_open_sym
     @evar_open_bott
     @evar_open_app
     @evar_open_imp
     @evar_open_exists
     @evar_open_mu

     @svar_open_free_evar
     @svar_open_free_svar
     @svar_open_bound_evar
     @svar_open_bound_svar
     @svar_open_sym
     @svar_open_bott
     @svar_open_app
     @svar_open_imp
     @svar_open_exists
     @svar_open_mu
  : ml_db.

Module Notations.
  Declare Scope ml_scope.
  Delimit Scope ml_scope with ml.
  (* TODO: change Bot and Top to unicode symbols *)
  Notation "a $ b" := (patt_app a b) (at level 65, right associativity) : ml_scope.
  Notation "'Bot'" := patt_bott : ml_scope.
  Notation "a ---> b"  := (patt_imp a b) (at level 90, right associativity,
                                         b at level 200) : ml_scope.
  Notation "'ex' , phi" := (patt_exists phi) (at level 70) : ml_scope.
  Notation "'mu' , phi" := (patt_mu phi) (at level 70) : ml_scope.

End Notations.

Module BoundVarSugar.
  (* Element variables - bound *)
  Notation b0 := (patt_bound_evar 0).
  Notation b1 := (patt_bound_evar 1).
  Notation b2 := (patt_bound_evar 2).
  Notation b3 := (patt_bound_evar 3).
  Notation b4 := (patt_bound_evar 4).
  Notation b5 := (patt_bound_evar 5).
  Notation b6 := (patt_bound_evar 6).
  Notation b7 := (patt_bound_evar 7).
  Notation b8 := (patt_bound_evar 8).
  Notation b9 := (patt_bound_evar 9).

  Notation B0 := (patt_bound_svar 0).
  Notation B1 := (patt_bound_svar 1).
  Notation B2 := (patt_bound_svar 2).
  Notation B3 := (patt_bound_svar 3).
  Notation B4 := (patt_bound_svar 4).
  Notation B5 := (patt_bound_svar 5).
  Notation B6 := (patt_bound_svar 6).
  Notation B7 := (patt_bound_svar 7).
  Notation B8 := (patt_bound_svar 8).
  Notation B9 := (patt_bound_svar 9).
  
End BoundVarSugar.

#[export]
 Hint Resolve
 evar_is_fresh_in_richer
set_evar_fresh_is_fresh
set_svar_fresh_is_fresh
x_eq_fresh_impl_x_notin_free_evars
  : core.

  Tactic Notation "solve_free_evars_inclusion" integer(depth) :=
    simpl;
    (do ! [rewrite simpl_free_evars/=]) ;
    apply elem_of_subseteq;
    let x := fresh "x" in
    let H := fresh "Hxin" in
    (* TODO: maybe we need something like: *)
    (*rewrite -!union_assoc_L.*)
    (* We may also want to remove duplicates, at least those that are neighbors *)
    intros x H;
    repeat (
        match H with
        | ?L /\ ?R => fail "Not implemented: destruct H"
        | _ => eauto depth using @sets.elem_of_union_l, @sets.elem_of_union_r with typeclass_instances
        end
      ).

  Tactic Notation "solve_free_svars_inclusion" integer(depth) :=
    simpl;
    (do ? [rewrite simpl_free_svars/=]) ;
    apply elem_of_subseteq;
    let x := fresh "x" in
    let H := fresh "Hxin" in
    (* TODO: maybe we need something like: *)
    (*rewrite -!union_assoc_L.*)
    (* We may also want to remove duplicates, at least those that are neighbors *)
    intros x H;
    repeat (
        match H with
        | ?L /\ ?R => fail "Not implemented: destruct H"
        | _ => eauto depth using @sets.elem_of_union_l, @sets.elem_of_union_r with typeclass_instances
        end
      ).
(*
        eauto 5 using @sets.elem_of_union_l, @sets.elem_of_union_r with typeclass_instances.
*)
  (*
  eauto depth using @sets.union_subseteq_l, @sets.union_subseteq_r
    with typeclass_instances.
*)

(*
#[export]
 Hint Extern 10 (free_evars _ ⊆ free_evars _) => solve_free_evars_inclusion : core.
*)

  (* assumes a goal `x₁ ≠ x₂` and a hypothesis of the shape `x₁ = fresh_evar ...`
     or `x₂ = fresh_evar ...`
  *)
  Ltac solve_fresh_neq :=
    repeat (
        match goal with
        | Heq: (eq ?x ?t) |- not (eq ?x ?y) =>
          pose proof (x_eq_fresh_impl_x_notin_free_evars Heq); clear Heq
        | Heq: (eq ?x ?t) |- not (eq ?y ?x) =>
          pose proof (x_eq_fresh_impl_x_notin_free_evars Heq); clear Heq
        end
      );
    (idtac + apply nesym);
    match goal with
    | H: not (elem_of ?x (free_evars ?phi)) |- not (eq ?x ?y) =>
      simpl in H;
      (do ! rewrite simpl_free_evars/= in H);
      rewrite -?union_assoc_L in H;
      repeat (
          match goal with
          | H: (not (elem_of ?x (singleton ?y))) |- _ =>
            apply stdpp_ext.not_elem_of_singleton_1 in H;
            first [ exact H | clear H]
          | H: (not (elem_of ?x (union ?l ?r))) |- _ => (apply not_elem_of_union in H; destruct H)
          end
        );
      fail
    end.

  Ltac remember_fresh_svars :=
    unfold fresh_svar in *;
    repeat(
        match goal with
        | |- context G [svar_fresh ?Y] =>
          match goal with
          | H: ?X = svar_fresh Y |- _ => fail 2
          | _ => remember (svar_fresh Y)
          end
        | H1: context G [svar_fresh ?Y] |- _ =>
          match goal with
          | H2: ?X = svar_fresh Y |- _ => fail 2
          | _ => remember (svar_fresh Y)
          end
        end
      ).

  Ltac solve_fresh_svar_neq :=
    subst; remember_fresh_svars;
    repeat (
        match goal with
        | Heq: (eq ?x ?t) |- not (eq ?x ?y) =>
          pose proof (X_eq_svar_fresh_impl_X_notin_S Heq); clear Heq
        | Heq: (eq ?x ?t) |- not (eq ?y ?x) =>
          pose proof (X_eq_svar_fresh_impl_X_notin_S Heq); clear Heq
        end
      );
    (idtac + apply nesym);
    match goal with
    | H: not (elem_of ?x ?S) |- not (eq ?x ?y) =>
      simpl in H;
      (do ? rewrite simpl_free_svars/= in H);
      rewrite -?union_assoc_L in H;
      repeat (
          match goal with
          | H: (not (elem_of ?x (singleton ?y))) |- _ =>
            apply stdpp_ext.not_elem_of_singleton_1 in H;
            first [ exact H | clear H]
          | H: (not (elem_of ?x (union ?l ?r))) |- _ => (apply not_elem_of_union in H; destruct H)
          end
        );
      fail
    end.
