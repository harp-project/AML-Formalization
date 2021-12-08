From Coq Require Import ssreflect ssrfun ssrbool.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import Setoid.
Require Import List.
Require Import Ensembles.
Require Import Coq.Strings.String.

From Coq Require Import Logic.Classical_Prop.
From stdpp Require Import countable infinite.
From stdpp Require Import pmap gmap mapset fin_sets propset.
Require Import stdpp_ext.

Require Import extralibrary.

Class MLVariables := {
  evar : Set;
  svar : Set;
  evar_eqdec :> EqDecision evar;
  evar_countable :> Countable evar;
  evar_infinite :> Infinite evar;
  svar_eqdec :> EqDecision svar;
  svar_countable :> Countable svar;
  svar_infinite :> Infinite svar;
}.

Class Signature := {
  variables :> MLVariables;
  symbols : Set;
  sym_eqdec :> EqDecision symbols;
}.

(* TODO have different type for element variable and for set variable index *)
Definition db_index := nat.

Inductive Pattern {Σ : Signature} : Set :=
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

Instance Pattern_eqdec {Σ : Signature} : EqDecision Pattern.
Proof. solve_decision. Defined.

Global Instance Pattern_countable {Σ : Signature} (sc : Countable symbols) : Countable Pattern.
Proof.
  set (enc :=
         fix go p : gen_tree (unit
                              + ((@symbols Σ)
                                 + (((@evar variables) + db_index)
                                    + ((@svar variables) + db_index))))%type :=
           match p with
           | patt_bott => GenLeaf (inl ())
           | patt_sym s => GenLeaf (inr (inl s))
           | patt_free_evar x => GenLeaf (inr (inr (inl (inl x))))
           | patt_free_svar X => GenLeaf (inr (inr (inr (inl X))))
           | patt_bound_evar n => GenLeaf (inr (inr (inl (inr n))))
           | patt_bound_svar n => GenLeaf (inr (inr (inr (inr n))))
           | patt_app p1 p2 => GenNode 0 [go p1; go p2]
           | patt_imp p1 p2 => GenNode 1 [go p1; go p2]
           | patt_exists p' => GenNode 2 [go p']
           | patt_mu p' => GenNode 3 [go p']
           end
      ).

  set (dec :=
         fix go (p : gen_tree (unit
                              + ((@symbols Σ)
                                 + (((@evar variables) + db_index)
                                    + ((@svar variables) + db_index))))%type) : Pattern :=
           match p with
           | GenLeaf (inl ()) => patt_bott
           | GenLeaf (inr (inl s)) => patt_sym s
           | GenLeaf (inr (inr (inl (inl x)))) => patt_free_evar x
           | GenLeaf (inr (inr (inr (inl X)))) => patt_free_svar X
           | GenLeaf (inr (inr (inl (inr n)))) => patt_bound_evar n
           | GenLeaf (inr (inr (inr (inr n)))) => patt_bound_svar n
           | GenNode 0 [p1; p2] => patt_app (go p1) (go p2)
           | GenNode 1 [p1; p2] => patt_imp (go p1) (go p2)
           | GenNode 2 [p'] => patt_exists (go p')
           | GenNode 3 [p'] => patt_mu (go p')
           | _ => patt_bott (* dummy *)
           end
      ).

  refine (inj_countable' enc dec _).
  intros x.
  induction x; simpl; congruence.
Defined.


Definition Theory {Σ : Signature} := propset Pattern.

Close Scope boolean_if_scope.

Section syntax.
  Context {Σ : Signature}.
  
  (* There are two substitution operations over patterns, [bevar_subst] and [bsvar_subst]. *)
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

     The function `bevar_subst` is also changed.
   *)
  Fixpoint bsvar_subst (phi psi : Pattern) (x : db_index) :=
    match phi with
    | patt_free_evar x' => patt_free_evar x'
    | patt_free_svar x' => patt_free_svar x'
    | patt_bound_evar n => patt_bound_evar n
    | patt_bound_svar n => match compare_nat n x with
                           | Nat_less _ _ _ => patt_bound_svar n
                           | Nat_equal _ _ _ => psi
                           | Nat_greater _ _ _ => patt_bound_svar (pred n)
                           end
    | patt_sym sigma => patt_sym sigma
    | patt_app phi1 phi2 => patt_app (bsvar_subst phi1 psi x)
                                     (bsvar_subst phi2 psi x)
    | patt_bott => patt_bott
    | patt_imp phi1 phi2 => patt_imp (bsvar_subst phi1 psi x) (bsvar_subst phi2 psi x)
    | patt_exists phi' => patt_exists (bsvar_subst phi' psi x)
    | patt_mu phi' => patt_mu (bsvar_subst phi' psi (S x))
    end.

  Notation "e .[ 'evar:' dbi ↦ e' ]" := (bevar_subst e e' dbi) (at level 2, e' at level 200, left associativity,
   format "e .[ 'evar:' dbi ↦ e' ]" ).
  Notation "e .[ 'svar:' dbi ↦ e' ]" := (bsvar_subst e e' dbi) (at level 2, e' at level 200, left associativity,
   format "e .[ 'svar:' dbi ↦ e' ]" ).

  Fixpoint bevar_occur (phi : Pattern) (x : db_index) : bool :=
    match phi with
    | patt_free_evar x' => false
    | patt_free_svar x' => false
    | patt_bound_evar n => if decide (n = x) is left _ then true else false
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
    | patt_bound_svar n => if (decide (n = x)) is left _ then true else false
    | patt_sym sigma => false
    | patt_app phi1 phi2 => orb (bsvar_occur phi1 x)
                                (bsvar_occur phi2 x)
    | patt_bott => false
    | patt_imp phi1 phi2 => orb (bsvar_occur phi1 x) (bsvar_occur phi2 x)
    | patt_exists phi' => bsvar_occur phi' x
    | patt_mu phi' => bsvar_occur phi' (S x)
    end.

(* TODO: deprecated, remove this
  Fixpoint nest_ex_aux level more ϕ {struct ϕ} : Pattern :=
    match ϕ with
    | patt_free_evar _ => ϕ
    | patt_free_svar _ => ϕ
    | patt_bound_evar n => patt_bound_evar (if decide (n < level) is left _ then n else n + more)
    | patt_bound_svar _ => ϕ
    | patt_sym _ => ϕ
    | patt_bott => ϕ
    | patt_app ϕ₁ ϕ₂ => patt_app (nest_ex_aux level more ϕ₁) (nest_ex_aux level more ϕ₂)
    | patt_imp ϕ₁ ϕ₂ => patt_imp (nest_ex_aux level more ϕ₁) (nest_ex_aux level more ϕ₂)
    | patt_exists ϕ' => patt_exists (nest_ex_aux (S level) more ϕ')
    | patt_mu ϕ' => patt_mu (nest_ex_aux level more ϕ')
    end.

  Fixpoint nest_mu_aux level more ϕ {struct ϕ} : Pattern :=
    match ϕ with
    | patt_free_evar _ => ϕ
    | patt_free_svar _ => ϕ
    | patt_bound_evar _ => ϕ
    | patt_bound_svar n => patt_bound_svar (if decide (n < level) is left _ then n else n + more)
    | patt_sym _ => ϕ
    | patt_bott => ϕ
    | patt_app ϕ₁ ϕ₂ => patt_app (nest_mu_aux level more ϕ₁) (nest_mu_aux level more ϕ₂)
    | patt_imp ϕ₁ ϕ₂ => patt_imp (nest_mu_aux level more ϕ₁) (nest_mu_aux level more ϕ₂)
    | patt_exists ϕ' => patt_exists (nest_mu_aux level more ϕ')
    | patt_mu ϕ' => patt_mu (nest_mu_aux (S level) more ϕ')
    end.
  
  Definition nest_ex ϕ := nest_ex_aux 0 1 ϕ.
  Definition nest_mu ϕ := nest_mu_aux 0 1 ϕ. *)
  
  (* substitute free element variable x for psi in phi *)
  Fixpoint free_evar_subst (phi psi : Pattern) (x : evar) :=
    match phi with
    | patt_free_evar x' => if decide (x = x') is left _ then psi else patt_free_evar x'
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

  (* substitute free set variable X for psi in phi *)
  Fixpoint free_svar_subst (phi psi : Pattern) (X : svar) : Pattern :=
    match phi with
    | patt_free_evar x => patt_free_evar x
    | patt_free_svar X' => if decide (X = X') is left _ then psi else patt_free_svar X'
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

  Notation "e .[[ 'evar:' x ↦ e' ]]" := (free_evar_subst e e' x) (at level 2, e' at level 200, left associativity,
   format "e .[[ 'evar:' x ↦ e' ]]" ).
  Notation "e .[[ 'svar:' X ↦ e' ]]" := (free_svar_subst e e' X) (at level 2, e' at level 200, left associativity,
   format "e .[[ 'svar:' X ↦ e' ]]" ).
  Notation "e . [ e' ]" := (instantiate e e') (at level 2, e' at level 200, left associativity).

  (** The free names of a type are defined as follow.  Notice the
  [exists] and [mu] cases: they do not bind any name. *)

  Definition EVarSet := gset evar.
  Definition SVarSet := gset svar.

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

  (* replace element variable x with de Bruijn index level *)
  Fixpoint evar_quantify (x : evar) (level : db_index)
           (p : Pattern) : Pattern :=
    match p with
    | patt_free_evar x' => if decide (x = x') is left _ then patt_bound_evar level else patt_free_evar x'
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

  (* replace set variable X with de Bruijn index level *)
  Fixpoint svar_quantify (X : svar) (level : db_index)
           (p : Pattern) : Pattern :=
    match p with
    | patt_free_evar x' => patt_free_evar x'
    | patt_free_svar X' => if decide (X = X') is left _ then patt_bound_svar level else patt_free_svar X'
    | patt_bound_evar x' => patt_bound_evar x'
    | patt_bound_svar X => patt_bound_svar X
    | patt_sym s => patt_sym s
    | patt_app ls rs => patt_app (svar_quantify X level ls) (svar_quantify X level rs)
    | patt_bott => patt_bott
    | patt_imp ls rs => patt_imp (svar_quantify X level ls) (svar_quantify X level rs)
    | patt_exists p' => patt_exists (svar_quantify X level p')
    | patt_mu p' => patt_mu (svar_quantify X (S level) p')
    end.

  Inductive PatCtx : Type :=
  | pctx_box
  | pctx_app_l (C : PatCtx) (r : Pattern)
  | pctx_app_r (l : Pattern) (C : PatCtx)
  | pctx_imp_l (C : PatCtx) (r : Pattern)
  | pctx_imp_r (l : Pattern) (C : PatCtx)
  | pctx_exists (x : evar) (C : PatCtx)
  (* | ctx_mu (C : PatCtx) <--- restriction *).

  Definition exists_quantify (x : evar)
             (p : Pattern) : Pattern :=
    patt_exists (evar_quantify x 0 p).

  Definition mu_quantify (X : svar)
             (p : Pattern) : Pattern :=
    patt_mu (svar_quantify X 0 p).

  Fixpoint subst_patctx (C : PatCtx) (p : Pattern) : Pattern :=
  match C with
   | pctx_box => p
   | pctx_app_l C r => patt_app (subst_patctx C p) r
   | pctx_app_r l C => patt_app l (subst_patctx C p)
   | pctx_imp_l C r => patt_imp (subst_patctx C p) r
   | pctx_imp_r l C => patt_imp l (subst_patctx C p)
   | pctx_exists x C => exists_quantify x (subst_patctx C p)
   (* | ctx_mu C => patt_mu (subst_patctx C p) *)
  end.

  Fixpoint size (p : Pattern) : nat :=
    match p with
    | patt_app ls rs => 1 + (size ls) + (size rs)
    | patt_imp ls rs => 1 + (size ls) + (size rs)
    | patt_exists p' => 1 + size p'
    | patt_mu p' => 1 + size p'
    | _ => 0
    end.


  Fixpoint size' (p : Pattern) : nat :=
    match p with
    | patt_app ls rs => 1 + (size' ls) + (size' rs)
    | patt_imp ls rs => 1 + (size' ls) + (size' rs)
    | patt_exists p' => 1 + size' p'
    | patt_mu p' => 1 + size' p'
    | _ => 1
    end.
  
  (* replace de Bruijn index k with element variable n *)
  Definition evar_open (k : db_index) (x : evar) (p : Pattern) : Pattern :=
    bevar_subst p (patt_free_evar x) k.


  (* replace de Bruijn index k with set variable n *)
  Definition svar_open (k : db_index) (X : svar) (p : Pattern) : Pattern :=
    bsvar_subst p (patt_free_svar X) k.

  Lemma evar_open_free_evar k n x: evar_open k n (patt_free_evar x) = patt_free_evar x.
  Proof. reflexivity. Qed.
  Lemma evar_open_free_svar k n X: evar_open k n (patt_free_svar X) = patt_free_svar X.
  Proof. reflexivity. Qed.
  Lemma evar_open_bound_evar k n x: evar_open k n (patt_bound_evar x) = 
                           match compare_nat x k with
                           | Nat_less _ _ _ => patt_bound_evar x
                           | Nat_equal _ _ _ => patt_free_evar n
                           | Nat_greater _ _ _ => patt_bound_evar (pred x)
                           end.
  Proof.
    cbn. case_match; done.
  Qed.
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

  (* More trivial but useful lemmas *)
  Lemma svar_open_free_evar k n x: svar_open k n (patt_free_evar x) = patt_free_evar x.
  Proof. reflexivity. Qed.
  Lemma svar_open_free_svar k n X: svar_open k n (patt_free_svar X) = patt_free_svar X.
  Proof. reflexivity. Qed.
  Lemma svar_open_bound_evar k n x: svar_open k n (patt_bound_evar x) = patt_bound_evar x.
  Proof. reflexivity. Qed.
  Lemma svar_open_bound_svar k n X: svar_open k n (patt_bound_svar X) = 
                                    match compare_nat X k with
                                    | Nat_less _ _ _ => patt_bound_svar X
                                    | Nat_equal _ _ _ => patt_free_svar n
                                    | Nat_greater _ _ _ => patt_bound_svar (pred X)
                                    end.
  Proof.
    reflexivity.
  Qed.
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


  Lemma evar_open_size :
    forall (k : db_index) (n : evar) (p : Pattern),
      size p = size (evar_open k n p).
  Proof.
    intros k n p. generalize dependent k.
    induction p; intros k; cbn; try reflexivity.
    break_match_goal; reflexivity.
    rewrite (IHp1 k); rewrite (IHp2 k); reflexivity.
    rewrite (IHp1 k); rewrite (IHp2 k); reflexivity.
    rewrite (IHp (S k)); reflexivity.
    rewrite (IHp k); reflexivity.
  Qed.

  Lemma svar_open_size :
    forall (k : db_index) (n : svar) (p : Pattern),
      size p = size (svar_open k n p).
  Proof.
    intros k n p. generalize dependent k.
    induction p; intros k; cbn; try reflexivity.
    break_match_goal; reflexivity.
    rewrite (IHp1 k); rewrite (IHp2 k); reflexivity.
    rewrite (IHp1 k); rewrite (IHp2 k); reflexivity.
    rewrite (IHp k); reflexivity.
    rewrite (IHp (S k)); reflexivity.
  Qed.

(*  TODO: deprecated

 (* set variable occurs positively in pattern *)

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
  . *)

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
    | patt_bound_svar n => if decide (n = dbi) is left _ then false else true
    | patt_app ϕ₁ ϕ₂ => no_positive_occurrence_db_b dbi ϕ₁ && no_positive_occurrence_db_b dbi ϕ₂
    | patt_imp ϕ₁ ϕ₂ => no_negative_occurrence_db_b dbi ϕ₁ && no_positive_occurrence_db_b dbi ϕ₂
    | patt_exists ϕ' => no_positive_occurrence_db_b dbi ϕ'
    | patt_mu ϕ' => no_positive_occurrence_db_b (S dbi) ϕ'                                  
    end.

  (* for free element variables *)
  Fixpoint evar_has_positive_occurrence (x : evar) (ϕ : Pattern) : bool :=
    match ϕ with
    | patt_free_evar x' => if decide (x = x') is left _ then true else false
    | patt_free_svar _ | patt_bound_evar _ | patt_bound_svar _ | patt_sym _ | patt_bott => false
    | patt_app ϕ₁ ϕ₂ => evar_has_positive_occurrence x ϕ₁ || evar_has_positive_occurrence x ϕ₂
    | patt_imp ϕ₁ ϕ₂ => evar_has_negative_occurrence x ϕ₁ || evar_has_positive_occurrence x ϕ₂
    | patt_exists ϕ' => evar_has_positive_occurrence x ϕ'
    | patt_mu ϕ' => evar_has_positive_occurrence x ϕ'
    end
  with
  evar_has_negative_occurrence (x : evar) (ϕ : Pattern) : bool :=
    match ϕ with
    | patt_free_evar _ | patt_free_svar _ | patt_bound_evar _ | patt_bound_svar _ | patt_sym _ | patt_bott => false
    | patt_app ϕ₁ ϕ₂ => evar_has_negative_occurrence x ϕ₁ || evar_has_negative_occurrence x ϕ₂
    | patt_imp ϕ₁ ϕ₂ => evar_has_positive_occurrence x ϕ₁ || evar_has_negative_occurrence x ϕ₂
    | patt_exists ϕ' => evar_has_negative_occurrence x ϕ'
    | patt_mu ϕ' => evar_has_negative_occurrence x ϕ'
    end.

  (* for free set variables *)
  Fixpoint svar_has_positive_occurrence (X : svar) (ϕ : Pattern) : bool :=
    match ϕ with
    | patt_free_svar X' => if decide (X = X') is left _ then true else false
    | patt_free_evar _ | patt_bound_evar _ | patt_bound_svar _ | patt_sym _ | patt_bott => false
    | patt_app ϕ₁ ϕ₂ => svar_has_positive_occurrence X ϕ₁ || svar_has_positive_occurrence X ϕ₂
    | patt_imp ϕ₁ ϕ₂ => svar_has_negative_occurrence X ϕ₁ || svar_has_positive_occurrence X ϕ₂
    | patt_exists ϕ' => svar_has_positive_occurrence X ϕ'
    | patt_mu ϕ' => svar_has_positive_occurrence X ϕ'
    end
  with
  svar_has_negative_occurrence (X : svar) (ϕ : Pattern) : bool :=
    match ϕ with
    | patt_free_evar _ | patt_free_svar _ | patt_bound_evar _ | patt_bound_svar _ | patt_sym _ | patt_bott => false
    | patt_app ϕ₁ ϕ₂ => svar_has_negative_occurrence X ϕ₁ || svar_has_negative_occurrence X ϕ₂
    | patt_imp ϕ₁ ϕ₂ => svar_has_positive_occurrence X ϕ₁ || svar_has_negative_occurrence X ϕ₂
    | patt_exists ϕ' => svar_has_negative_occurrence X ϕ'
    | patt_mu ϕ' => svar_has_negative_occurrence X ϕ'
    end.
  
(* TODO: deprecated

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
    1: { case_match; simpl.
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
    induction phi; intros db1 db2 x'; cbn; split; try constructor; try inversion H; subst; try firstorder.
    * break_match_goal; intros; constructor.
    * break_match_goal; intros; constructor.
  Qed.

  Lemma positive_occurrence_db_evar_open : forall (phi : Pattern) (db1 db2 : db_index) (x : evar),
      positive_occurrence_db db1 phi -> positive_occurrence_db db1 (evar_open db2 x phi).
  Proof.
    intros phi db1 db2 x H.
    pose proof (H' := positive_negative_occurrence_db_evar_open phi db1 db2 x).
    firstorder.
  Qed.

  Lemma negative_occurrence_db_evar_open : forall (phi : Pattern) (db1 db2 : db_index) (x : evar),
      negative_occurrence_db db1 phi -> negative_occurrence_db db1 (evar_open db2 x phi).
  Proof.
    intros phi db1 db2 x H.
    pose proof (H' := positive_negative_occurrence_db_evar_open phi db1 db2 x).
    firstorder.
  Qed. *)

  Lemma positive_negative_occurrence_evar_open_and : forall (phi : Pattern) (db1 db2 : db_index) (x : evar),
      (*le db1 db2 ->*)
      (no_positive_occurrence_db_b db1 phi -> no_positive_occurrence_db_b db1 (evar_open db2 x phi))
      /\ (no_negative_occurrence_db_b db1 phi -> no_negative_occurrence_db_b db1 (evar_open db2 x phi)).
  Proof.
    induction phi; intros db1 db2 x'; cbn; split; intro H; try lia; auto.
    * case_match; auto.
    * case_match; auto.
    * rewrite -> (proj1 (IHphi1 db1 db2 x')), -> (proj1 (IHphi2 db1 db2 x')); destruct_and!; auto.
    * rewrite -> (proj2 (IHphi1 db1 db2 x')), -> (proj2 (IHphi2 db1 db2 x')); destruct_and!; auto.
    * rewrite -> (proj2 (IHphi1 db1 db2 x')), -> (proj1 (IHphi2 db1 db2 x')); destruct_and!; auto.
    * rewrite -> (proj1 (IHphi1 db1 db2 x')), -> (proj2 (IHphi2 db1 db2 x')); destruct_and!; auto.
    * rewrite -> (proj1 (IHphi db1 (S db2) x')); auto.
    * rewrite -> (proj2 (IHphi db1 (S db2) x')); auto.
    * rewrite -> (proj1 (IHphi (S db1) db2 x')); auto.
    * rewrite -> (proj2 (IHphi (S db1) db2 x')); auto.
  Qed.

  Lemma no_negative_occurrence_evar_open phi db1 db2 x:
    no_negative_occurrence_db_b db1 phi = true ->
    no_negative_occurrence_db_b db1 (evar_open db2 x phi) = true.
  Proof.
    apply positive_negative_occurrence_evar_open_and.
  Qed.

  Lemma no_positive_occurrence_evar_open phi db1 db2 x:
    no_positive_occurrence_db_b db1 phi = true ->
    no_positive_occurrence_db_b db1 (evar_open db2 x phi) = true.
  Proof.
    apply positive_negative_occurrence_evar_open_and.
  Qed.

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
  
  Fixpoint well_formed_closed_mu_aux (phi : Pattern) (max_ind_svar : db_index) : bool :=
    match phi with
    | patt_free_evar _ => true
    | patt_free_svar _ => true
    | patt_bound_evar n => true
    | patt_bound_svar n => if decide (n < max_ind_svar) is left _ then true else false
    | patt_sym _ => true
    | patt_app psi1 psi2 => well_formed_closed_mu_aux psi1 max_ind_svar &&
                            well_formed_closed_mu_aux psi2 max_ind_svar
    | patt_bott => true
    | patt_imp psi1 psi2 => well_formed_closed_mu_aux psi1 max_ind_svar &&
                            well_formed_closed_mu_aux psi2 max_ind_svar
    | patt_exists psi => well_formed_closed_mu_aux psi max_ind_svar
    | patt_mu psi => well_formed_closed_mu_aux psi (S max_ind_svar)
    end.

  Fixpoint well_formed_closed_ex_aux (phi : Pattern) (max_ind_evar : db_index) : bool :=
    match phi with
    | patt_free_evar _ => true
    | patt_free_svar _ => true
    | patt_bound_evar n => if decide (n < max_ind_evar) is left _ then true else false
    | patt_bound_svar n => true
    | patt_sym _ => true
    | patt_app psi1 psi2 => well_formed_closed_ex_aux psi1 max_ind_evar &&
                            well_formed_closed_ex_aux psi2 max_ind_evar
    | patt_bott => true
    | patt_imp psi1 psi2 => well_formed_closed_ex_aux psi1 max_ind_evar &&
                            well_formed_closed_ex_aux psi2 max_ind_evar
    | patt_exists psi => well_formed_closed_ex_aux psi (S max_ind_evar)
    | patt_mu psi => well_formed_closed_ex_aux psi max_ind_evar
    end.
  
  Definition well_formed_closed (phi : Pattern) : bool
    := well_formed_closed_mu_aux phi 0 && well_formed_closed_ex_aux phi 0.

  (* bevar_subst is identity if n does not occur in phi *)
  Lemma bevar_subst_not_occur n ψ ϕ :
    well_formed_closed_ex_aux ϕ n ->
    bevar_subst ϕ ψ n = ϕ.
  Proof.
    generalize dependent n.
    induction ϕ; simpl; intros dbi H; auto.
    - case_match. 2: done. case_match; try done; lia.
    - apply andb_true_iff in H as [H1 H2].
      rewrite -> IHϕ1 by auto.
      now rewrite -> IHϕ2 by auto.
    - apply andb_true_iff in H as [H1 H2].
      rewrite -> IHϕ1 by auto.
      now rewrite -> IHϕ2 by auto.
    - rewrite -> IHϕ. 2: { assumption.  } reflexivity.
    - rewrite -> IHϕ by auto. auto.
  Qed.

  (* evar_open is identity if n does not occur in phi *)
  Lemma evar_open_not_occur n x ϕ :
    well_formed_closed_ex_aux ϕ n ->
    evar_open n x ϕ = ϕ.
  Proof.
    apply bevar_subst_not_occur.
  Qed.


  Lemma well_formed_closed_ex_aux_ind (phi : Pattern) (ind_evar1 ind_evar2 : db_index) :
    ind_evar1 <= ind_evar2 ->
    well_formed_closed_ex_aux phi ind_evar1 = true->
    well_formed_closed_ex_aux phi ind_evar2 = true.
  Proof.
    intros H H0.
    generalize dependent ind_evar1. generalize dependent ind_evar2.
    induction phi; intros ind_evar_2 ind_evar_1 Heqevar H;
      simpl in *; repeat case_match; try (naive_bsolver lia); auto.
    eapply IHphi. 2: eassumption. lia.
  Qed.

  Lemma well_formed_closed_mu_aux_ind (phi : Pattern) (ind_svar1 ind_svar2 : db_index) :
    ind_svar1 <= ind_svar2  ->
    well_formed_closed_mu_aux phi ind_svar1 = true ->
    well_formed_closed_mu_aux phi ind_svar2 = true.
  Proof.
    intros H H1.
    generalize dependent ind_svar1. generalize dependent ind_svar2.
    induction phi; intros ind_svar_2 ind_svar_1 Hleqsvar;
      simpl in *; repeat case_match; try (naive_bsolver lia); auto.
    eapply IHphi. lia.
  Qed.
  
  Definition well_formed (phi : Pattern) := well_formed_positive phi && well_formed_closed phi.

  (* From https://www.chargueraud.org/research/2009/ln/main.pdf in 3.3 (body def.) *)
  Definition wfc_body_ex phi  := forall x, 
      ~ elem_of x (free_evars phi) -> well_formed_closed (evar_open 0 x phi) = true.

  (*Helper lemma for wf_body_to_wf_ex*)
  Lemma wfc_ex_aux_body_ex_imp2:
    forall phi n x,
      well_formed_closed_ex_aux (evar_open n x phi) n = true
      ->
      well_formed_closed_ex_aux phi (S n) = true.
  Proof using .
    induction phi; firstorder.
    - simpl. cbn in H. unfold well_formed_closed_ex_aux.
      repeat case_match; simpl; auto; try lia.
      unfold well_formed_closed_ex_aux in H. case_match; auto. lia.
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

  (*Helper lemma for wf_body_to_wf_ex*)
  Lemma wfc_mu_aux_body_ex_imp2:
    forall phi n n' x,
      well_formed_closed_mu_aux (evar_open n x phi) n' = true
      ->
      well_formed_closed_mu_aux phi n' = true.
  Proof using .
    induction phi; firstorder.
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

  Lemma wfc_ex_aux_body_mu_imp2:
    forall phi n n' X,
      well_formed_closed_ex_aux (svar_open n X phi) n' = true
      ->
      well_formed_closed_ex_aux phi n' = true.
  Proof using .
    induction phi; firstorder.
    - simpl in H. simpl.
      destruct_and!.
      erewrite IHphi1. 2: eassumption.
      erewrite IHphi2. 2: eassumption.
      reflexivity.
    - simpl in H. simpl.
      destruct_and!.
      erewrite IHphi1. 2: eassumption.
      erewrite IHphi2. 2: eassumption.
      reflexivity.
  Qed.
  
  Lemma wfc_mu_aux_body_mu_imp2:
    forall phi n X,
      well_formed_closed_mu_aux (svar_open n X phi) n = true
      ->
      well_formed_closed_mu_aux phi (S n) = true.
  Proof using .
    induction phi; firstorder.
    - simpl. cbn in H. unfold well_formed_closed_mu_aux.
      repeat case_match; simpl; auto; try lia.
      unfold well_formed_closed_mu_aux in H. case_match; auto. lia.
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


  (* The following lemmas are trivial but useful for [rewrite !simpl_evar_open]. *)

  Lemma bevar_subst_free_evar ψ (pf : well_formed_closed ψ) n x :
    bevar_subst (patt_free_evar x) ψ n = patt_free_evar x.
  Proof. reflexivity. Qed.

  Lemma bevar_subst_free_svar ψ (pf : well_formed_closed ψ) n X :
    bevar_subst (patt_free_svar X) ψ n = patt_free_svar X.
  Proof. reflexivity. Qed.

  Lemma bevar_subst_bound_evar ψ (pf : well_formed_closed ψ) n x :
    bevar_subst (patt_bound_evar x) ψ n = match compare_nat x n with
                                          | Nat_less _ _ _ => patt_bound_evar x
                                          | Nat_equal _ _ _ => ψ
                                          | Nat_greater _ _ _ => patt_bound_evar (pred x)
                                          end.
  Proof.
    cbn. case_match; done.
  Qed.

  Lemma bevar_subst_bound_svar ψ (pf : well_formed_closed ψ) n X :
    bevar_subst (patt_bound_svar X) ψ n = patt_bound_svar X.
  Proof. reflexivity. Qed.

  Lemma bevar_subst_sym ψ (pf : well_formed_closed ψ) n s :
    bevar_subst (patt_sym s) ψ n = patt_sym s.
  Proof. reflexivity. Qed.

  Lemma bevar_subst_app ψ (pf : well_formed_closed ψ) n ls rs :
    bevar_subst (patt_app ls rs) ψ n = patt_app (bevar_subst ls ψ n) (bevar_subst rs ψ n).
  Proof. reflexivity. Qed.

  Lemma bevar_subst_bott ψ (pf : well_formed_closed ψ) n:
    bevar_subst patt_bott ψ n = patt_bott.
  Proof. reflexivity. Qed.

  Lemma bevar_subst_imp ψ (pf : well_formed_closed ψ) n ls rs :
    bevar_subst (patt_imp ls rs) ψ n = patt_imp (bevar_subst ls ψ n) (bevar_subst rs ψ n).
  Proof. reflexivity. Qed.

  Lemma bevar_subst_exists ψ (pf : well_formed_closed ψ) n ϕ :
    bevar_subst (patt_exists ϕ) ψ n = patt_exists (bevar_subst ϕ ψ (S n)).
  Proof. reflexivity. Qed.

  Lemma bevar_subst_mu ψ (pf : well_formed_closed ψ) n ϕ :
    bevar_subst (patt_mu ϕ) ψ n = patt_mu (bevar_subst ϕ ψ n).
  Proof. reflexivity. Qed.

  (* More trivial but useful lemmas *)
  Lemma bsvar_subst_free_evar ψ (pf : well_formed_closed ψ) n x :
    bsvar_subst (patt_free_evar x) ψ n = patt_free_evar x.
  Proof. reflexivity. Qed.

  Lemma bsvar_subst_free_svar ψ (pf : well_formed_closed ψ) n X :
    bsvar_subst (patt_free_svar X) ψ n = patt_free_svar X.
  Proof. reflexivity. Qed.

  Lemma bsvar_subst_bound_evar ψ (pf : well_formed_closed ψ) n x :
    bsvar_subst (patt_bound_evar x) ψ n = patt_bound_evar x.
  Proof. reflexivity. Qed.

  Lemma bsvar_subst_bound_svar ψ (pf : well_formed_closed ψ) n X :
    bsvar_subst (patt_bound_svar X) ψ n = match compare_nat X n with
                                          | Nat_less _ _ _ => patt_bound_svar X
                                          | Nat_equal _ _ _ => ψ
                                          | Nat_greater _ _ _ => patt_bound_svar (pred X)
                                          end.
  Proof.
    reflexivity.
  Qed.

  Lemma bsvar_subst_sym ψ (pf : well_formed_closed ψ) n s :
    bsvar_subst (patt_sym s) ψ n = patt_sym s.
  Proof. reflexivity. Qed.

  Lemma bsvar_subst_app ψ (pf : well_formed_closed ψ) n ls rs :
    bsvar_subst (patt_app ls rs) ψ n = patt_app (bsvar_subst ls ψ n) (bsvar_subst rs ψ n).
  Proof. reflexivity. Qed.

  Lemma bsvar_subst_bott ψ (pf : well_formed_closed ψ) n :
    bsvar_subst patt_bott ψ n = patt_bott.
  Proof. reflexivity. Qed.

  Lemma bsvar_subst_imp ψ (pf : well_formed_closed ψ) n ls rs:
    bsvar_subst (patt_imp ls rs) ψ n = patt_imp (bsvar_subst ls ψ n) (bsvar_subst rs ψ n).
  Proof. reflexivity. Qed.

  Lemma bsvar_subst_exists ψ (pf : well_formed_closed ψ) n ϕ :
    bsvar_subst (patt_exists ϕ) ψ n = patt_exists (bsvar_subst ϕ ψ n).
  Proof. reflexivity. Qed.

  Lemma bsvar_subst_mu ψ (pf : well_formed_closed ψ) n ϕ :
    bsvar_subst (patt_mu ϕ) ψ n = patt_mu (bsvar_subst ϕ ψ (S n)).
  Proof. reflexivity. Qed.



  Class EBinder (ebinder : Pattern -> Pattern)
        (fevo: db_index -> Pattern -> Pattern -> Pattern )
        (fsvo: db_index -> Pattern -> Pattern -> Pattern ) :=
    {
    ebinder_bevar_subst :
      forall ψ,
        well_formed_closed ψ ->
        forall n ϕ,
          bevar_subst (ebinder ϕ) ψ n = fevo n ψ ϕ ;
    ebinder_bsvar_subst :
      forall ψ,
        well_formed_closed ψ ->
        forall n ϕ,
          bsvar_subst (ebinder ϕ) ψ n = fsvo n ψ ϕ ;
    }.

  Class SBinder (sbinder : Pattern -> Pattern) :=
    {
    sbinder_bevar_subst :
      forall ψ,
        well_formed_closed ψ ->
        forall n ϕ,
          bevar_subst (sbinder ϕ) ψ n = sbinder (bevar_subst ϕ ψ n) ;
    sbinder_bsvar_subst :
      forall ψ,
        well_formed_closed ψ ->
        forall n ϕ,
          bsvar_subst (sbinder ϕ) ψ n = sbinder (bsvar_subst ϕ ψ (S n)) ;
    }.

  (* Non-variable nullary operation *)
  Class NVNullary (nvnullary : Pattern) :=
    {
    nvnullary_bevar_subst :
      forall ψ,
        well_formed_closed ψ ->
        forall n,
          bevar_subst nvnullary ψ n = nvnullary ;
    nvnullary_bsvar_subst :
      forall ψ,
        well_formed_closed ψ ->
        forall n,
          bevar_subst nvnullary ψ n = nvnullary ;
    }.

  Class Unary (patt : Pattern -> Pattern) :=
    {
    unary_bevar_subst :
      forall ψ,
        well_formed_closed ψ ->
        forall n ϕ,
          bevar_subst (patt ϕ) ψ n = patt (bevar_subst ϕ ψ n) ;
    unary_bsvar_subst :
      forall ψ,
        well_formed_closed ψ ->
        forall n ϕ,
          bsvar_subst (patt ϕ) ψ n = patt (bsvar_subst ϕ ψ n) ;
    }.

  Class Binary (binary : Pattern -> Pattern -> Pattern) :=
    {
    binary_bevar_subst :
      forall ψ,
        well_formed_closed ψ ->
        forall n ϕ₁ ϕ₂,
          bevar_subst (binary ϕ₁ ϕ₂) ψ n = binary (bevar_subst ϕ₁ ψ n) (bevar_subst ϕ₂ ψ n) ;
    binary_bsvar_subst :
      forall ψ,
        well_formed_closed ψ ->
        forall n ϕ₁ ϕ₂,
          bsvar_subst (binary ϕ₁ ϕ₂) ψ n = binary (bsvar_subst ϕ₁ ψ n) (bsvar_subst ϕ₂ ψ n) ;
    }.

  Definition simpl_bevar_subst' :=
    (@ebinder_bevar_subst,
     @sbinder_bevar_subst,
     @nvnullary_bevar_subst,
     @unary_bevar_subst,
     @binary_bevar_subst
    ).

  Definition simpl_bsvar_subst' :=
    (@ebinder_bsvar_subst,
     @sbinder_bsvar_subst,
     @nvnullary_bsvar_subst,
     @unary_bsvar_subst,
     @binary_bsvar_subst
    ).

  #[global]
   Instance EBinder_exists : EBinder patt_exists _ _ :=
    {|
    ebinder_bevar_subst := bevar_subst_exists ;
    ebinder_bsvar_subst := bsvar_subst_exists ;
    |}.

  #[global]
   Instance SBinder_mu : SBinder patt_mu :=
    {|
    sbinder_bevar_subst := bevar_subst_mu ;
    sbinder_bsvar_subst := bsvar_subst_mu ;
    |}.


  #[global]
   Instance NVNullary_bott : NVNullary patt_bott :=
    {|
    nvnullary_bevar_subst := bevar_subst_bott ;
    nvnullary_bsvar_subst := bsvar_subst_bott ;
    |}.

  #[global]
   Instance NVNullary_sym s : NVNullary (patt_sym s) :=
    {|
    nvnullary_bevar_subst := λ ψ (wfcψ : well_formed_closed ψ) n, @bevar_subst_sym ψ wfcψ n s ;
    nvnullary_bsvar_subst := λ ψ (wfcψ : well_formed_closed ψ) n, @bsvar_subst_sym ψ wfcψ n s;
    |}.

  #[global]
   Instance Binary_app : Binary patt_app :=
    {|
    binary_bevar_subst := bevar_subst_app ;
    binary_bsvar_subst := bsvar_subst_app ;
    |}.

  #[global]
   Instance Binary_imp : Binary patt_imp :=
    {|
    binary_bevar_subst := bevar_subst_imp ;
    binary_bsvar_subst := bsvar_subst_imp ;
    |}.



  Lemma well_formed_bott:
    well_formed patt_bott.
  Proof.
    unfold well_formed. simpl.
    unfold well_formed_closed. simpl.
    reflexivity.
  Qed.

  Lemma well_formed_imp ϕ₁ ϕ₂:
    well_formed ϕ₁ = true ->
    well_formed ϕ₂ = true ->
    well_formed (patt_imp ϕ₁ ϕ₂) = true.
  Proof.
    unfold well_formed. unfold well_formed_closed. simpl.
    intros H1 H2.
    destruct_and!.
    split_and!; auto.
  Qed.

  Lemma well_formed_app ϕ₁ ϕ₂:
    well_formed ϕ₁ = true ->
    well_formed ϕ₂ = true ->
    well_formed (patt_app ϕ₁ ϕ₂) = true.
  Proof.
    unfold well_formed,well_formed_closed.
    naive_bsolver.
  Qed.

  Lemma well_formed_ex_app ϕ₁ ϕ₂:
    well_formed (patt_exists ϕ₁) = true ->
    well_formed (patt_exists ϕ₂) = true ->
    well_formed (patt_exists (patt_app ϕ₁ ϕ₂)) = true.
  Proof.
    unfold well_formed,well_formed_closed.
    naive_bsolver.
  Qed.

  Lemma well_formed_impl_well_formed_ex ϕ:
    well_formed ϕ = true ->
    well_formed (patt_exists ϕ) = true.
  Proof.
    unfold well_formed,well_formed_closed.
    intros. destruct_and!. split_and!; auto.
    eapply well_formed_closed_ex_aux_ind in H2. simpl. eassumption. lia.
  Qed.

  (* fresh variables *)
  
  Definition evar_fresh (l : list evar) : evar := fresh l.
  Definition svar_fresh (l : list svar) : svar := fresh l.
  
  Definition fresh_evar ϕ := evar_fresh (elements (free_evars ϕ)).
  Definition fresh_svar ϕ := svar_fresh (elements (free_svars ϕ)).

  Definition evar_is_fresh_in x ϕ := x ∉ free_evars ϕ.
  Definition svar_is_fresh_in x ϕ := x ∉ free_svars ϕ.

  (* Lemmas about fresh variables *)

  Lemma set_evar_fresh_is_fresh' (S : EVarSet) : evar_fresh (elements S) ∉ S.
  Proof.
    intros H.
    pose proof (Hf := @infinite_is_fresh _ evar_infinite (elements S)).
    unfold elements in H. unfold gset_elements in H.
    apply gset_to_list_elem_of in H.
    unfold elements in Hf. unfold gset_elements in Hf.
    unfold evar_fresh in H. unfold fresh in Hf. contradiction.
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
    pose proof (Hf := @infinite_is_fresh _ svar_infinite (elements S)).
    unfold elements in H. unfold gset_elements in H.
    apply gset_to_list_elem_of in H.
    unfold elements in Hf. unfold gset_elements in Hf.
    unfold evar_fresh in H. unfold fresh in Hf. contradiction.
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
    eauto using not_elem_of_larger_impl_not_elem_of.
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
    eauto using not_elem_of_larger_impl_not_elem_of.
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


  Lemma evar_is_fresh_in_free_evar_subst x phi psi:
    evar_is_fresh_in x psi ->
    evar_is_fresh_in x (phi.[[evar: x ↦ psi]]).
  Proof.
    move: x psi. induction phi; intros y psi H; unfold evar_is_fresh_in; simpl; try set_solver.
    case_match; auto. set_solver.
  Qed.

  Lemma evar_is_fresh_in_evar_quantify x n phi:
    evar_is_fresh_in x (evar_quantify x n phi).
  Proof.
    move: x n. induction phi; intros y m; unfold evar_is_fresh_in; simpl; try set_solver.
    case_match; auto; set_solver.
  Qed.

  Lemma svar_is_fresh_in_free_evar_subst X phi psi:
    svar_is_fresh_in X psi ->
    svar_is_fresh_in X (phi.[[svar: X ↦ psi]]).
  Proof.
    move: X psi. induction phi; intros y psi H; unfold svar_is_fresh_in; simpl; try set_solver.
    case_match; auto. set_solver.
  Qed.

  Lemma svar_is_fresh_in_svar_quantify X n phi:
    svar_is_fresh_in X (svar_quantify X n phi).
  Proof.
    move: X n. induction phi; intros Y m; unfold svar_is_fresh_in; simpl; try set_solver.
    case_match; auto; set_solver.
  Qed.

  Lemma wfc_ex_aux_bevar_subst :
    forall phi psi n,
      well_formed_closed_ex_aux phi (S n) = true
      -> well_formed_closed_ex_aux psi n = true
      -> well_formed_closed_ex_aux (bevar_subst phi psi n) n = true.
  Proof.
    intros phi psi n H H0. 
    generalize dependent n. generalize dependent psi.
    induction phi; intros psi n' H H0; try lia; auto.
    - simpl in *. unfold well_formed_closed_ex_aux. repeat case_match; simpl; auto. lia.
    - simpl. simpl in H. apply andb_true_iff in H. destruct H as [H1 H2].
      rewrite IHphi1. apply H1. assumption. rewrite IHphi2. apply H2. assumption.
      reflexivity.
    - simpl. simpl in H. apply andb_true_iff in H. destruct H as [H1 H2].
      rewrite IHphi1. apply H1. assumption. rewrite IHphi2. apply H2. assumption.
      reflexivity.
    - simpl. simpl in H. rewrite IHphi. assumption. 2: reflexivity.
      eapply well_formed_closed_ex_aux_ind. 2: apply H0. lia.
    - simpl. simpl in H.
      rewrite IHphi. apply H.
      eapply well_formed_closed_ex_aux_ind. 2: apply H0. lia.
      reflexivity.
  Qed.

  Lemma wfc_mu_aux_bevar_subst :
    forall phi psi n n',
      well_formed_closed_mu_aux phi n' = true
      -> well_formed_closed_mu_aux psi n' = true
      -> well_formed_closed_mu_aux (bevar_subst phi psi n) n' = true.
  Proof.
    intros phi psi n n' H H0. 
    generalize dependent n. generalize dependent n'. generalize dependent psi.
    induction phi; intros psi n' H n'' H0; try lia; auto.
    - simpl in *. unfold well_formed_closed_mu_aux. repeat case_match; simpl; auto.
    - simpl. simpl in H.
      rewrite IHphi1; auto. 2: rewrite IHphi2; auto. all: destruct_and!; auto.
    - simpl. simpl in H. destruct_and!.
      rewrite IHphi1; auto. rewrite IHphi2; auto.
    - simpl. simpl in H. rewrite IHphi. assumption. 2: reflexivity.
      eauto using well_formed_closed_ex_aux_ind.
    - simpl. simpl in H.
      rewrite IHphi. apply H. 2: reflexivity.
      eapply well_formed_closed_mu_aux_ind.
      2: eassumption. lia.
  Qed.


  Lemma wfc_ex_aux_bsvar_subst :
    forall phi psi n n',
      well_formed_closed_ex_aux phi n = true
      -> well_formed_closed_ex_aux psi n = true
      -> well_formed_closed_ex_aux (bsvar_subst phi psi n') n = true.
  Proof.
    intros phi psi n n' H H0. 
    generalize dependent n. generalize dependent n'. generalize dependent psi.
    induction phi; intros psi n' n'' H H0; try lia; auto.
    - simpl in *. unfold well_formed_closed_ex_aux. repeat case_match; simpl; auto.
    - simpl. simpl in H. destruct_and!. split_and; auto.
    - simpl. simpl in H. destruct_and!. split_and; auto.
    - simpl. simpl in H. rewrite IHphi. assumption.
      eapply well_formed_closed_ex_aux_ind. 2: eassumption. lia. reflexivity.
    - simpl. simpl in H.
      rewrite IHphi. apply H.
      eapply well_formed_closed_ex_aux_ind. 2: eassumption. lia. reflexivity.
  Qed.

  Lemma wfc_mu_aux_bsvar_subst :
    forall phi psi n',
      well_formed_closed_mu_aux phi (S n') = true
      -> well_formed_closed_mu_aux psi n' = true
      -> well_formed_closed_mu_aux (bsvar_subst phi psi n') n' = true.
  Proof.
    intros phi psi n' H H0. 
    generalize dependent n'. generalize dependent psi.
    induction phi; intros psi n' H H0; try lia; auto.
    - simpl in *. unfold well_formed_closed_mu_aux. repeat case_match; simpl; auto. lia.
    - simpl. simpl in H. destruct_and!.
      rewrite IHphi1. apply H1. assumption. rewrite IHphi2. apply H2. assumption.
      reflexivity.
    - simpl. simpl in H. destruct_and!.
      rewrite IHphi1. apply H1. assumption. rewrite IHphi2. apply H2. assumption.
      reflexivity.
    - simpl. simpl in H. rewrite IHphi. assumption.
      assumption. reflexivity.
    - simpl. simpl in H.
      rewrite IHphi. apply H.
      eapply well_formed_closed_mu_aux_ind. 2: eassumption. lia. reflexivity.
  Qed.


  (*Helper lemma for wf_ex_to_wf_body *)
  Corollary wfc_ex_aux_body_ex_imp1:
    forall phi n x,
      well_formed_closed_ex_aux phi (S n) = true
      ->
      well_formed_closed_ex_aux (evar_open n x phi) n = true.
  Proof using .
    intros. apply wfc_ex_aux_bevar_subst; auto.
  Qed.

  Corollary wfc_mu_aux_body_ex_imp1:
    forall phi n n' x,
      well_formed_closed_mu_aux phi n' = true
      ->
      well_formed_closed_mu_aux (evar_open n x phi) n' = true.
  Proof using .
    intros. now apply wfc_mu_aux_bevar_subst.
  Qed.

  Corollary wfc_ex_aux_body_mu_imp1:
    forall phi n n' X,
      well_formed_closed_ex_aux phi n' = true
      ->
      well_formed_closed_ex_aux (svar_open n X phi) n' = true.
  Proof using .
    intros. now apply wfc_ex_aux_bsvar_subst.
  Qed.

  Corollary wfc_mu_aux_body_mu_imp1:
    forall phi n X,
      well_formed_closed_mu_aux phi (S n) = true
      ->
      well_formed_closed_mu_aux (svar_open n X phi) n = true.
  Proof using .
    intros. now apply wfc_mu_aux_bsvar_subst.
  Qed.

  Lemma wfc_mu_aux_bsvar_subst_le :
    forall phi psi n n', n' <= n ->
      well_formed_closed_mu_aux phi (S n) = true ->
      well_formed_closed_mu_aux psi n
      ->
      well_formed_closed_mu_aux (phi.[svar:n' ↦ psi]) n = true.
  Proof using .
    induction phi; intros psi n0 n' H Hwf1 Hwf2; try lia; auto.
    - simpl. case_match; auto. simpl. case_match; try lia.
      simpl in Hwf1. case_match; try lia. simpl. case_match; lia.
    - simpl. simpl in H. simpl in Hwf1. apply andb_true_iff in Hwf1 as [H1 H2].
      rewrite (IHphi1 _ _ n'); auto. rewrite (IHphi2 _ _ n'); auto.
    - simpl. simpl in H. simpl in Hwf1. apply andb_true_iff in Hwf1 as [H1 H2].
      rewrite (IHphi1 _ _ n'); auto. rewrite (IHphi2 _ _ n'); auto.
    - simpl. simpl in Hwf1. rewrite (IHphi _ _ n'); auto.
    - simpl. simpl in Hwf1. rewrite (IHphi _ _ (S n')); auto. lia.
      eapply well_formed_closed_mu_aux_ind. 2: eassumption. lia.
  Qed.

  Lemma wfc_ex_aux_bsvar_subst_le:
    forall phi psi n n', n' <= n ->
      well_formed_closed_ex_aux phi (S n) = true ->
      well_formed_closed_ex_aux psi n = true
      ->
      well_formed_closed_ex_aux (phi.[evar:n'↦psi]) n = true.
  Proof using .
    induction phi; intros psi n0 n' H Hwf1 Hwf2; try lia; auto.
    - simpl. case_match; auto. simpl. case_match; try lia.
      simpl in Hwf1. case_match; try lia. simpl. case_match; lia.
    - simpl. simpl in H. simpl in Hwf1. apply andb_true_iff in Hwf1 as [H1 H2].
      rewrite (IHphi1 _ _ n'); auto. rewrite (IHphi2 _ _ n'); auto.
    - simpl. simpl in H. simpl in Hwf1. apply andb_true_iff in Hwf1 as [H1 H2].
      rewrite (IHphi1 _ _ n'); auto. rewrite (IHphi2 _ _ n'); auto.
    - simpl. simpl in Hwf1. rewrite (IHphi _ _ (S n')); auto. lia.
      eapply well_formed_closed_ex_aux_ind. 2: eassumption. lia.
    - simpl. simpl in Hwf1. rewrite (IHphi _ _ n'); auto.
  Qed.

  Corollary wfc_mu_aux_body_mu_imp3:
    forall phi n n' X, n' <= n ->
      well_formed_closed_mu_aux phi (S n) = true
      ->
      well_formed_closed_mu_aux (svar_open n' X phi) n = true.
  Proof using .
    intros. now apply wfc_mu_aux_bsvar_subst_le.
  Qed.

  Corollary wfc_mu_aux_body_ex_imp3:
    forall phi n n' X, n' <= n ->
      well_formed_closed_ex_aux phi (S n) = true
      ->
      well_formed_closed_ex_aux (evar_open n' X phi) n = true.
  Proof using .
    intros. now apply wfc_ex_aux_bsvar_subst_le.
  Qed.

  Corollary wfc_ex_aux_body_iff: 
    forall phi n x,
      well_formed_closed_ex_aux phi (S n) = true
      <->
      well_formed_closed_ex_aux (evar_open n x phi) n = true.
  Proof.
    split.
    apply wfc_ex_aux_body_ex_imp1.
    apply wfc_ex_aux_body_ex_imp2.
  Qed.

  Corollary wfc_mu_aux_body_iff: 
    forall phi n X,
      well_formed_closed_mu_aux phi (S n) = true
      <->
      well_formed_closed_mu_aux (svar_open n X phi) n = true.
  Proof.
    split.
    apply wfc_mu_aux_body_mu_imp1.
    apply wfc_mu_aux_body_mu_imp2.
  Qed.

  
  (*If (ex, phi) is closed, then its body is closed too*)
  Corollary wfc_ex_to_wfc_body:
    forall phi, well_formed_closed (patt_exists phi) = true -> wfc_body_ex phi.
  Proof.
    intros phi WFE.
    unfold wfc_body_ex. intros x H.
    unfold well_formed_closed in *. simpl in WFE.
    apply andb_prop in WFE. destruct WFE as [WFE1 WFE2].
    rewrite wfc_ex_aux_body_ex_imp1. auto.
    rewrite wfc_mu_aux_body_ex_imp1. auto.
    reflexivity.
  Qed.

    (* Lemmas about wfc_ex and wfc_mu *)

  (*If phi is a closed body, then (ex, phi) is closed too*)
  Corollary wfc_body_to_wfc_ex phi:
    wfc_body_ex phi ->
    well_formed_closed (patt_exists phi) = true.
  Proof.
    intros WFE. unfold wfc_body_ex in WFE. unfold well_formed_closed. simpl.
    unfold well_formed_closed in WFE.
    pose proof (Htmp := WFE (fresh_evar phi) ltac:(apply set_evar_fresh_is_fresh)).
    destruct_and!.
    split_and.
    2: { rewrite -> wfc_ex_aux_body_iff. eassumption. }
    eapply wfc_mu_aux_body_ex_imp2. eassumption.
  Qed.

  (* From https://www.chargueraud.org/research/2009/ln/main.pdf in 3.4 (lc_abs_iff_body) *)
  (*Conclusion*)
  Corollary wfc_body_wfc_ex_iff: 
    forall phi,
      well_formed_closed (patt_exists phi) = true <-> wfc_body_ex phi.
  Proof.
    split.
    - apply wfc_ex_to_wfc_body.
    - apply wfc_body_to_wfc_ex.
  Qed.

(* TODO: deprecated, remove this
  (*Similarly to the section above but with mu*)
  Definition wfc_body_mu phi := forall X, 
      X ∉ (free_svars phi) -> well_formed_closed (svar_open 0 X phi) = true.

  (*If (mu, phi) is closed, then its body is closed too*)
  Lemma wfc_mu_to_wfc_body:
    forall phi, well_formed_closed (patt_mu phi) = true -> wfc_body_mu phi.
  Proof.
    intros phi H.
    unfold wfc_body_mu. intros X H0.
    unfold well_formed_closed in *. simpl in H.
    destruct_and!.
    split_and!; auto using wfc_ex_aux_body_mu_imp1,wfc_mu_aux_body_mu_imp1.
  Qed.

  (*If phi is a closed body, then (mu, phi) is closed too*)
  Lemma wfc_body_to_wfc_mu:
    forall phi, wfc_body_mu phi -> well_formed_closed (patt_mu phi) = true.
  Proof.
    intros phi H. unfold wfc_body_mu in H. unfold well_formed_closed. simpl.
    unfold well_formed_closed in H.
    pose proof (Htmp := H (fresh_svar phi) ltac:(apply set_svar_fresh_is_fresh)).
    destruct_and!. split_and.
    eauto using wfc_mu_aux_body_mu_imp2.
    eapply wfc_ex_aux_body_mu_imp2. eassumption.
  Qed.

  (* From https://www.chargueraud.org/research/2009/ln/main.pdf in 3.4 (lc_abs_iff_body) *)
  (*Conclusion*)
  Lemma wfc_body_wfc_mu_iff: 
    forall phi (X : svar),
      well_formed_closed (patt_mu phi) = true <-> wfc_body_mu phi.
  Proof.
    split.
    - apply wfc_mu_to_wfc_body.
    - apply wfc_body_to_wfc_mu.
  Qed.

  (* Similarly with positiveness *)
  Definition wfp_body_ex phi := forall x,
      x ∉ (free_evars phi) -> well_formed_positive (evar_open 0 x phi) = true.

  Lemma wfp_ex_to_wfp_body: forall phi,
      well_formed_positive (patt_exists phi) = true ->
      wfp_body_ex phi.
  Proof.
    unfold wfp_body_ex. intros phi H x H0.
    apply wfp_evar_open. simpl in H. assumption.
  Qed.

  (* Connection between bodies and well-formedness *)
  Definition wf_body_ex phi := forall x, 
      x ∉ (free_evars phi) -> well_formed (evar_open 0 x phi) = true.

  (* This might be useful in soundness cases prop_ex_left/right *)
  Lemma wf_ex_to_wf_body: forall phi,
      well_formed (patt_exists phi) = true ->
      wf_body_ex phi.
  Proof.
    unfold wf_body_ex. intros phi H x H0. unfold well_formed in *.
    apply andb_true_iff in H.
    destruct H as [H1 H2].
    rewrite (@wfp_ex_to_wfp_body phi H1). assumption.
    rewrite (@wfc_ex_to_wfc_body phi H2). assumption.
    reflexivity.
  Qed.

*)

  Lemma wfp_evar_open : forall phi x n,
      well_formed_positive phi = true ->
      well_formed_positive (evar_open n x phi) = true.
  Proof.
    induction phi; simpl in *; intros x' n' H; auto.
    - cbn. case_match; reflexivity.
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
    - now apply IHphi.
    - apply andb_true_iff in H.
      destruct H as [H1 H2].
      apply andb_true_iff.
      split.
      apply no_negative_occurrence_evar_open; auto.
      apply IHphi. apply H2.
  Qed.

(*
   TODO: deprecated, remove this
  (* inductive def of well_formed_closed, corresponding lemmas *)
  
  Inductive well_formed_closed_induc : Pattern -> Prop :=
  | wfc_free_evar : forall (x : evar), well_formed_closed_induc (patt_free_evar x)
  | wfc_free_svar : forall (X : svar), well_formed_closed_induc (patt_free_svar X)
  | wfc_sym       : forall (sym : symbols), well_formed_closed_induc (patt_sym sym)
  | wfc_app       : forall (phi psi : Pattern),
      well_formed_closed_induc phi -> well_formed_closed_induc psi
      -> well_formed_closed_induc (patt_app phi psi)
  | wfc_bott      : well_formed_closed_induc patt_bott
  | wfc_imp       : forall (phi psi : Pattern),
      well_formed_closed_induc phi -> well_formed_closed_induc psi
      -> well_formed_closed_induc (patt_imp phi psi)
  | wfc_ex        : forall phi : Pattern, 
      (forall (x : evar), 
          x ∉ (free_evars phi) ->
          well_formed_closed_induc (evar_open 0 x phi))
      -> well_formed_closed_induc (patt_exists phi)
  | wfc_mu        : forall phi : Pattern, 
      (forall (X : svar),
          X ∉ (free_svars phi) ->
          well_formed_closed_induc (svar_open 0 X phi)) 
      -> well_formed_closed_induc (patt_mu phi).

  Lemma wfc_wfc_ind_helper : forall sz phi, 
      well_formed_closed phi = true ->
      le (size phi) sz
      ->
      well_formed_closed_induc phi.
  Proof.
    induction sz; destruct phi; intros Hwf Hsz ; simpl in *; try inversion Hsz; auto. 1, 2, 5, 6 : constructor.
    - inversion Hwf.
    - inversion Hwf.
    - unfold well_formed_closed in *; simpl in *.
      destruct_and!.
      constructor.
      { apply IHsz. split_and!; assumption. lia. }
      { apply IHsz. split_and!; assumption. lia. }
    - unfold well_formed_closed in *; simpl in *.
      destruct_and!.
      constructor.
      { apply IHsz. split_and!; assumption. lia. }
      { apply IHsz. split_and!; assumption. lia. }
    - unfold well_formed_closed in *. simpl in *.
      constructor. apply wfc_ex_to_wfc_body in Hwf. unfold wfc_body_ex in Hwf. intros x H1. 
      apply (IHsz (evar_open 0 x phi)). apply Hwf. assumption. erewrite evar_open_size in Hsz.  apply Peano.le_S_n in Hsz. exact Hsz.
    - unfold well_formed_closed in Hwf. simpl in Hwf.
      constructor. apply wfc_mu_to_wfc_body in Hwf. unfold wfc_body_mu in Hwf. intros X H1. 
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
      well_formed_closed phi = true.
  Proof.
    intros phi H. induction H; simpl; auto.
    - unfold well_formed_closed. simpl. unfold well_formed_closed in *.
      destruct_and!. split_and!; auto.
    - unfold well_formed_closed. simpl. unfold well_formed_closed in *.
      destruct_and!. split_and!; auto.
    - apply wfc_body_to_wfc_ex. unfold wfc_body_ex. assumption.
    - apply wfc_body_to_wfc_mu. unfold wfc_body_mu. assumption.
  Qed.
*)

  (* Additional lemmas: evar_open, svar_open, freshness, well_formedness, etc. *)

  (* evar_open and evar_quantify are inverses *)
  Lemma evar_open_evar_quantify x n phi:
    well_formed_closed_ex_aux phi n ->
    (evar_open n x (evar_quantify x n phi)) = phi.
  Proof.
    intros H.
    (*apply wfc_wfc_ind in H.*)
    move: n H.
    induction phi; intros n' H; cbn; auto.
    - destruct (decide (x = x0)); subst; simpl.
      + break_match_goal; auto; lia.
      + reflexivity.
    - simpl in *. repeat case_match; simpl; auto; try lia; congruence.
    - cbn in H. simpl. unfold evar_open, evar_quantify in IHphi1, IHphi2.
      apply andb_true_iff in H.
      destruct H as [H1 H2].
      erewrite -> IHphi1, IHphi2 by eassumption.
      reflexivity.
    - simpl in H. unfold evar_open, evar_quantify in IHphi1, IHphi2.
      apply andb_true_iff in H.
      destruct H as [H1 H2].
      erewrite -> IHphi1, IHphi2 by eassumption.
      reflexivity.
    - simpl in H. unfold evar_open, evar_quantify in IHphi.
      erewrite -> IHphi by eassumption. reflexivity.
    - simpl in H. apply IHphi in H. unfold evar_open in H. rewrite H. reflexivity.
  Qed.

  Lemma svar_open_svar_quantify X n phi:
    well_formed_closed_mu_aux phi n ->
    (svar_open n X (svar_quantify X n phi)) = phi.
  Proof.
    intros H.
    (*apply wfc_wfc_ind in H.*)
    move: n H.
    induction phi; intros n' H; cbn; auto.
    - destruct (decide (X = x)); subst; simpl.
      + break_match_goal; auto; lia.
      + reflexivity.
    - simpl in *. repeat case_match; simpl; auto; try lia; congruence.
    - cbn in H. simpl. unfold svar_open in IHphi1, IHphi2.
      apply andb_true_iff in H.
      destruct H as [H1 H2].
      erewrite -> IHphi1, IHphi2 by eassumption.
      reflexivity.
    - simpl in H. unfold svar_open in IHphi1, IHphi2.
      apply andb_true_iff in H.
      destruct H as [H1 H2].
      erewrite -> IHphi1, IHphi2 by eassumption.
      reflexivity.
    - simpl in H. unfold svar_open in IHphi.
      erewrite -> IHphi by eassumption. reflexivity.
    - simpl in H. apply IHphi in H. unfold svar_open in H. rewrite H. reflexivity.
  Qed.

  Lemma evar_quantify_evar_open x n phi:
    x ∉ free_evars phi -> well_formed_closed_ex_aux phi n ->
    (evar_quantify x n (evar_open n x phi)) = phi.
  Proof.
    revert n.
    induction phi; intros n' H0 H1; simpl; auto.
    - destruct (decide (x = x0)); simpl.
      + subst. simpl in H0. apply sets.not_elem_of_singleton_1 in H0. congruence.
      + reflexivity.
    - simpl in *. unfold evar_quantify,evar_open. simpl.
      repeat case_match; auto; try congruence. lia.
    - unfold evar_open in IHphi1, IHphi2.
      apply sets.not_elem_of_union in H0. destruct H0 as [E1 E2].
      rewrite -> IHphi1, IHphi2.
      reflexivity.
      all: auto; apply andb_true_iff in H1; apply H1.
    - unfold evar_open in IHphi1, IHphi2.
      apply sets.not_elem_of_union in H0. destruct H0 as [E1 E2].
      rewrite -> IHphi1, IHphi2.
      reflexivity.
      all: auto; apply andb_true_iff in H1; apply H1.
    - simpl in H0. unfold evar_open in IHphi.
      rewrite -> IHphi by assumption. reflexivity.
    - simpl in H0. unfold evar_open in IHphi.
      rewrite -> IHphi by assumption. reflexivity.
  Qed.

  Lemma svar_quantify_svar_open X n phi:
    X ∉ free_svars phi -> well_formed_closed_mu_aux phi n ->
    (svar_quantify X n (svar_open n X phi)) = phi.
  Proof.
    revert n.
    induction phi; intros n' H0 H1; simpl; auto.
    - destruct (decide (X = x)); simpl.
      + subst. simpl in H0. apply sets.not_elem_of_singleton_1 in H0. congruence.
      + reflexivity.
    - simpl in *. unfold svar_quantify,svar_open,bsvar_subst.
      repeat case_match; auto; try congruence. lia.
    - unfold svar_open in IHphi1, IHphi2.
      apply sets.not_elem_of_union in H0. destruct H0 as [E1 E2].
      rewrite -> IHphi1, IHphi2.
      reflexivity.
      all: auto; apply andb_true_iff in H1; apply H1.
    - unfold svar_open in IHphi1, IHphi2.
      apply sets.not_elem_of_union in H0. destruct H0 as [E1 E2].
      rewrite -> IHphi1, IHphi2.
      reflexivity.
      all: auto; apply andb_true_iff in H1; apply H1.
    - simpl in H0. unfold svar_open in IHphi.
      erewrite -> IHphi by assumption. reflexivity.
    - simpl in H0. unfold svar_open in IHphi.
      erewrite -> IHphi by assumption. reflexivity.
  Qed.

  Lemma double_evar_quantify φ : forall x n,
    evar_quantify x n (evar_quantify x n φ) = evar_quantify x n φ.
  Proof.
    induction φ; intros x' n'; simpl; auto.
    * unfold evar_quantify. repeat case_match; auto. contradiction.
    * now rewrite -> IHφ1, -> IHφ2.
    * now rewrite -> IHφ1, -> IHφ2.
    * now rewrite IHφ.
    * now rewrite IHφ.
  Qed.

  Lemma double_svar_quantify φ : forall X n,
    svar_quantify X n (svar_quantify X n φ) = svar_quantify X n φ.
  Proof.
    induction φ; intros x' n'; simpl; auto.
    * unfold svar_quantify. repeat case_match; auto. contradiction.
    * now rewrite -> IHφ1, -> IHφ2.
    * now rewrite -> IHφ1, -> IHφ2.
    * now rewrite IHφ.
    * now rewrite IHφ.
  Qed.

  Lemma well_formed_bevar_subst φ : forall ψ n m,
    m >= n -> well_formed_closed_ex_aux φ n ->
    bevar_subst φ ψ m = φ.
  Proof.
    induction φ; intros ψ n' m' H H0; simpl; auto.
    * simpl in H0. repeat case_match; auto; try lia; congruence.
    * simpl in H0. apply eq_sym, andb_true_eq in H0. destruct H0. erewrite IHφ1, IHφ2.
      3: apply eq_sym, H1.
      4: apply eq_sym, H0. all: auto.
    * simpl in H0. apply eq_sym, andb_true_eq in H0. destruct H0. erewrite IHφ1, IHφ2.
      3: apply eq_sym, H1.
      4: apply eq_sym, H0. all: auto.
    * simpl in H0. erewrite IHφ. 3: apply H0. auto. lia.
    * simpl in H0. erewrite IHφ. 3: apply H0. all: auto.
  Qed.

  Lemma well_formed_bsvar_subst φ : forall ψ k m,
    m >= k -> well_formed_closed_mu_aux φ k ->
    bsvar_subst φ ψ m = φ.
  Proof.
    induction φ; intros ψ k' m' H H0; simpl; auto.
    * simpl in H0. repeat case_match; auto; try lia; congruence.
    * simpl in H0. apply eq_sym, andb_true_eq in H0. destruct H0. erewrite IHφ1, IHφ2.
      3: apply eq_sym, H1.
      4: apply eq_sym, H0. all: auto.
    * simpl in H0. apply eq_sym, andb_true_eq in H0. destruct H0. erewrite IHφ1, IHφ2.
      3: apply eq_sym, H1.
      4: apply eq_sym, H0. all: auto.
    * simpl in H0. erewrite IHφ. 3: apply H0. auto. lia.
    * simpl in H0. erewrite IHφ. 3: apply H0. all: auto. lia.
  Qed.

(* TODO: deprecated
  Lemma double_bevar_subst φ : forall ψ n,
    well_formed_closed_ex_aux ψ n ->
    bevar_subst (bevar_subst φ ψ n) ψ n = bevar_subst φ ψ n.
  Proof.
    induction φ; intros ψ n' H; simpl; auto.
    - repeat case_match; simpl.
      + rewrite Heqc. auto.
      + erewrite well_formed_bevar_subst. 3: exact H. all: auto.
      + case_match; auto. 
    - erewrite IHφ1, IHφ2; eauto.
    - erewrite IHφ1, IHφ2; eauto.
    - erewrite IHφ. auto. eapply well_formed_closed_ex_aux_ind. 2: eassumption. lia.
    - erewrite IHφ. auto. eapply well_formed_closed_ex_aux_ind. 2: eassumption. lia.
  Qed.

  Lemma evar_open_last: forall phi i u j v,
      (i <> j) -> evar_open i u (evar_open j v phi) = evar_open j v phi
      ->
      (evar_open i u phi) = phi.
  Proof.
    induction phi; firstorder.
    - cbn in H0. cbn. repeat case_match; auto; try lia.
      simpl in H0. case_match; congruence.
      simpl in H0. case_match; congruence.
      simpl in H0. case_match; congruence.
    - unfold evar_open in *. rewrite bevar_subst_app;[reflexivity|]. erewrite IHphi1, IHphi2. reflexivity. exact H. inversion H0. exact H3. exact H.  inversion H0. exact H2.
    - unfold evar_open in *. rewrite bevar_subst_imp;[reflexivity|]. erewrite IHphi1, IHphi2. reflexivity. exact H. inversion H0. exact H3. exact H.  inversion H0. exact H2.
    - simpl in H0. inversion H0. unfold evar_open in *. rewrite bevar_subst_exists;[reflexivity|]. erewrite (IHphi (S i) _ (S j)). reflexivity. lia. exact H2.
    - simpl in H0. inversion H0. unfold evar_open in *. rewrite bevar_subst_mu;[reflexivity|]. erewrite (IHphi (i) _ (j)). reflexivity. lia. exact H2.
  Qed.

  Lemma svar_open_last: forall phi i u j v,
      evar_open i u (svar_open j v phi) = svar_open j v phi
      ->
      (evar_open i u phi) = phi.
  Proof.
    induction phi; firstorder.
    - unfold evar_open in *. rewrite bevar_subst_app;[reflexivity|]. erewrite IHphi1, IHphi2. reflexivity. inversion H. exact H2. inversion H. exact H1.
    - unfold evar_open in *. rewrite bevar_subst_imp;[reflexivity|]. erewrite IHphi1, IHphi2. reflexivity. inversion H. exact H2. inversion H. exact H1.
    - simpl in H. inversion H. unfold evar_open in *. rewrite bevar_subst_exists;[reflexivity|]. erewrite (IHphi (S i) _ (j)). reflexivity. exact H1.
    - simpl in H. inversion H. unfold evar_open in *. rewrite bevar_subst_mu;[reflexivity|]. erewrite (IHphi (i) _ (S j)). reflexivity. exact H1.
  Qed.
  
  Lemma svar_open_last2: forall phi i u j v,
      svar_open i u (evar_open j v phi) = evar_open j v phi
      ->
      (svar_open i u phi) = phi.
  Proof.
    induction phi; firstorder.
    - unfold svar_open in *. rewrite bsvar_subst_app;[reflexivity|]. erewrite IHphi1, IHphi2. reflexivity. inversion H. exact H2. inversion H. exact H1.
    - unfold svar_open in *. rewrite bsvar_subst_imp;[reflexivity|]. erewrite IHphi1, IHphi2. reflexivity. inversion H. exact H2. inversion H. exact H1.
    - simpl in H. inversion H. unfold svar_open in *. rewrite bsvar_subst_exists;[reflexivity|]. erewrite (IHphi (i) _ (S j)). reflexivity. exact H1.
    - simpl in H. inversion H. unfold svar_open in *. rewrite bsvar_subst_mu;[reflexivity|]. erewrite (IHphi (S i) _ (j)). reflexivity. exact H1.
  Qed.
  
  Lemma svar_open_last3: forall phi i u j v,
      (i <> j) -> svar_open i u (svar_open j v phi) = svar_open j v phi
      ->
      (svar_open i u phi) = phi.
  Proof.
    induction phi; firstorder.
    - cbn in *. unfold bsvar_subst in H0. repeat case_match; congruence.
    - unfold svar_open in *. rewrite bsvar_subst_app;[reflexivity|]. erewrite IHphi1, IHphi2. reflexivity. exact H. inversion H0. exact H3. exact H.  inversion H0. exact H2.
    - unfold svar_open in *. rewrite bsvar_subst_imp;[reflexivity|]. erewrite IHphi1, IHphi2. reflexivity. exact H. inversion H0. exact H3. exact H.  inversion H0. exact H2.
    - simpl in H0. inversion H0. unfold svar_open in *. rewrite bsvar_subst_exists;[reflexivity|]. erewrite (IHphi (i) _ (j)). reflexivity. lia. exact H2.
    - simpl in H0. inversion H0. unfold svar_open in *. rewrite bsvar_subst_mu;[reflexivity|]. erewrite (IHphi (S i) _ (S j)). reflexivity. lia. exact H2.
  Qed. *)

  (* opening on closed patterns is identity *)
  Lemma evar_open_closed :
    forall phi,
      well_formed_closed_ex_aux phi 0 ->
      forall n v,
        evar_open n v phi = phi.
  Proof.
    intros phi H n v. unfold evar_open. erewrite well_formed_bevar_subst. 3: exact H.
    auto. lia.
  Qed.

  Lemma svar_open_closed :
    forall phi,
      well_formed_closed_mu_aux phi 0 ->
      forall n v,
        svar_open n v phi = phi.
  Proof. 
    intros phi H n v. unfold svar_open. erewrite well_formed_bsvar_subst. 3: exact H.
    auto. lia.
  Qed.

  Lemma bevar_subst_comm_higher :
    forall phi psi1 psi2 n m, 
    n > m -> well_formed_closed_ex_aux psi1 0 -> well_formed_closed_ex_aux psi2 0 ->
    bevar_subst (bevar_subst phi psi1 n) psi2 m = 
    bevar_subst (bevar_subst phi psi2 m) psi1 (pred n).
  Proof.
    induction phi; intros psi1 psi2 n0 m0 NEQ Hwf1 Hwf2; simpl; auto.
    - repeat case_match; simpl; try rewrite -> Heqc; try rewrite -> Heqc0; auto; subst; try congruence.
      all:  repeat case_match; try lia; auto.
      1-2: subst; erewrite well_formed_bevar_subst; try eassumption; auto; lia.
    - rewrite -> IHphi1, -> IHphi2; auto.
    - rewrite -> IHphi1, -> IHphi2; auto.
    - rewrite -> IHphi; auto; try lia.
      replace (pred (S n0)) with n0 by lia.
      now replace (S (pred n0)) with n0 by lia.
    - rewrite -> IHphi; auto.
  Qed.

  Lemma bevar_subst_comm_lower :
    forall phi psi1 psi2 n m, 
    n < m -> well_formed_closed_ex_aux psi1 0 -> well_formed_closed_ex_aux psi2 0 ->
    bevar_subst (bevar_subst phi psi1 n) psi2 m = 
    bevar_subst (bevar_subst phi psi2 (S m)) psi1 n.
  Proof.
    induction phi; intros psi1 psi2 n0 m0 NEQ Hwf1 Hwf2; simpl; auto.
    - repeat case_match; simpl; try rewrite -> Heqc; try rewrite -> Heqc0; auto; subst; try congruence.
      all:  repeat case_match; try lia; auto.
      1-2: subst; erewrite well_formed_bevar_subst; try eassumption; auto. 2: lia.
      eapply well_formed_closed_ex_aux_ind. 2: exact Hwf1. lia.
    - rewrite -> IHphi1, -> IHphi2; auto.
    - rewrite -> IHphi1, -> IHphi2; auto.
    - rewrite -> IHphi; auto; try lia.
    - rewrite -> IHphi; auto.
  Qed.

  Lemma bsvar_subst_comm_higher :
    forall phi psi1 psi2 n m, 
    n > m -> well_formed_closed_mu_aux psi1 0 -> well_formed_closed_mu_aux psi2 0 ->
    bsvar_subst (bsvar_subst phi psi1 n) psi2 m = 
    bsvar_subst (bsvar_subst phi psi2 m) psi1 (pred n).
  Proof.
    induction phi; intros psi1 psi2 n0 m0 NEQ Hwf1 Hwf2; simpl; auto.
    - repeat case_match; simpl; try rewrite -> Heqc; try rewrite -> Heqc0; auto; subst; try congruence.
      all:  repeat case_match; try lia; auto.
      1-2: subst; erewrite well_formed_bsvar_subst; try eassumption; auto; lia.
    - rewrite -> IHphi1, -> IHphi2; auto.
    - rewrite -> IHphi1, -> IHphi2; auto.
    - rewrite -> IHphi; auto.
    - rewrite -> IHphi; auto. 2: lia.
      replace (pred (S n0)) with n0 by lia.
      now replace (S (pred n0)) with n0 by lia.
  Qed.

  Lemma bsvar_subst_comm_lower :
    forall phi psi1 psi2 n m, 
    n < m -> well_formed_closed_mu_aux psi1 0 -> well_formed_closed_mu_aux psi2 0 ->
    bsvar_subst (bsvar_subst phi psi1 n) psi2 m = 
    bsvar_subst (bsvar_subst phi psi2 (S m)) psi1 n.
  Proof.
    induction phi; intros psi1 psi2 n0 m0 NEQ Hwf1 Hwf2; simpl; auto.
    - repeat case_match; simpl; try rewrite -> Heqc; try rewrite -> Heqc0; auto; subst; try congruence.
      all:  repeat case_match; try lia; auto.
      1-2: subst; erewrite well_formed_bsvar_subst; try eassumption; auto. 2: lia.
      eapply well_formed_closed_mu_aux_ind. 2: exact Hwf1. lia.
    - rewrite -> IHphi1, -> IHphi2; auto.
    - rewrite -> IHphi1, -> IHphi2; auto.
    - rewrite -> IHphi; auto.
    - rewrite -> IHphi; auto. lia.
  Qed.

  Corollary evar_open_comm_higher:
    forall n m,
      n < m 
      ->
      forall x y phi,
        evar_open n x (evar_open m y phi) = evar_open (pred m) y (evar_open n x phi).
  Proof.
    intros n m Hneqnm x y phi. apply bevar_subst_comm_higher; auto.
  Qed.

  Corollary evar_open_comm_lower:
    forall n m,
      n > m 
      ->
      forall x y phi,
        evar_open n x (evar_open m y phi) = evar_open m y (evar_open (S n) x phi).
  Proof.
    intros n m Hneqnm x y phi. apply bevar_subst_comm_lower; auto.
  Qed.

  Corollary svar_open_comm_higher:
    forall n m,
      n < m 
      ->
      forall X Y phi,
        svar_open n X (svar_open m Y phi) = svar_open (pred m) Y (svar_open n X phi).
  Proof.
    intros n m Hneqnm x y phi. apply bsvar_subst_comm_higher; auto.
  Qed.

  Corollary svar_open_comm_lower:
    forall n m,
      n > m
      ->
      forall X Y phi,
        svar_open n X (svar_open m Y phi) = svar_open m Y (svar_open (S n) X phi).
  Proof.
    intros n m Hneqnm x y phi. apply bsvar_subst_comm_lower; auto.
  Qed.

  Lemma bevar_subst_bsvar_subst phi psi1 psi2 dbi1 dbi2
    : well_formed_closed psi1 -> well_formed_closed psi2 ->
      bevar_subst (bsvar_subst phi psi1 dbi1) psi2 dbi2
      = bsvar_subst (bevar_subst phi psi2 dbi2) psi1 dbi1.
  Proof.
    generalize dependent dbi1. generalize dependent dbi2.
    induction phi; intros dbi1 dbi2 Hwf1 Hwf2; simpl; auto.
    * break_match_goal; auto. erewrite well_formed_bsvar_subst; auto.
      unfold well_formed_closed in *. destruct_and!.
      eapply well_formed_closed_mu_aux_ind. 2: eassumption. lia.
    * break_match_goal; auto. erewrite well_formed_bevar_subst; auto.
      unfold well_formed_closed in *. destruct_and!.
      eapply well_formed_closed_ex_aux_ind. 2: eassumption. lia.
    * simpl. rewrite -> IHphi1, -> IHphi2; auto.
    * simpl. rewrite -> IHphi1, -> IHphi2; auto.
    * simpl. rewrite IHphi; auto.
    * simpl. rewrite IHphi; auto.
  Qed.

  Corollary svar_open_evar_open_comm
    : forall (phi : Pattern) (dbi1 : db_index)(x : evar)(dbi2 : db_index)(X : svar),
      evar_open dbi1 x (svar_open dbi2 X phi) = svar_open dbi2 X (evar_open dbi1 x phi).
  Proof.
    intros phi dbi1 x dbi2 X. apply bevar_subst_bsvar_subst; auto.
  Qed.

  (* TODO make a wrapper that does not have the 'sz' variable *)
  Lemma bevar_subst_fresh_notin: 
    forall sz phi psi v,
      le (size phi) sz ->
      v ∉ (free_evars phi) ->
      v ∉ (free_evars psi) ->
      forall n,
        v ∉ (free_evars (bevar_subst phi psi n)).
  Proof.
    induction sz; destruct phi; intros psi v Hsz Hlsv Hneq n0; simpl in *; try inversion Hsz; auto.
    - case_match; set_solver.
    - case_match; set_solver.
    - specialize (IHsz phi1 psi v ltac:(lia) ltac:(set_solver) ltac:(set_solver) n0) as IH1.
      specialize (IHsz phi2 psi v ltac:(lia) ltac:(set_solver) ltac:(set_solver) n0) as IH2.
      set_solver.
    - specialize (IHsz phi1 psi v ltac:(lia) ltac:(set_solver) ltac:(set_solver) n0) as IH1.
      specialize (IHsz phi2 psi v ltac:(lia) ltac:(set_solver) ltac:(set_solver) n0) as IH2.
      set_solver.
    - specialize (IHsz phi1 psi v ltac:(lia) ltac:(set_solver) ltac:(set_solver) n0) as IH1.
      specialize (IHsz phi2 psi v ltac:(lia) ltac:(set_solver) ltac:(set_solver) n0) as IH2.
      set_solver.
    - specialize (IHsz phi1 psi v ltac:(lia) ltac:(set_solver) ltac:(set_solver) n0) as IH1.
      specialize (IHsz phi2 psi v ltac:(lia) ltac:(set_solver) ltac:(set_solver) n0) as IH2.
      set_solver.
    - now specialize (IHsz phi psi v ltac:(lia) ltac:(set_solver) ltac:(set_solver) (S n0)).
    - now specialize (IHsz phi psi v ltac:(lia) ltac:(set_solver) ltac:(set_solver) (S n0)).
    - now specialize (IHsz phi psi v ltac:(lia) ltac:(set_solver) ltac:(set_solver) n0).
    - now specialize (IHsz phi psi v ltac:(lia) ltac:(set_solver) ltac:(set_solver) n0).
  Qed.

  Lemma bsvar_subst_fresh_notin: 
    forall sz phi psi v,
      le (size phi) sz ->
      v ∉ (free_svars phi) ->
      v ∉ (free_svars psi) ->
      forall n,
        v ∉ (free_svars (bsvar_subst phi psi n)).
  Proof.
    induction sz; destruct phi; intros psi v Hsz Hlsv Hneq n0; simpl in *; try inversion Hsz; auto.
    - case_match; set_solver.
    - case_match; set_solver.
    - specialize (IHsz phi1 psi v ltac:(lia) ltac:(set_solver) ltac:(set_solver) n0) as IH1.
      specialize (IHsz phi2 psi v ltac:(lia) ltac:(set_solver) ltac:(set_solver) n0) as IH2.
      set_solver.
    - specialize (IHsz phi1 psi v ltac:(lia) ltac:(set_solver) ltac:(set_solver) n0) as IH1.
      specialize (IHsz phi2 psi v ltac:(lia) ltac:(set_solver) ltac:(set_solver) n0) as IH2.
      set_solver.
    - specialize (IHsz phi1 psi v ltac:(lia) ltac:(set_solver) ltac:(set_solver) n0) as IH1.
      specialize (IHsz phi2 psi v ltac:(lia) ltac:(set_solver) ltac:(set_solver) n0) as IH2.
      set_solver.
    - specialize (IHsz phi1 psi v ltac:(lia) ltac:(set_solver) ltac:(set_solver) n0) as IH1.
      specialize (IHsz phi2 psi v ltac:(lia) ltac:(set_solver) ltac:(set_solver) n0) as IH2.
      set_solver.
    - now specialize (IHsz phi psi v ltac:(lia) ltac:(set_solver) ltac:(set_solver) (n0)).
    - now specialize (IHsz phi psi v ltac:(lia) ltac:(set_solver) ltac:(set_solver) (n0)).
    - now specialize (IHsz phi psi v ltac:(lia) ltac:(set_solver) ltac:(set_solver) (S n0)).
    - now specialize (IHsz phi psi v ltac:(lia) ltac:(set_solver) ltac:(set_solver) (S n0)).
  Qed.

  Corollary evar_open_fresh_notin: 
    forall phi v w,
      v ∉ (free_evars phi) ->
      w ∉ (free_evars phi) ->
      (v <> w) ->
      forall n,
        v ∉ (free_evars (evar_open n w phi)).
  Proof.
    intros phi v w N1 N2 NEQ n. eapply bevar_subst_fresh_notin.
    reflexivity.
    auto.
    set_solver.
  Qed.

  Corollary svar_open_fresh_notin: 
    forall phi v w,
      v ∉ (free_svars phi) ->
      w ∉ (free_svars phi) ->
      (v <> w) ->
      forall n,
        v ∉ (free_svars (svar_open n w phi)).
  Proof.
    intros phi v w N1 N2 NEQ n.
    unfold svar_open. eapply bsvar_subst_fresh_notin.
    reflexivity.
    auto.
    set_solver.
  Qed.

  Lemma free_evars_svar_open : forall (psi : Pattern) (dbi :db_index) (X : svar),
      free_evars (svar_open dbi X psi) = free_evars psi.
  Proof.
    unfold svar_open.
    induction psi; intros dbi X; simpl; try reflexivity.
    * case_match; reflexivity.
    * rewrite -> IHpsi1. rewrite -> IHpsi2. reflexivity.
    * rewrite -> IHpsi1. rewrite -> IHpsi2. reflexivity.
    * rewrite -> IHpsi. reflexivity.
    * rewrite -> IHpsi. reflexivity.
  Qed.

  Lemma not_free_implies_positive_negative_occurrence :
    forall (phi : Pattern) (X : svar),
      X ∉ (free_svars phi) ->
      svar_has_positive_occurrence X phi = false /\ svar_has_negative_occurrence X phi = false.
  Proof.
    induction phi; simpl; intros Y H; split; try auto.
    * case_match; auto. set_solver.
    * now erewrite -> (proj1 (IHphi1 _ _)), -> (proj1 (IHphi2 _ _)).
    * now erewrite -> (proj2 (IHphi1 _ _)), -> (proj2 (IHphi2 _ _)).
    * now erewrite -> (proj2 (IHphi1 _ _)), -> (proj1 (IHphi2 _ _)).
    * now erewrite -> (proj1 (IHphi1 _ _)), -> (proj2 (IHphi2 _ _)).
    * now erewrite -> (proj1 (IHphi _ _)).
    * now erewrite -> (proj2 (IHphi _ _)).
    * now erewrite -> (proj1 (IHphi _ _)).
    * now erewrite -> (proj2 (IHphi _ _)).
    Unshelve. all: set_solver.
  Qed.

  Lemma well_formed_app_1 : forall (phi1 phi2 : Pattern),
      well_formed (patt_app phi1 phi2) -> well_formed phi1.
  Proof.
    unfold well_formed. simpl. intros phi1 phi2 H.
    apply andb_true_iff in H as [Hpos Hclos].
    apply andb_true_iff in Hclos as [Hcl1 Hcl2]. simpl in Hcl1, Hcl2.
    apply andb_true_iff in Hpos as [Hpos1 Hpos2].
    apply andb_true_iff in Hcl1 as [Hcl11 Hcl12].
    apply andb_true_iff in Hcl2 as [Hcl21 Hcl22].
    rewrite -> Hpos1. unfold well_formed_closed. simpl.
    now rewrite -> Hcl11, -> Hcl21.
  Qed.

  Lemma well_formed_app_2 : forall (phi1 phi2 : Pattern),
      well_formed (patt_app phi1 phi2) -> well_formed phi2.
  Proof.
    unfold well_formed. simpl. intros phi1 phi2 H.
    apply andb_true_iff in H as [Hpos Hclos].
    apply andb_true_iff in Hclos as [Hcl1 Hcl2]. simpl in Hcl1, Hcl2.
    apply andb_true_iff in Hpos as [Hpos1 Hpos2].
    apply andb_true_iff in Hcl1 as [Hcl11 Hcl12].
    apply andb_true_iff in Hcl2 as [Hcl21 Hcl22].
    rewrite -> Hpos2. unfold well_formed_closed. simpl.
    now rewrite -> Hcl12, -> Hcl22.
  Qed.

  Lemma free_svars_evar_open : forall (ϕ : Pattern) (dbi :db_index) (x : evar),
      free_svars (evar_open dbi x ϕ) = free_svars ϕ.
  Proof.
    unfold evar_open.
    induction ϕ; intros dbi x'; simpl; try reflexivity.
    * case_match; reflexivity.
    * rewrite -> IHϕ1. rewrite -> IHϕ2. reflexivity.
    * rewrite -> IHϕ1. rewrite -> IHϕ2. reflexivity.
    * rewrite -> IHϕ. reflexivity.
    * rewrite -> IHϕ. reflexivity.
  Qed.

  Lemma free_svars_exists : forall (ϕ : Pattern),
      free_svars (patt_exists ϕ) = free_svars ϕ.
  Proof. done. Qed.

  Lemma positive_negative_occurrence_db_named :
    forall (phi : Pattern) (dbi : db_index) (X : svar),
      (no_positive_occurrence_db_b dbi phi ->
       svar_has_positive_occurrence X phi = false ->
       svar_has_positive_occurrence X (svar_open dbi X phi) = false)
      /\ (no_negative_occurrence_db_b dbi phi ->
          svar_has_negative_occurrence X phi = false ->
          svar_has_negative_occurrence X (svar_open dbi X phi) = false).
  Proof.
    unfold svar_open.
    induction phi; intros dbi X; split; simpl; try firstorder.
    * do 2 case_match; auto; congruence.
    * case_match; auto; congruence.
    * destruct_and!. apply orb_false_iff in H0 as [H01 H02].
      erewrite -> (proj1 (IHphi1 _ _)), -> (proj1 (IHphi2 _ _)); auto.
    * destruct_and!. apply orb_false_iff in H0 as [H01 H02].
      erewrite -> (proj2 (IHphi1 _ _)), -> (proj2 (IHphi2 _ _)); auto.
    * destruct_and!. apply orb_false_iff in H0 as [H01 H02].
      erewrite -> (proj2 (IHphi1 _ _)), -> (proj1 (IHphi2 _ _)); auto.
    * destruct_and!. apply orb_false_iff in H0 as [H01 H02].
      erewrite -> (proj1 (IHphi1 _ _)), -> (proj2 (IHphi2 _ _)); auto.
  Qed.

  Lemma positive_negative_occurrence_evar_open : forall (ϕ : Pattern) (X : svar) (dbi : db_index) (x : evar),
      (svar_has_positive_occurrence X (evar_open dbi x ϕ) = false <-> svar_has_positive_occurrence X ϕ = false)
      /\ (svar_has_negative_occurrence X (evar_open dbi x ϕ) = false <-> svar_has_negative_occurrence X ϕ = false).
  Proof.
    unfold evar_open.
    induction ϕ; intros dbi X; split; simpl; auto.
    * case_match; auto; congruence.
    * case_match; auto; congruence.
    * split.
      - intro H. apply orb_false_iff in H as [? ?].
        erewrite -> (proj1 (proj1 (IHϕ1 _ _ _))), -> (proj1 (proj1 (IHϕ2 _ _ _))); eauto.
      - intro H. apply orb_false_iff in H as [? ?].
        erewrite -> (proj2 (proj1 (IHϕ1 _ _ _))), -> (proj2 (proj1 (IHϕ2 _ _ _))); eauto.
    * split.
      - intro H. apply orb_false_iff in H as [? ?].
        erewrite -> (proj1 (proj2 (IHϕ1 _ _ _))), -> (proj1 (proj2 (IHϕ2 _ _ _))); eauto.
      - intro H. apply orb_false_iff in H as [? ?].
        erewrite -> (proj2 (proj2 (IHϕ1 _ _ _))), -> (proj2 (proj2 (IHϕ2 _ _ _))); eauto.
    * split.
      - intro H. apply orb_false_iff in H as [? ?].
        erewrite -> (proj1 (proj2 (IHϕ1 _ _ _))), -> (proj1 (proj1 (IHϕ2 _ _ _))); eauto.
      - intro H. apply orb_false_iff in H as [? ?].
        erewrite -> (proj2 (proj2 (IHϕ1 _ _ _))), -> (proj2 (proj1 (IHϕ2 _ _ _))); eauto.
    * split.
      - intro H. apply orb_false_iff in H as [? ?].
        erewrite -> (proj1 (proj1 (IHϕ1 _ _ _))), -> (proj1 (proj2 (IHϕ2 _ _ _))); eauto.
      - intro H. apply orb_false_iff in H as [? ?].
        erewrite -> (proj2 (proj1 (IHϕ1 _ _ _))), -> (proj2 (proj2 (IHϕ2 _ _ _))); eauto.
    * split.
      - intro H. erewrite -> (proj1 (proj1 (IHϕ _ _ _))); eauto.
      - intro H. erewrite -> (proj2 (proj1 (IHϕ _ _ _))); eauto.
    * split.
      - intro H. erewrite -> (proj1 (proj2 (IHϕ _ _ _))); eauto.
      - intro H. erewrite -> (proj2 (proj2 (IHϕ _ _ _))); eauto.
    * split.
      - intro H. erewrite -> (proj1 (proj1 (IHϕ _ _ _))); eauto.
      - intro H. erewrite -> (proj2 (proj1 (IHϕ _ _ _))); eauto.
    * split.
      - intro H. erewrite -> (proj1 (proj2 (IHϕ _ _ _))); eauto.
      - intro H. erewrite -> (proj2 (proj2 (IHϕ _ _ _))); eauto.
  Qed.

  Corollary positive_occurrence_evar_open : forall (ϕ : Pattern) (X : svar) (dbi : db_index) (x : evar),
      svar_has_positive_occurrence X (evar_open dbi x ϕ) = false <-> svar_has_positive_occurrence X ϕ = false.
  Proof.
    apply positive_negative_occurrence_evar_open.
  Qed.

  Corollary negative_occurrence_evar_open : forall (ϕ : Pattern) (X : svar) (dbi : db_index) (x : evar),
      svar_has_negative_occurrence X (evar_open dbi x ϕ) = false <-> svar_has_negative_occurrence X ϕ = false.
  Proof.
    apply positive_negative_occurrence_evar_open.
  Qed.

  Lemma evar_open_wfp : forall (sz : nat) (phi : Pattern),
      le (size phi) sz -> well_formed_positive phi ->
      forall(n : db_index) (x : evar), well_formed_positive (evar_open n x phi).
  Proof.
    unfold evar_open.
    induction sz; destruct phi; intros Hsz Hwfp dbi e; simpl in *; auto; try inversion Hsz; subst.
    + case_match; constructor.
    + case_match; constructor.
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

(* TODO: deprecated
  Lemma positive_occurrence_db_svar_open : forall (phi : Pattern) (dbi : db_index) (X : svar),
      (positive_occurrence_db dbi phi ->
       positive_occurrence_db dbi (svar_open dbi X phi))
      /\ (negative_occurrence_db dbi phi -> negative_occurrence_db dbi (svar_open dbi X phi)).
  Proof.
    unfold svar_open.
    induction phi; intros dbi X; simpl; split; intros; try constructor; try inversion H; try firstorder.
    + case_match; constructor.
    + case_match; auto.
      lia. subst. constructor. lia.
  Qed. *)

  Lemma positive_negative_occurrence_db_svar_open_le : forall (phi : Pattern) (dbi1 dbi2 : db_index) (X : svar),
      dbi1 < dbi2 ->
      (
        no_positive_occurrence_db_b dbi1 phi ->
        no_positive_occurrence_db_b dbi1 (svar_open dbi2 X phi)
      )
      /\ (no_negative_occurrence_db_b dbi1 phi -> no_negative_occurrence_db_b dbi1 (svar_open dbi2 X phi)).
  Proof.
    unfold svar_open.
    induction phi; intros dbi1 dbi2 X Hneq; split; intros H; simpl in *; auto.
    + do 2 case_match; auto; simpl; case_match; auto. lia.
    + case_match; constructor; auto.
    + destruct_and!; split_and!.
      - now apply IHphi1.
      - now apply IHphi2.
    + destruct_and!; split_and!.
      - now apply IHphi1.
      - now apply IHphi2.
    + destruct_and!; split_and!.
      - now apply IHphi1.
      - now apply IHphi2.
    + destruct_and!; split_and!.
      - now apply IHphi1.
      - now apply IHphi2.
    + now apply IHphi.
    + now apply IHphi.
    + apply IHphi; auto. lia.
    + apply IHphi; auto. lia.
  Qed.

  Lemma wfp_svar_open : forall (phi : Pattern) (dbi : db_index) (X : svar),
      well_formed_positive phi = true ->
      well_formed_positive (svar_open dbi X phi) = true.
  Proof.
    unfold svar_open.
    induction phi; simpl; intros dbi X H.
    + constructor.
    + constructor.
    + constructor.
    + simpl. case_match; constructor.
    + constructor.
    + inversion H. apply andb_true_iff in H1. destruct H1 as [H1 H2].
      rewrite IHphi1. assumption. rewrite IHphi2. assumption.
      destruct_and!. symmetry. simpl. split_and!; auto.
    + constructor.
    + apply andb_true_iff in H. destruct H as [H1 H2]. rewrite IHphi1. apply H1. rewrite IHphi2. apply H2.
      reflexivity.
    + simpl in H. simpl. auto.
    + simpl in H. simpl. apply andb_true_iff in H. destruct H as [H1 H2].
      rewrite IHphi. apply H2. rewrite andb_true_r.
      apply positive_negative_occurrence_db_svar_open_le; auto. lia.
  Qed.

  Lemma positive_negative_occurrence_named_svar_open :
    forall (phi : Pattern) (X Y : svar) (dbi : db_index),
      X <> Y ->
      (
        svar_has_negative_occurrence X phi = false ->
        svar_has_negative_occurrence X (svar_open dbi Y phi) = false
      ) /\ (
        svar_has_positive_occurrence X phi = false ->
        svar_has_positive_occurrence X (svar_open dbi Y phi) = false
      ).
  Proof.
    unfold svar_open.
    induction phi; intros X Y dbi XneY; split; intros Hneg; simpl in *; auto; try firstorder.
    - now case_match.
    - case_match; try auto. simpl. case_match; auto. congruence.
    - apply orb_false_iff in Hneg as [H1 H2].
      now erewrite -> (proj1 (IHphi1 X Y dbi XneY)), -> (proj1 (IHphi2 X Y dbi XneY)).
    - apply orb_false_iff in Hneg as [H1 H2].
      now erewrite -> (proj2 (IHphi1 X Y dbi XneY)), -> (proj2 (IHphi2 X Y dbi XneY)).
    - apply orb_false_iff in Hneg as [H1 H2].
      now erewrite -> (proj2 (IHphi1 X Y dbi XneY)), -> (proj1 (IHphi2 X Y dbi XneY)).
    - apply orb_false_iff in Hneg as [H1 H2].
      now erewrite -> (proj1 (IHphi1 X Y dbi XneY)), -> (proj2 (IHphi2 X Y dbi XneY)).
  Qed.

  Corollary evar_open_wfc_aux db1 db2 X phi :
    db1 <= db2 ->
    well_formed_closed_ex_aux phi db1 ->
    evar_open db2 X phi = phi.
  Proof.
    intros H H0. unfold evar_open. eapply well_formed_bevar_subst. 2: eassumption. auto.
  Qed.

  Corollary evar_open_wfc m X phi : well_formed_closed_ex_aux phi 0 -> evar_open m X phi = phi.
  Proof.
    intros H.
    unfold well_formed_closed in H.
    apply evar_open_wfc_aux with (X := X)(db2 := m) in H.
    2: lia.
    auto.
  Qed.

  Corollary svar_open_wfc_aux db1 db2 X phi :
    db1 <= db2 ->
    well_formed_closed_mu_aux phi db1 ->
    svar_open db2 X phi = phi.
  Proof.
    intros H H0. unfold evar_open. eapply well_formed_bsvar_subst. 2: eassumption. auto.
  Qed.

  Corollary svar_open_wfc m X phi : well_formed_closed_mu_aux phi 0 -> svar_open m X phi = phi.
  Proof.
    intros H.
    unfold well_formed_closed in H.
    apply svar_open_wfc_aux with (X := X)(db2 := m) in H.
    2: lia.
    auto.
  Qed.

  Corollary evar_open_bsvar_subst m phi1 phi2 dbi X
    : well_formed_closed phi2 ->
      evar_open m X (bsvar_subst phi1 phi2 dbi)
      = bsvar_subst (evar_open m X phi1) phi2 dbi.
  Proof.
    intro H. apply bevar_subst_bsvar_subst; auto.
  Qed.

  Corollary svar_open_bevar_subst m phi1 phi2 dbi X
    : well_formed_closed phi2 ->
      svar_open m X (bevar_subst phi1 phi2 dbi)
      = bevar_subst (svar_open m X phi1) phi2 dbi.
  Proof.
    intro H. apply eq_sym, bevar_subst_bsvar_subst; auto.
  Qed.

  Corollary svar_open_bsvar_subst_higher m phi1 phi2 dbi X
    : well_formed_closed phi2 ->
      m < dbi ->
      svar_open m X (bsvar_subst phi1 phi2 dbi)
      = bsvar_subst (svar_open m X phi1) phi2 (pred dbi).
  Proof.
    intros H H0. apply bsvar_subst_comm_higher; auto.
    unfold well_formed_closed in *. destruct_and!. auto.
  Qed.

  Corollary svar_open_bsvar_subst_lower m phi1 phi2 dbi X
    : well_formed_closed phi2 ->
      m > dbi ->
      svar_open m X (bsvar_subst phi1 phi2 dbi)
      = bsvar_subst (svar_open (S m) X phi1) phi2 dbi.
  Proof.
    intros H H0. apply bsvar_subst_comm_lower; auto.
    unfold well_formed_closed in *. destruct_and!. auto.
  Qed.

  Corollary evar_open_bevar_subst_higher m phi1 phi2 dbi X
    : well_formed_closed_ex_aux phi2 0 ->
      m < dbi ->
      evar_open m X (bevar_subst phi1 phi2 dbi)
      = bevar_subst (evar_open m X phi1) phi2 (pred dbi).
  Proof.
    intros H H0. apply bevar_subst_comm_higher; auto.
  Qed.

  Corollary evar_open_bevar_subst_lower m phi1 phi2 dbi X
    : well_formed_closed phi2 ->
      m > dbi ->
      evar_open m X (bevar_subst phi1 phi2 dbi)
      = bevar_subst (evar_open (S m) X phi1) phi2 dbi.
  Proof.
    intros H H0. apply bevar_subst_comm_lower; auto.
    unfold well_formed_closed in *. destruct_and!. auto.
  Qed.

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

  Lemma free_svars_bsvar_subst' :
    forall φ ψ dbi X,
      (X ∈ free_svars (bsvar_subst φ ψ dbi)) <->
      ((X ∈ (free_svars ψ) /\ bsvar_occur φ dbi) \/ (X ∈ (free_svars φ))).
  Proof.
    induction φ; intros ψ dbi X; simpl.
    - split; intros H; auto.
      destruct H.
      destruct H. congruence. assumption.
    - split; intros H; auto.
      destruct H; auto.
      destruct H; congruence.
    - split; intros H; auto.
      destruct H; auto.
      destruct H; congruence.
    - case_match; split; intros H.
      + simpl in H. set_solver.
      + destruct H.
        * destruct H; auto. case_match; auto; subst. lia. congruence.
        * set_solver.
      + left. split; auto. case_match; auto.
      + simpl in H. set_solver.
      + simpl in H. set_solver.
      + destruct H.
        * destruct H. case_match; try lia; congruence.
        * set_solver.
    - split; intros H; auto.
      destruct H.
      + destruct H. congruence.
      + set_solver.
    - rewrite elem_of_union.
      rewrite elem_of_union.
      rewrite IHφ1.
      rewrite IHφ2.
      split; intros H.
      + destruct H.
        * destruct H.
          -- left. destruct H.
             split; auto. rewrite H0. auto.
          -- right. left. assumption.
        * destruct H.
          -- left. destruct H.
             split; auto. rewrite H0. apply orbT.
          -- right. right. assumption.
      + destruct H.
        * destruct H as [H1 H2].
          destruct (decide (bsvar_occur φ1 dbi)).
          -- left. left. split; assumption.
          -- destruct (decide (bsvar_occur φ2 dbi)).
             2: { apply orb_prop in H2. destruct H2.
                  rewrite H in n. congruence.
                  rewrite H in n0. congruence.
             }
             right.
             left. split; assumption.
        * destruct H.
          -- left. right. assumption.
          -- right. right. assumption.
    - split; intros H; auto.
      destruct H.
      + destruct H. congruence.
      + set_solver.
    - rewrite elem_of_union.
      rewrite elem_of_union.
      rewrite IHφ1.
      rewrite IHφ2.
      split; intros H.
      + destruct H.
        * destruct H.
          -- left. destruct H.
             split; auto. rewrite H0. auto.
          -- right. left. assumption.
        * destruct H.
          -- left. destruct H.
             split; auto. rewrite H0. apply orbT.
          -- right. right. assumption.
      + destruct H.
        * destruct H as [H1 H2].
          destruct (decide (bsvar_occur φ1 dbi)).
          -- left. left. split; assumption.
          -- destruct (decide (bsvar_occur φ2 dbi)).
             2: { apply orb_prop in H2. destruct H2.
                  rewrite H in n. congruence.
                  rewrite H in n0. congruence.
             }
             right.
             left. split; assumption.
        * destruct H.
          -- left. right. assumption.
          -- right. right. assumption.
    - rewrite IHφ. auto.
    - rewrite IHφ. auto.
  Qed.

  Lemma free_evars_bevar_subst' :
    forall φ ψ dbi X,
      (X ∈ free_evars (bevar_subst φ ψ dbi)) <->
      ((X ∈ (free_evars ψ) /\ bevar_occur φ dbi) \/ (X ∈ (free_evars φ))).
  Proof.
    induction φ; intros ψ dbi X; simpl.
    - split; intros H; auto.
      destruct H.
      destruct H. congruence. assumption.
    - split; intros H; auto.
      destruct H; auto.
      destruct H; congruence.
    - case_match; split; intros H.
      + simpl in H. set_solver.
      + destruct H.
        * destruct H; auto. case_match; auto; subst. lia. congruence.
        * set_solver.
      + left. split; auto. case_match; auto.
      + simpl in H. set_solver.
      + simpl in H. set_solver.
      + destruct H.
        * destruct H. case_match; try lia; congruence.
        * set_solver.
    - split; intros H; auto.
      destruct H; auto.
      destruct H; congruence.
    - split; intros H; auto.
      destruct H.
      + destruct H. congruence.
      + set_solver.
    - rewrite elem_of_union.
      rewrite elem_of_union.
      rewrite IHφ1.
      rewrite IHφ2.
      split; intros H.
      + destruct H.
        * destruct H.
          -- left. destruct H.
             split; auto. rewrite H0. auto.
          -- right. left. assumption.
        * destruct H.
          -- left. destruct H.
             split; auto. rewrite H0. apply orbT.
          -- right. right. assumption.
      + destruct H.
        * destruct H as [H1 H2].
          destruct (decide (bevar_occur φ1 dbi)).
          -- left. left. split; assumption.
          -- destruct (decide (bevar_occur φ2 dbi)).
             2: { apply orb_prop in H2. destruct H2.
                  rewrite H in n. congruence.
                  rewrite H in n0. congruence.
             }
             right.
             left. split; assumption.
        * destruct H.
          -- left. right. assumption.
          -- right. right. assumption.
    - split; intros H; auto.
      destruct H.
      + destruct H. congruence.
      + set_solver.
    - rewrite elem_of_union.
      rewrite elem_of_union.
      rewrite IHφ1.
      rewrite IHφ2.
      split; intros H.
      + destruct H.
        * destruct H.
          -- left. destruct H.
             split; auto. rewrite H0. auto.
          -- right. left. assumption.
        * destruct H.
          -- left. destruct H.
             split; auto. rewrite H0. apply orbT.
          -- right. right. assumption.
      + destruct H.
        * destruct H as [H1 H2].
          destruct (decide (bevar_occur φ1 dbi)).
          -- left. left. split; assumption.
          -- destruct (decide (bevar_occur φ2 dbi)).
             2: { apply orb_prop in H2. destruct H2.
                  rewrite H in n. congruence.
                  rewrite H in n0. congruence.
             }
             right.
             left. split; assumption.
        * destruct H.
          -- left. right. assumption.
          -- right. right. assumption.
    - rewrite IHφ. auto.
    - rewrite IHφ. auto.
  Qed.


  Lemma free_svars_bsvar_subst :
    forall φ ψ dbi,
    free_svars (bsvar_subst φ ψ dbi) ⊆ union (free_svars ψ) (free_svars φ).
  Proof.
    induction φ; intros ψ dbi; simpl; try set_solver.
    case_match; simpl; set_solver.
  Qed.

  Lemma free_evars_bevar_subst :
    forall φ ψ dbi,
    free_evars (bevar_subst φ ψ dbi) ⊆ union (free_evars ψ) (free_evars φ).
  Proof.
    induction φ; intros ψ dbi Hwf; simpl; try set_solver.
    case_match; simpl; set_solver.
  Qed.

  Lemma free_svars_svar_open'' :
    forall φ dbi X Y,
      (X ∈ free_svars (svar_open dbi Y φ)) <->
      (((X = Y) /\ (bsvar_occur φ dbi)) \/ (X ∈ (free_svars φ))).
  Proof.
    intros φ dbi X Y.
    unfold svar_open.
    pose proof (Htmp := free_svars_bsvar_subst' φ (patt_free_svar Y) dbi X).
    simpl in Htmp.
    assert (X ∈ @singleton _ SVarSet _ Y <-> X = Y) by set_solver.
    tauto.
  Qed.

  Corollary free_svars_svar_open ϕ X dbi :
    free_svars (svar_open dbi X ϕ) ⊆ union (singleton X) (free_svars ϕ).
  Proof.
    apply free_svars_bsvar_subst; auto.
  Qed.

  Lemma free_evars_evar_open'' :
    forall φ dbi x y,
      (x ∈ free_evars (evar_open dbi y φ)) <->
      ((x = y /\ bevar_occur φ dbi) \/ (x ∈ (free_evars φ))).
  Proof.
    intros φ dbi x y.
    unfold evar_open.
    pose proof (Htmp := free_evars_bevar_subst' φ (patt_free_evar y) dbi x).
    simpl in Htmp.
    assert (x ∈ @singleton _ EVarSet _ y <-> x = y) by set_solver;
    tauto.
  Qed.

  Corollary free_evars_evar_open ϕ x dbi :
    free_evars (evar_open dbi x ϕ) ⊆ union (singleton x) (free_evars ϕ).
  Proof.
    apply free_evars_bevar_subst; auto.
  Qed.

  Lemma free_evars_evar_open' ϕ x dbi:
    free_evars ϕ ⊆ free_evars (evar_open dbi x ϕ).
  Proof.
    move: dbi.
    induction ϕ; intros dbi; simpl; try apply empty_subseteq.
    - apply PreOrder_Reflexive.
    - apply union_least.
      + eapply PreOrder_Transitive. apply IHϕ1.
        apply union_subseteq_l.
      + eapply PreOrder_Transitive. apply IHϕ2.
        apply union_subseteq_r.
    - apply union_least.
      + eapply PreOrder_Transitive. apply IHϕ1.
        apply union_subseteq_l.
      + eapply PreOrder_Transitive. apply IHϕ2.
        apply union_subseteq_r.
    - set_solver.
    - set_solver.
  Qed.

  Corollary svar_is_fresh_in_svar_open X Y dbi ϕ:
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

  Corollary evar_is_fresh_in_evar_open x y dbi ϕ:
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

  Fixpoint count_evar_occurrences (x : evar) (p : Pattern) :=
    match p with
    | patt_free_evar x' => if decide (x' = x) is left _ then 1 else 0 
    | patt_free_svar _ => 0
    | patt_bound_evar _ => 0
    | patt_bound_svar _ => 0
    | patt_sym _ => 0
    | patt_app phi1 phi2 => count_evar_occurrences x phi1 + count_evar_occurrences x phi2 
    | patt_bott => 0
    | patt_imp phi1 phi2 => count_evar_occurrences x phi1 + count_evar_occurrences x phi2 
    | patt_exists phi' => count_evar_occurrences x phi'
    | patt_mu phi' => count_evar_occurrences x phi'
    end.

  Lemma count_evar_occurrences_0 (x : evar) (p : Pattern) :
    x ∉ free_evars p ->
    count_evar_occurrences x p = 0.
  Proof.
    intros H.
    induction p; simpl in H; simpl; auto.
    - apply not_elem_of_singleton_1 in H.
      destruct (decide (x0 = x)). subst. contradiction. reflexivity.
    - apply not_elem_of_union in H. destruct H as [H1 H2].
      rewrite IHp1; [assumption|].
      rewrite IHp2; [assumption|].
      reflexivity.
    - apply not_elem_of_union in H. destruct H as [H1 H2].
      rewrite IHp1; [assumption|].
      rewrite IHp2; [assumption|].
      reflexivity.
  Qed.

(* TODO: deprecated

  Lemma nest_ex_aux_comm n more more' p:
    nest_ex_aux (n + more) more' (nest_ex_aux n more p) = nest_ex_aux n (more + more') p.
  Proof.
    move: n more more'.
    induction p; intros n' more more'; simpl; auto.
    - f_equal.
      repeat case_match; auto; try lia.
    - by rewrite IHp1 IHp2.
    - by rewrite IHp1 IHp2.
    - replace (S (n' + more)) with ((S n') + more) by lia.
        by rewrite IHp.
    - by rewrite IHp.
  Qed.

  Lemma nest_mu_aux_comm n more more' p:
    nest_mu_aux (n + more) more' (nest_mu_aux n more p) = nest_mu_aux n (more + more') p.
  Proof.
    move: n more more'.
    induction p; intros n' more more'; simpl; auto.
    - f_equal.
      repeat case_match; auto; try lia.
    - by rewrite IHp1 IHp2.
    - by rewrite IHp1 IHp2.
    - by rewrite IHp.
    - replace (S (n' + more)) with ((S n') + more) by lia.
        by rewrite IHp.
  Qed. *)

  Lemma free_evar_subst_no_occurrence x p q:
    count_evar_occurrences x p = 0 ->
    free_evar_subst p q x = p.
  Proof.
    intros H.
    remember (size' p) as sz.
    assert (Hsz: size' p <= sz) by lia.
    clear Heqsz.

    move: p Hsz H.
    induction sz; intros p Hsz H; destruct p; simpl in *; try lia; auto.
    - simpl in H. simpl.
      destruct (decide (x = x0)).
      + subst x0. destruct (decide (x = x)). simpl in H. inversion H. contradiction.
      + reflexivity.
    - rewrite IHsz. lia. lia. rewrite IHsz. lia. lia. reflexivity.
    - rewrite IHsz. lia. lia. rewrite IHsz. lia. lia. reflexivity.
    - f_equal. rewrite IHsz. lia. exact H. reflexivity.
    - rewrite IHsz; auto. lia.
  Qed.


  Lemma wfc_impl_no_neg_pos_occ p m:
    well_formed_closed_mu_aux p m ->
    (no_negative_occurrence_db_b m p && no_positive_occurrence_db_b m p) = true.
  Proof.
    intros H.
    move: m H.
    induction p; intros m H; simpl; simpl in H; auto.
    - repeat case_match; try reflexivity; try lia. congruence.
    - apply andb_prop in H. destruct H as [H1 H2].
      specialize (IHp1 m H1). specialize (IHp2 m H2).
      destruct_and!. split_and!; assumption.
    - apply andb_prop in H. destruct H as [H1 H2].
      specialize (IHp1 m H1). specialize (IHp2 m H2).
      destruct_and!. split_and!; assumption.
  Qed.

  Record PatternCtx : Type :=
    { pcEvar : evar ;
      pcPattern : Pattern;
    }.

  Definition is_linear_context (C : PatternCtx) := count_evar_occurrences (pcEvar C) (pcPattern C) = 1.

  Definition PC_wf C := well_formed (pcPattern C).

  Definition emplace (ctx : PatternCtx) (p : Pattern) : Pattern :=
    free_evar_subst (pcPattern ctx) p (pcEvar ctx).

  (* TODO make Set ? *)
  Inductive Application_context : Type :=
  | box
  | ctx_app_l (cc : Application_context) (p : Pattern) (Prf : well_formed p)
  | ctx_app_r (p : Pattern) (cc : Application_context) (Prf : well_formed p)
  .

  Fixpoint AC_free_evars (AC : Application_context) : EVarSet :=
    match AC with
    | box => ∅
    | @ctx_app_l cc p _ => free_evars p ∪ AC_free_evars cc
    | @ctx_app_r p cc _ => free_evars p ∪ AC_free_evars cc
    end.

  Fixpoint subst_ctx (C : Application_context) (p : Pattern)
    : Pattern :=
    match C with
    | box => p
    | @ctx_app_l C' p' prf => patt_app (subst_ctx C' p) p'
    | @ctx_app_r p' C' prf => patt_app p' (subst_ctx C' p)
    end.

  (* TODO rewrite using wc_sctx *)
  Lemma wf_sctx (C : Application_context) (A : Pattern) :
    well_formed A = true -> well_formed (subst_ctx C A) = true.
  Proof.
    intros H.
    unfold well_formed in H.
    apply andb_true_iff in H. destruct H as [Hwfp Hwfc].
    unfold well_formed_closed in Hwfc.
    induction C; simpl.
    - unfold well_formed. rewrite Hwfp. unfold well_formed_closed. rewrite Hwfc. reflexivity.
    - unfold well_formed. simpl.
      unfold well_formed in IHC. apply andb_true_iff in IHC. destruct IHC as [IHC1 IHC2].
      rewrite IHC1. simpl.
      unfold well_formed in Prf. apply andb_true_iff in Prf. destruct Prf as [Prf1 Prf2].
      rewrite Prf1. simpl.
      unfold well_formed_closed in *. simpl.
      destruct_and!. split_and!; auto.
    - unfold well_formed,well_formed_closed in *. simpl in *.
      destruct_and!. split_and!; auto.
  Qed.

  Lemma wp_sctx (C : Application_context) (A : Pattern) :
    well_formed_positive A = true -> well_formed_positive (subst_ctx C A) = true.
  Proof.
    intros H.
    induction C.
    - auto.
    - simpl. rewrite IHC. simpl.
      unfold well_formed in Prf. apply andb_true_iff in Prf. destruct Prf. exact H0.
    - simpl. unfold well_formed in Prf. apply andb_true_iff in Prf.
      destruct Prf. rewrite H0. rewrite IHC. reflexivity.
  Qed.

  Lemma wcex_sctx (C : Application_context) (A : Pattern) idx1 :
    well_formed_closed_ex_aux A idx1 = true -> well_formed_closed_ex_aux (subst_ctx C A) idx1 = true.
  Proof.
    intros H.
    induction C.
    - auto.
    - simpl. rewrite IHC. simpl.
      unfold well_formed,well_formed_closed in *.
      destruct_and!.
      eapply well_formed_closed_ex_aux_ind. 2: eassumption. lia.
    - simpl. rewrite IHC.
      unfold well_formed,well_formed_closed in *.
      destruct_and!. split_and!; auto.
      eapply well_formed_closed_ex_aux_ind. 2: eassumption. lia.
  Qed.

  Lemma wcmu_sctx (C : Application_context) (A : Pattern) idx1 :
    well_formed_closed_mu_aux A idx1 = true -> well_formed_closed_mu_aux (subst_ctx C A) idx1 = true.
  Proof.
    intros H.
    induction C.
    - auto.
    - simpl. rewrite IHC. simpl.
      unfold well_formed,well_formed_closed in *.
      destruct_and!.
      eapply well_formed_closed_mu_aux_ind. 2: eassumption. lia.
    - simpl. rewrite IHC.
      unfold well_formed,well_formed_closed in *.
      destruct_and!. split_and!; auto.
      eapply well_formed_closed_mu_aux_ind. 2: eassumption. lia.
  Qed.
  
  Fixpoint free_evars_ctx (C : Application_context)
    : (EVarSet) :=
    match C with
    | box => empty
    | @ctx_app_l cc p prf => union (free_evars_ctx cc) (free_evars p)
    | @ctx_app_r p cc prf => union (free_evars p) (free_evars_ctx cc)
    end.


  Definition ApplicationContext2Pattern (boxvar : evar) (AC : Application_context) :=
    subst_ctx AC (patt_free_evar boxvar).

  Lemma ApplicationContext2Pattern_one_occ (AC : Application_context) (boxvar : evar):
    boxvar ∉ free_evars_ctx AC ->
    count_evar_occurrences boxvar (ApplicationContext2Pattern boxvar AC) = 1.
  Proof.
    intros H.
    induction AC; simpl.
    - destruct (decide (boxvar = boxvar)). reflexivity. contradiction.
    - simpl in H. apply not_elem_of_union in H. 
      rewrite IHAC.
      { exact (proj1 H). }
      simpl in H.
      rewrite count_evar_occurrences_0. 2: lia.
      exact (proj2 H).
    - simpl in H. apply not_elem_of_union in H. 
      rewrite IHAC.
      { exact (proj2 H). }
      simpl in H.
      rewrite count_evar_occurrences_0. 2: lia.
      exact (proj1 H).
  Qed.

  Program Definition ApplicationContext2PatternCtx'
             (boxvar : evar)
             (AC : Application_context)
             (pf : boxvar ∉ free_evars_ctx AC)
    : PatternCtx :=
    {|
    pcEvar := boxvar;
    pcPattern := ApplicationContext2Pattern boxvar AC;
    |}.

  Lemma AC2PC'_wf boxvar AC pf: PC_wf (@ApplicationContext2PatternCtx' boxvar AC pf).
  Proof.
    unfold PC_wf. apply wf_sctx. reflexivity.
  Qed.

  Definition ApplicationContext2PatternCtx (AC : Application_context) : PatternCtx :=
    let boxvar := (evar_fresh (elements (free_evars_ctx AC))) in
    @ApplicationContext2PatternCtx' boxvar AC (@set_evar_fresh_is_fresh' _).

  Lemma AC2PC_wf AC: PC_wf (ApplicationContext2PatternCtx AC).
  Proof.
    apply AC2PC'_wf.
  Defined.
  
  
  Definition is_application (p : Pattern) : bool :=
    match p with
    | patt_app _ _ => true
    | _ => false
    end.

  Definition is_free_evar (p : Pattern) : bool :=
    match p with
    | patt_free_evar _ => true
    | _ => false
    end.

  Definition is_application_or_free_evar (p : Pattern) : bool :=
    is_application p || is_free_evar p.

  Lemma ApplicationContext2PatternCtx_is_application (AC : Application_context) :
    let p := pcPattern (ApplicationContext2PatternCtx AC) in
    is_application_or_free_evar p = true.
  Proof.
    destruct AC; reflexivity.
  Qed.

  Definition is_application_or_free_evar_x (x : evar) (p : Pattern)  : bool :=
    is_application p ||
                   (match p with
                    | patt_free_evar x' => if decide (x' = x) is left _ then true else false
                    | _ => false
                    end).

  Fixpoint PatternCtx2ApplicationContext'
           (box_evar : evar)
           (p : Pattern)
           (wf : well_formed p)
    : Application_context :=
    (match p as q return well_formed q -> Application_context with
     | patt_app p1 p2 =>
       fun wf =>
      if decide (count_evar_occurrences box_evar p1 = 0) is left _ then
        @ctx_app_r p1 (@PatternCtx2ApplicationContext' box_evar p2 (well_formed_app_2 wf)) (well_formed_app_1 wf)
      else if decide (count_evar_occurrences box_evar p2 = 0) is left _ then
             @ctx_app_l (@PatternCtx2ApplicationContext' box_evar p1 (well_formed_app_1 wf)) p2 (well_formed_app_2 wf)
           else
             box
    | _ => fun _ => box
    end
    ) wf
  .
  

  Definition PatternCtx2ApplicationContext (C : PatternCtx) (pf: PC_wf C) : Application_context :=
    @PatternCtx2ApplicationContext' (pcEvar C) (pcPattern C) pf.

  Lemma count_evar_occurrences_subst_ctx AC x:
    x ∉ free_evars_ctx AC ->
    count_evar_occurrences x (subst_ctx AC (patt_free_evar x)) = 1.
  Proof.
    intros H.
    induction AC; simpl.
    - destruct (decide (x = x)); [reflexivity|contradiction].
    - simpl in H. apply not_elem_of_union in H.
      rewrite IHAC;[exact (proj1 H)|].
      rewrite count_evar_occurrences_0; [exact (proj2 H)|].
      reflexivity.
    - simpl in H. apply not_elem_of_union in H.
      rewrite IHAC;[exact (proj2 H)|].
      rewrite count_evar_occurrences_0; [exact (proj1 H)|].
      reflexivity.
  Qed.
  
  Lemma ApplicationContext2PatternCtx2ApplicationContext'
        (boxvar : evar)
        (AC : Application_context)
        (Hnotin: boxvar ∉ free_evars_ctx AC) :
    let C : PatternCtx := @ApplicationContext2PatternCtx' boxvar AC Hnotin in
    let pf := AC2PC'_wf Hnotin in
    PatternCtx2ApplicationContext' boxvar pf = AC.
  Proof.
    simpl.
    move: (AC2PC'_wf Hnotin).
    move: boxvar Hnotin.
    
    induction AC; intros boxvar Hnotin pf.
    - reflexivity.
    - simpl.
      simpl in Hnotin.
      pose proof (Hnotin' := Hnotin).
      apply not_elem_of_union in Hnotin'.
      destruct Hnotin' as [HnotinAC Hnotinp].
      assert (Hcount1: count_evar_occurrences boxvar (subst_ctx AC (patt_free_evar boxvar)) = 1).
      { rewrite count_evar_occurrences_subst_ctx; [exact HnotinAC|reflexivity]. }
      rewrite Hcount1.
      destruct (decide (1 = 0)); [inversion e|simpl].
      clear n.

      assert (HoneOcc : count_evar_occurrences boxvar (ApplicationContext2Pattern boxvar (ctx_app_l AC Prf)) = 1).
      { apply ApplicationContext2Pattern_one_occ. simpl. exact Hnotin. }
      simpl in HoneOcc.
      rewrite Hcount1 in HoneOcc.
      assert (Hcount0: count_evar_occurrences boxvar p = 0).
      { lia. }
      rewrite Hcount0.
      destruct (decide (0 = 0)). 2: contradiction. simpl. clear e.
      f_equal.
      2: { apply proof_irrelevance. }
      rewrite IHAC;[assumption|reflexivity].
    - simpl.
      simpl in Hnotin.
      pose proof (Hnotin' := Hnotin).
      apply not_elem_of_union in Hnotin'.
      destruct Hnotin' as [Hnotinp HnotinAC].

      assert (HoneOcc : count_evar_occurrences boxvar (ApplicationContext2Pattern boxvar (ctx_app_r AC Prf)) = 1).
      { apply ApplicationContext2Pattern_one_occ. simpl. exact Hnotin. }
      
      assert (Hcount1: count_evar_occurrences boxvar (subst_ctx AC (patt_free_evar boxvar)) = 1).
      { rewrite count_evar_occurrences_subst_ctx; [exact HnotinAC|reflexivity]. }

      simpl in HoneOcc.
      rewrite Hcount1 in HoneOcc.
      assert (Hcount0: count_evar_occurrences boxvar p = 0).
      { lia. }

      rewrite Hcount0.
      destruct (decide (0 = 0)). 2: contradiction. simpl. clear e.

      f_equal.
      2: { apply proof_irrelevance. }
      rewrite IHAC;[assumption|reflexivity].
  Qed.

  Lemma ApplicationContext2PatternCtx2ApplicationContext (AC : Application_context) :
    PatternCtx2ApplicationContext (AC2PC_wf AC) = AC.
  Proof.
    unfold PatternCtx2ApplicationContext, ApplicationContext2PatternCtx.
    unfold AC2PC_wf.
    apply ApplicationContext2PatternCtx2ApplicationContext'.
  Qed.

  Fixpoint is_implicative_context' (box_evar : evar) (phi : Pattern) : bool :=
    match phi with
    | patt_bott => true
    | patt_free_evar _ => true
    | patt_imp phi1 phi2 =>
      (if decide(count_evar_occurrences box_evar phi1 <> 0) is left _
       then is_implicative_context' box_evar phi1 else true) &&
      (if decide(count_evar_occurrences box_evar phi2 <> 0) is left _
       then is_implicative_context' box_evar phi2 else true)
    | _ => false
    end.

  Definition is_implicative_context (C : PatternCtx) :=
    is_implicative_context' (pcEvar C) (pcPattern C).
    

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
    - case_match; subst.
      + case_match; try lia. constructor. reflexivity.
      + congruence.
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

  Lemma bevar_subst_contains_subformula ϕ₁ ϕ₂ dbi :
    bevar_occur ϕ₁ dbi = true ->
    is_subformula_of_ind ϕ₂ (bevar_subst ϕ₁ ϕ₂ dbi).
  Proof.
    generalize dependent dbi.
    induction ϕ₁; intros dbi H; simpl; simpl in H; try inversion H.
    - case_match; subst.
      + case_match; try lia. constructor. reflexivity.
      + congruence.
    - specialize (IHϕ₁1 dbi). specialize (IHϕ₁2 dbi).
      move: H H1 IHϕ₁1 IHϕ₁2.
      case: (bevar_occur ϕ₁1 dbi); case: (bevar_occur ϕ₁2 dbi); move=> H H1 IHϕ₁₁ IHϕ₁₂.
      + apply sub_app_l. auto.
      + apply sub_app_l. auto.
      + apply sub_app_r. auto.
      + done.
    - specialize (IHϕ₁1 dbi). specialize (IHϕ₁2 dbi).
      move: H H1 IHϕ₁1 IHϕ₁2.
      case: (bevar_occur ϕ₁1 dbi); case: (bevar_occur ϕ₁2 dbi); move=> H H1 IHϕ₁₁ IHϕ₁₂.
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
    2: { simpl. lia. }
    cbn. case_match; reflexivity.
  Qed.

  Corollary bsvar_occur_evar_open dbi1 dbi2 X phi:
    bsvar_occur phi dbi1 = false ->
    bsvar_occur (evar_open dbi2 X phi) dbi1 = false.
  Proof.
    apply Private_bsvar_occur_evar_open with (sz := size phi). lia.
  Qed.

  Lemma Private_bevar_occur_svar_open sz dbi1 dbi2 X phi:
    size phi <= sz ->
    bevar_occur phi dbi1 = false ->
    bevar_occur (svar_open dbi2 X phi) dbi1 = false.
  Proof.
    move: phi dbi1 dbi2.
    induction sz; move=> phi; destruct phi; simpl; move=> dbi1 dbi2 Hsz H; try rewrite !IHsz; auto; try lia; try apply orb_false_elim in H; firstorder.
    { cbn. case_match; reflexivity. }
    simpl. lia.
  Qed.

  Corollary bevar_occur_svar_open dbi1 dbi2 X phi:
    bevar_occur phi dbi1 = false ->
    bevar_occur (svar_open dbi2 X phi) dbi1 = false.
  Proof.
    apply Private_bevar_occur_svar_open with (sz := size phi). lia.
  Qed.

  Lemma Private_bevar_occur_evar_open sz dbi1 dbi2 X phi:
    size phi <= sz -> dbi1 < dbi2 ->
    bevar_occur phi dbi1 = false ->
    bevar_occur (evar_open dbi2 X phi) dbi1 = false.
  Proof.
    move: phi dbi1 dbi2.
    induction sz; move=> phi; destruct phi; simpl; move=> dbi1 dbi2 Hsz H H1; try rewrite !IHsz; auto; try lia; try apply orb_false_elim in H1; firstorder.
    { cbn. repeat case_match; simpl; auto; try lia. rewrite Heqs. reflexivity.
      case_match; try lia. }
    simpl. lia.
 Qed.

  Corollary bevar_occur_evar_open dbi1 dbi2 X phi:
    bevar_occur phi dbi1 = false -> dbi1 < dbi2 ->
    bevar_occur (evar_open dbi2 X phi) dbi1 = false.
  Proof.
    intros H H0. apply Private_bevar_occur_evar_open with (sz := size phi); auto.
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

  Corollary evar_fresh_svar_open x X dbi ϕ:
    evar_is_fresh_in x ϕ ->
    evar_is_fresh_in x (svar_open dbi X ϕ).
  Proof.
    unfold evar_is_fresh_in.
      by rewrite free_evars_svar_open.
  Qed.

  Corollary svar_fresh_evar_open x X dbi ϕ:
    svar_is_fresh_in X ϕ ->
    svar_is_fresh_in X (evar_open dbi x ϕ).
  Proof.
    unfold svar_is_fresh_in.
      by rewrite free_svars_evar_open.
  Qed.

  Corollary evar_fresh_in_subformula x ϕ₁ ϕ₂ :
    is_subformula_of_ind ϕ₁ ϕ₂ ->
    evar_is_fresh_in x ϕ₂ ->
    evar_is_fresh_in x ϕ₁.
  Proof.
    unfold evar_is_fresh_in.
    intros Hsub Hfresh.
    apply free_evars_subformula in Hsub.
    auto.
  Qed.

  Corollary evar_fresh_in_subformula' x ϕ₁ ϕ₂ :
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

  Corollary svar_fresh_in_subformula x ϕ₁ ϕ₂ :
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
    - case_match; set_solver.
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

  Lemma free_svars_bevar_subst ϕ₁ ϕ₂ dbi:
    free_svars (bevar_subst ϕ₁ ϕ₂ dbi) ⊆ free_svars ϕ₁ ∪ free_svars ϕ₂.
  Proof.
    generalize dependent dbi.
    induction ϕ₁; intros db; simpl.
    - apply empty_subseteq.
    - apply union_subseteq_l.
    - case_match; set_solver.
    - apply empty_subseteq.
    - apply empty_subseteq.
    - specialize (IHϕ₁1 db).
      specialize (IHϕ₁2 db).
      remember (free_svars (bevar_subst ϕ₁1 ϕ₂ db)) as A1.
      remember (free_svars (bevar_subst ϕ₁2 ϕ₂ db)) as A2.
      remember (free_svars ϕ₁1) as B1.
      remember (free_svars ϕ₁2) as B2.
      remember (free_svars ϕ₂) as C.
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
      remember (free_svars (bevar_subst ϕ₁1 ϕ₂ db)) as A1.
      remember (free_svars (bevar_subst ϕ₁2 ϕ₂ db)) as A2.
      remember (free_svars ϕ₁1) as B1.
      remember (free_svars ϕ₁2) as B2.
      remember (free_svars ϕ₂) as C.
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

  Lemma free_svars_bevar_subst_1 ϕ₁ ϕ₂ dbi:
    free_svars ϕ₁ ⊆ free_svars (bevar_subst ϕ₁ ϕ₂ dbi).
  Proof.
    generalize dependent dbi.
    induction ϕ₁; intros dbi; simpl; try apply reflexivity.
    - apply empty_subseteq.
    - apply union_mono; auto.
    - apply union_mono; auto.
    - auto.
    - auto.
  Qed.

  Corollary free_evars_bsvar_subst_eq ϕ₁ ϕ₂ dbi:
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

  Corollary free_svars_bevar_subst_eq ϕ₁ ϕ₂ dbi:
    bevar_occur ϕ₁ dbi ->
    free_svars (bevar_subst ϕ₁ ϕ₂ dbi) = free_svars ϕ₁ ∪ free_svars ϕ₂.
  Proof.
    intros H.
    apply (anti_symm subseteq).
    - apply free_svars_bevar_subst.
    - apply union_least.
      + apply free_svars_bevar_subst_1.
      + pose proof (Hsub := @bevar_subst_contains_subformula ϕ₁ ϕ₂ dbi H).
        apply free_svars_subformula. auto.
  Qed.

  Lemma bsvar_subst_not_occur_is_noop ϕ₁ ϕ₂ dbi:
    bsvar_occur ϕ₁ dbi = false -> well_formed_closed_mu_aux ϕ₁ dbi ->
    bsvar_subst ϕ₁ ϕ₂ dbi = ϕ₁.
  Proof.
    generalize dependent dbi.
    induction ϕ₁; intros dbi H; simpl; simpl in H; auto.
    - case_match; [congruence|].
      case_match; intros. 2: congruence. case_match; try lia; auto.
    - intros H0. apply orb_false_iff in H as [H1 H2]. apply andb_true_iff in H0 as [H01 H02].
      rewrite -> IHϕ₁1. 2: auto.
      rewrite -> IHϕ₁2. 2: auto.
      all: auto.
    - intros H0. apply orb_false_iff in H as [H1 H2]. apply andb_true_iff in H0 as [H01 H02].
      rewrite -> IHϕ₁1. 2: auto.
      rewrite -> IHϕ₁2. 2: auto.
      all: auto.
    - intro H0. rewrite -> IHϕ₁. all: auto.
    - intro H0. rewrite -> IHϕ₁. all: auto.
  Qed.

  Lemma bevar_subst_not_occur_is_noop ϕ₁ ϕ₂ dbi:
    bevar_occur ϕ₁ dbi = false -> well_formed_closed_ex_aux ϕ₁ dbi ->
    bevar_subst ϕ₁ ϕ₂ dbi = ϕ₁.
  Proof.
    generalize dependent dbi.
    induction ϕ₁; intros dbi H; simpl; simpl in H; auto.
    - case_match; [congruence|].
      case_match; intros. 2: congruence. case_match; try lia; auto.
    - intros H0. apply orb_false_iff in H as [H1 H2]. apply andb_true_iff in H0 as [H01 H02].
      rewrite -> IHϕ₁1. 2: auto.
      rewrite -> IHϕ₁2. 2: auto.
      all: auto.
    - intros H0. apply orb_false_iff in H as [H1 H2]. apply andb_true_iff in H0 as [H01 H02].
      rewrite -> IHϕ₁1. 2: auto.
      rewrite -> IHϕ₁2. 2: auto.
      all: auto.
    - intro H0. rewrite -> IHϕ₁. all: auto.
    - intro H0. rewrite -> IHϕ₁. all: auto.
  Qed.

  Corollary svar_open_not_occur_is_noop ϕ₁ X dbi:
    bsvar_occur ϕ₁ dbi = false -> well_formed_closed_mu_aux ϕ₁ dbi ->
    svar_open dbi X ϕ₁ = ϕ₁.
  Proof.
    intro H. now apply bsvar_subst_not_occur_is_noop.
  Qed.

  Lemma wfc_mu_aux_implies_not_bsvar_occur phi ns :
    well_formed_closed_mu_aux phi ns ->
    bsvar_occur phi ns = false.
  Proof.
    move: ns.
    induction phi; intros ns Hwfc; simpl; simpl in Hwfc; auto.
    - repeat case_match; try lia. congruence.
    - apply andb_true_iff in Hwfc.
      destruct Hwfc as [Hwfc1 Hwfc2].
      destruct (bsvar_occur phi1 ns) eqn:Heq1, (bsvar_occur phi2 ns) eqn:Heq2; simpl.
      rewrite IHphi1 in Heq1. assumption. congruence.
      rewrite IHphi1 in Heq1. assumption. congruence.
      rewrite IHphi2 in Heq2. assumption. congruence.
      rewrite IHphi2 in Heq2. assumption. congruence.
    - apply andb_true_iff in Hwfc.
      destruct Hwfc as [Hwfc1 Hwfc2].
      destruct (bsvar_occur phi1 ns) eqn:Heq1, (bsvar_occur phi2 ns) eqn:Heq2; simpl.
      rewrite IHphi1 in Heq1. assumption. congruence.
      rewrite IHphi1 in Heq1. assumption. congruence.
      rewrite IHphi2 in Heq2. assumption. congruence.
      rewrite IHphi2 in Heq2. assumption. congruence.
  Qed.

  Lemma wfc_ex_aux_implies_not_bevar_occur phi ne :
    well_formed_closed_ex_aux phi ne ->
    bevar_occur phi ne = false.
  Proof.
    move: ne.
    induction phi; intros ne Hwfc; simpl; simpl in Hwfc; auto.
    - apply bool_decide_eq_false.
      case_match;[lia|congruence].
    - apply andb_true_iff in Hwfc.
      destruct Hwfc as [Hwfc1 Hwfc2].
      erewrite IHphi1; eauto.
    - apply andb_true_iff in Hwfc.
      destruct Hwfc as [Hwfc1 Hwfc2].
      erewrite IHphi1, IHphi2; eauto.
  Qed.

  Lemma wfc_mu_implies_not_bsvar_occur phi n :
    well_formed_closed_mu_aux phi 0 ->
    ~ bsvar_occur phi n.
  Proof.
    intros H.
    erewrite wfc_mu_aux_implies_not_bsvar_occur. exact notF.
    unfold well_formed_closed in H.
    eapply well_formed_closed_mu_aux_ind.
    2: eassumption. lia.
  Qed.

  Lemma wfc_ex_implies_not_bevar_occur phi n :
    well_formed_closed_ex_aux phi 0 ->
    bevar_occur phi n = false.
  Proof.
    intros H.
    erewrite wfc_ex_aux_implies_not_bevar_occur.
    { reflexivity. }
    eapply well_formed_closed_ex_aux_ind.
    2: apply H.
    lia.
  Qed.

  Lemma not_bsvar_occur_bsvar_subst phi psi n:
    well_formed_closed_mu_aux psi 0 -> well_formed_closed_mu_aux phi n ->
    ~ bsvar_occur (bsvar_subst phi psi n) n.
  Proof.
    move: n.
    induction phi; intros n' H H0; simpl; auto.
    - intros Hcontra.
      case_match.
      + subst. simpl in Hcontra. case_match.
        * lia.
        * congruence.
      + apply wfc_mu_implies_not_bsvar_occur with (n := n') in H. congruence.
      + subst. simpl in Hcontra. inversion H0. case_match.
        * lia.
        * congruence.
    - intros Hcontra.
      destruct (bsvar_occur (bsvar_subst phi1 psi n') n') eqn:Heq1, (bsvar_occur (bsvar_subst phi2 psi n') n') eqn:Heq2.
      + eapply IHphi2; eauto. now apply andb_true_iff in H0.
      + eapply IHphi1; eauto. now apply andb_true_iff in H0.
      + eapply IHphi2; eauto. now apply andb_true_iff in H0.
      + simpl in Hcontra. congruence.
    - intros Hcontra.
      destruct (bsvar_occur (bsvar_subst phi1 psi n') n')
               eqn:Heq1, (bsvar_occur (bsvar_subst phi2 psi n') n') eqn:Heq2.
      + eapply IHphi1; eauto. now apply andb_true_iff in H0.
      + eapply IHphi1; eauto. now apply andb_true_iff in H0.
      + eapply IHphi2; eauto. now apply andb_true_iff in H0.
      + simpl in Hcontra. congruence.
  Qed.

  Lemma not_bsvar_occur_impl_no_neg_occ_and_no_pos_occ phi n:
    ~ bsvar_occur phi n ->
    no_negative_occurrence_db_b n phi && no_positive_occurrence_db_b n phi.
  Proof.
    move: n.
    induction phi; intros n' H; simpl; simpl in H; auto.
    - unfold not in H.
      case_match; auto.
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

  Corollary not_bsvar_occur_impl_pos_occ_db phi n:
    ~ bsvar_occur phi n ->
    no_positive_occurrence_db_b n phi.
  Proof.
    intros H.
    pose proof (H1 := not_bsvar_occur_impl_no_neg_occ_and_no_pos_occ H).
    now apply andb_true_iff in H1.
  Qed.

  Corollary not_bsvar_occur_impl_neg_occ_db phi n:
    ~ bsvar_occur phi n ->
    no_negative_occurrence_db_b n phi.
  Proof.
    intros H.
    pose proof (H1 := not_bsvar_occur_impl_no_neg_occ_and_no_pos_occ H).
    now apply andb_true_iff in H1.
  Qed.

  (* TODO: why is this Private? It can be useful for not only 0 dbi *)
  Lemma Private_wfc_impl_no_neg_pos_occ psi maxsvar dbi:
    well_formed_closed_mu_aux psi maxsvar = true ->
    maxsvar <= dbi ->
    no_negative_occurrence_db_b dbi psi = true
    /\ no_positive_occurrence_db_b dbi psi = true.
  Proof.
    move: dbi maxsvar.
    induction psi; intros dbi maxsvar Hwfc Hleq; simpl; auto.
    - split.
      { auto. }
      simpl in Hwfc.
      repeat case_match; auto.
      subst. lia.
    - split.
      + simpl in Hwfc.
        destruct_and!. split_and!; naive_bsolver auto.
      + simpl in Hwfc.
        destruct_and!. split_and!; naive_bsolver auto.
    - split.
      + simpl in Hwfc.
        destruct_and!. split_and!; naive_bsolver auto.
      + simpl in Hwfc.
        destruct_and!. split_and!; naive_bsolver auto.
    - simpl in Hwfc.
      split_and!; naive_bsolver auto.
    - simpl in Hwfc.
      split_and!; eapply IHpsi.
      1,3: eassumption. all: lia.
  Qed.

  Corollary wfc_impl_no_neg_occ psi dbi:
    well_formed_closed_mu_aux psi 0 = true ->
    no_negative_occurrence_db_b dbi psi = true.
  Proof.
    intros H.
    unfold well_formed_closed in H.
    pose proof (HX := Private_wfc_impl_no_neg_pos_occ).
    specialize (HX psi 0 dbi H).
    simpl in HX.
    specialize (HX ltac:(lia)).
    destruct HX as [HX1 HX2].
    apply HX1.
  Qed.

  Corollary wfc_impl_no_pos_occ psi dbi:
    well_formed_closed_mu_aux psi 0 = true ->
    no_positive_occurrence_db_b dbi psi = true.
  Proof.
    intros H.
    unfold well_formed_closed in H.
    pose proof (HX := Private_wfc_impl_no_neg_pos_occ).
    specialize (HX psi 0 dbi H).
    simpl in HX.
    specialize (HX ltac:(lia)).
    destruct HX as [HX1 HX2].
    apply HX2.
  Qed.

  Lemma no_neg_occ_db_bsvar_subst phi psi dbi1 dbi2:
    well_formed_closed_mu_aux psi 0 = true -> dbi1 < dbi2 ->
    (no_negative_occurrence_db_b dbi1 phi = true ->
     no_negative_occurrence_db_b dbi1 (bsvar_subst phi psi dbi2) = true)
    /\ (no_positive_occurrence_db_b dbi1 phi = true ->
        no_positive_occurrence_db_b dbi1 (bsvar_subst phi psi dbi2) = true).
  Proof.
    intros Hwfcpsi.
    move: dbi1 dbi2.

    induction phi; intros dbi1 dbi2 H; simpl; auto.
    -
      case_match; auto.
      + split; intros H0.
        * apply wfc_impl_no_neg_occ. apply Hwfcpsi.
        * apply wfc_impl_no_pos_occ. apply Hwfcpsi.
      + split; intros H0.
        * auto.
        * repeat case_match. congruence. simpl. case_match; auto. lia.
    - specialize (IHphi1 dbi1 dbi2).
      specialize (IHphi2 dbi1 dbi2).
      destruct (IHphi1 H) as [IHphi11 IHphi12].
      destruct (IHphi2 H) as [IHphi21 IHphi22].
      split; intro H0.
      + eapply elimT in H0.
        2: apply andP.
        destruct H0 as [H1 H2].
        specialize (IHphi11 H1).
        specialize (IHphi21 H2).
        rewrite IHphi11 IHphi21. reflexivity.
      + eapply elimT in H0.
        2: apply andP.
        destruct H0 as [H1 H2].
        specialize (IHphi12 H1).
        specialize (IHphi22 H2).
        rewrite IHphi12 IHphi22. reflexivity.
    - specialize (IHphi1 dbi1 dbi2).
      specialize (IHphi2 dbi1 dbi2).
      destruct (IHphi1 H) as [IHphi11 IHphi12].
      destruct (IHphi2 H) as [IHphi21 IHphi22].
      split; intro H0.
      + eapply elimT in H0.
        2: apply andP.
        destruct H0 as [H1 H2].
        specialize (IHphi12 H1).
        specialize (IHphi21 H2).
        rewrite IHphi12 IHphi21. reflexivity.
      + eapply elimT in H0.
        2: apply andP.
        destruct H0 as [H1 H2].
        specialize (IHphi11 H1).
        specialize (IHphi22 H2).
        rewrite IHphi11 IHphi22. reflexivity.
    - split; intros H0; apply IHphi; auto; lia.
  Qed.


  Lemma Private_wfp_bsvar_subst (phi psi : Pattern) (n : nat) :
    well_formed_positive psi ->
    well_formed_closed_mu_aux psi 0 ->
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
      + intros _. case_match; auto.
      + intros H phi' Hwfphi'.
        do 2 case_match; auto.
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
        apply no_neg_occ_db_bsvar_subst; auto. lia.
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

  Corollary wfp_bsvar_subst (phi psi : Pattern) :
    well_formed_positive (patt_mu phi) ->
    well_formed_positive psi ->
    well_formed_closed_mu_aux psi 0 ->
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

  (*
  TODO: deprecated

  Lemma not_bevar_occur_level_nest_ex_aux level more ϕ :
    more > 0 ->
    bevar_occur (nest_ex_aux level more ϕ) level = false.
  Proof.
    intros Hmore.
    move: ϕ level.
    induction ϕ; move=> level; simpl; auto.
    - repeat case_match; simpl; auto; lia.
    - rewrite IHϕ1. rewrite IHϕ2. simpl. reflexivity.
    - rewrite IHϕ1. rewrite IHϕ2. simpl. reflexivity.
  Qed.

  Lemma not_bsvar_occur_level_nest_mu_aux level more ϕ :
    more > 0 ->
    bsvar_occur (nest_mu_aux level more ϕ) level = false.
  Proof.
    intros Hmore.
    move: ϕ level.
    induction ϕ; move=> level; simpl; auto.
    - repeat case_match; simpl; lia.
    - rewrite IHϕ1. rewrite IHϕ2. simpl. reflexivity.
    - rewrite IHϕ1. rewrite IHϕ2. simpl. reflexivity.
  Qed.

  Lemma nest_ex_aux_wfcex level more ϕ:
    well_formed_closed_ex_aux ϕ level ->
    nest_ex_aux level more ϕ = ϕ.
  Proof.
    move: level.
    induction ϕ; simpl; intros level H; auto.
    - case_match;[reflexivity|congruence].
    - destruct_and!. by rewrite -> IHϕ1, -> IHϕ2.
    - destruct_and!. by rewrite -> IHϕ1, -> IHϕ2.
    - by rewrite IHϕ.
    - by rewrite IHϕ.
  Qed.

  Lemma nest_mu_aux_wfcmu level more ϕ:
    well_formed_closed_mu_aux ϕ level ->
    nest_mu_aux level more ϕ = ϕ.
  Proof.
    move: level.
    induction ϕ; simpl; intros level H; auto.
    - case_match;[reflexivity|congruence].
    - destruct_and!. by rewrite -> IHϕ1, -> IHϕ2.
    - destruct_and!. by rewrite -> IHϕ1, -> IHϕ2.
    - by rewrite IHϕ.
    - by rewrite IHϕ.
  Qed.

  Lemma bsvar_subst_nest_ex_aux_comm level more ϕ dbi ψ:
    well_formed_closed_ex_aux ψ level ->
    bsvar_subst (nest_ex_aux level more ϕ) ψ dbi = nest_ex_aux level more (bsvar_subst ϕ ψ dbi).
  Proof.
    move: level dbi. unfold svar_open.
    induction ϕ; move=> level dbi H; simpl; auto.
    - case_match; try reflexivity. by rewrite nest_ex_aux_wfcex.
    - rewrite IHϕ1;[assumption|]. rewrite IHϕ2;[assumption|]. reflexivity.
    - rewrite IHϕ1;[assumption|]. rewrite IHϕ2;[assumption|]. reflexivity.
    - rewrite IHϕ.
      { eapply well_formed_closed_ex_aux_ind;[|eassumption]. lia. }
      reflexivity.
    - rewrite IHϕ;[assumption|]. reflexivity.
  Qed.

  Lemma svar_open_nest_ex_aux_comm level more ϕ dbi X:
    svar_open dbi X (nest_ex_aux level more ϕ) = nest_ex_aux level more (svar_open dbi X ϕ).
  Proof.
    apply bsvar_subst_nest_ex_aux_comm.
    reflexivity.
  Qed.

  Lemma bevar_subst_nest_mu_aux_comm level more ϕ dbi ψ:
    well_formed_closed_mu_aux ψ level ->
    bevar_subst (nest_mu_aux level more ϕ) ψ dbi = nest_mu_aux level more (bevar_subst ϕ ψ dbi).
  Proof.
    move: level dbi. unfold svar_open.
    induction ϕ; move=> level dbi H; simpl; auto.
    - case_match; try reflexivity. by rewrite nest_mu_aux_wfcmu.
    - rewrite IHϕ1;[assumption|]. rewrite IHϕ2;[assumption|]. reflexivity.
    - rewrite IHϕ1;[assumption|]. rewrite IHϕ2;[assumption|]. reflexivity.
    - rewrite IHϕ;[assumption|]. reflexivity.
    - rewrite IHϕ.
      { eapply well_formed_closed_mu_aux_ind;[|eassumption]. lia. }
      reflexivity.
  Qed.

  Lemma evar_open_nest_mu_aux_comm level more ϕ dbi X:
    evar_open dbi X (nest_mu_aux level more ϕ) = nest_mu_aux level more (evar_open dbi X ϕ).
  Proof.
    move: level dbi. unfold evar_open.
    induction ϕ; move=> level dbi; simpl; auto; try congruence.
    - case_match; reflexivity.
  Qed.

  Lemma bevar_subst_nest_ex_aux level ϕ dbi ψ:
    well_formed_closed_ex_aux ψ level ->
    bevar_subst (nest_ex_aux level 1 ϕ) ψ dbi
    = match (compare_nat dbi level) with
      | Nat_less _ _ _ => nest_ex_aux level 1 (bevar_subst ϕ ψ dbi)
      | Nat_equal _ _ _ => nest_ex_aux level 1 ϕ
      | Nat_greater _ _ _ => nest_ex_aux level 1 (bevar_subst ϕ ψ (dbi-1))
      end.
  Proof.
    intros Hwfc.
    move: level Hwfc dbi. unfold evar_open.
    induction ϕ; move=> level Hwfc dbi; destruct (compare_nat dbi level); simpl; auto.
    1: {
      repeat (case_match; simpl; try lia; try reflexivity).
      by rewrite nest_ex_aux_wfcex.
    }
    1: {
      repeat (case_match; simpl; try lia; try reflexivity).
    }
    
    1: {
      repeat (case_match; simpl; try lia; try reflexivity).
      by rewrite nest_ex_aux_wfcex.
    }
    1,2,3,4,5,6: (rewrite -> IHϕ1 by assumption; rewrite -> IHϕ2 by assumption;
                  destruct (compare_nat dbi level); simpl; try reflexivity; try lia).
    
    4,5,6: (rewrite -> IHϕ by assumption; destruct (compare_nat dbi level); simpl; try reflexivity; try lia).
    1,2,3: (rewrite IHϕ; destruct (compare_nat (S dbi) (S level)); simpl; try reflexivity; try lia).
    1,2,3: (eapply well_formed_closed_ex_aux_ind;[|eassumption];lia).
    assert (Hdbi1: dbi - 0 = dbi). lia.
    assert (Hdbi2: S (dbi - 1) = dbi). lia.
    rewrite Hdbi1. rewrite Hdbi2. reflexivity.
  Qed.


  Lemma evar_open_nest_ex_aux_comm level ϕ dbi X:
    evar_open dbi X (nest_ex_aux level 1 ϕ)
    = match (compare_nat dbi level) with
      | Nat_less _ _ _ => nest_ex_aux level 1 (evar_open dbi X ϕ)
      | Nat_equal _ _ _ => nest_ex_aux level 1 ϕ
      | Nat_greater _ _ _ => nest_ex_aux level 1 (evar_open (dbi-1) X ϕ)
      end.
  Proof.
    unfold evar_open.
    apply bevar_subst_nest_ex_aux.
    reflexivity.
  Qed.


  Lemma bsvar_subst_nest_mu_aux level ϕ dbi ψ:
    well_formed_closed_mu_aux ψ level ->
    bsvar_subst (nest_mu_aux level 1 ϕ) ψ dbi
    = match (compare_nat dbi level) with
      | Nat_less _ _ _ => nest_mu_aux level 1 (bsvar_subst ϕ ψ dbi)
      | Nat_equal _ _ _ => nest_mu_aux level 1 ϕ
      | Nat_greater _ _ _ => nest_mu_aux level 1 (bsvar_subst ϕ ψ(dbi-1))
      end.
  Proof.
    intros Hwfc.
    move: level Hwfc dbi. unfold svar_open.
    induction ϕ; move=> level Hwfc dbi; destruct (compare_nat dbi level); simpl; auto.
    1: {
      repeat (case_match; simpl; try lia; try reflexivity).
      by rewrite nest_mu_aux_wfcmu.
    }
    1: {
      repeat (case_match; simpl; try lia; try reflexivity).
    }
    
    1: {
      repeat (case_match; simpl; try lia; try reflexivity).
      by rewrite nest_mu_aux_wfcmu.
    }
    1,2,3,4,5,6: (rewrite -> IHϕ1, -> IHϕ2 by assumption;
                  destruct (compare_nat dbi level); simpl; try reflexivity; try lia).
    
    1,2,3: (rewrite -> IHϕ by assumption; destruct (compare_nat dbi level); simpl; try reflexivity; try lia).
    1,2,3: (rewrite -> IHϕ; destruct (compare_nat (S dbi) (S level)); simpl; try reflexivity; try lia).
    1,2,4: (eapply well_formed_closed_mu_aux_ind;[|eassumption];lia).
    assert (Hdbi1: dbi - 0 = dbi). lia.
    assert (Hdbi2: S (dbi - 1) = dbi). lia.
    rewrite Hdbi1. rewrite Hdbi2. reflexivity.
  Qed.


  Lemma svar_open_nest_mu_aux_comm level ϕ dbi X:
    svar_open dbi X (nest_mu_aux level 1 ϕ)
    = match (compare_nat dbi level) with
      | Nat_less _ _ _ => nest_mu_aux level 1 (svar_open dbi X ϕ)
      | Nat_equal _ _ _ => nest_mu_aux level 1 ϕ
      | Nat_greater _ _ _ => nest_mu_aux level 1 (svar_open (dbi-1) X ϕ)
      end.
  Proof.
    unfold svar_open.
    apply bsvar_subst_nest_mu_aux.
    reflexivity.
  Qed.


  Lemma free_svars_nest_ex_aux dbi more ϕ:
    free_svars (nest_ex_aux dbi more ϕ) = free_svars ϕ.
  Proof.
    move: dbi. induction ϕ; move=> dbi; simpl; try reflexivity.
    - rewrite IHϕ1. rewrite IHϕ2. reflexivity.
    - rewrite IHϕ1. rewrite IHϕ2. reflexivity.
    - rewrite IHϕ. reflexivity.
    - rewrite IHϕ. reflexivity.
  Qed.

  Lemma free_evars_nest_mu_aux dbi more ϕ:
    free_evars (nest_mu_aux dbi more ϕ) = free_evars ϕ.
  Proof.
    move: dbi. induction ϕ; move=> dbi; simpl; try reflexivity.
    - rewrite IHϕ1. rewrite IHϕ2. reflexivity.
    - rewrite IHϕ1. rewrite IHϕ2. reflexivity.
    - rewrite IHϕ. reflexivity.
    - rewrite IHϕ. reflexivity.
  Qed.
  
  Lemma free_evars_nest_ex_aux dbi more ϕ:
    free_evars (nest_ex_aux dbi more ϕ) = free_evars ϕ.
  Proof.
    move: dbi. induction ϕ; move=> dbi; simpl; try reflexivity.
    - rewrite IHϕ1. rewrite IHϕ2. reflexivity.
    - rewrite IHϕ1. rewrite IHϕ2. reflexivity.
    - rewrite IHϕ. reflexivity.
    - rewrite IHϕ. reflexivity.
  Qed.

  Lemma free_svars_nest_mu_aux dbi more ϕ:
    free_svars (nest_mu_aux dbi more ϕ) = free_svars ϕ.
  Proof.
    move: dbi. induction ϕ; move=> dbi; simpl; try reflexivity.
    - rewrite IHϕ1. rewrite IHϕ2. reflexivity.
    - rewrite IHϕ1. rewrite IHϕ2. reflexivity.
    - rewrite IHϕ. reflexivity.
    - rewrite IHϕ. reflexivity.
  Qed.

  Corollary fresh_svar_nest_ex_aux dbi more ϕ:
    fresh_svar (nest_ex_aux dbi more ϕ) = fresh_svar ϕ.
  Proof.
    unfold fresh_svar.
      by rewrite free_svars_nest_ex_aux.
  Qed.

  Corollary fresh_evar_nest_mu_aux dbi more ϕ:
    fresh_evar (nest_mu_aux dbi more ϕ) = fresh_evar ϕ.
  Proof.
    unfold fresh_evar.
      by rewrite free_evars_nest_mu_aux.
  Qed.

  Corollary fresh_evar_nest_ex_aux dbi more ϕ:
    fresh_evar (nest_ex_aux dbi more ϕ) = fresh_evar ϕ.
  Proof.
    unfold fresh_evar.
      by rewrite free_evars_nest_ex_aux.
  Qed.

  Corollary fresh_svar_nest_mu_aux dbi more ϕ:
    fresh_svar (nest_mu_aux dbi more ϕ) = fresh_svar ϕ.
  Proof.
    unfold fresh_svar.
      by rewrite free_svars_nest_mu_aux.
  Qed.

  Corollary not_bevar_occur_0_nest_ex ϕ :
    bevar_occur (nest_ex ϕ) 0 = false.
  Proof.
    apply not_bevar_occur_level_nest_ex_aux. lia.
  Qed.

  Corollary not_bsvar_occur_0_nest_mu ϕ :
    bsvar_occur (nest_mu ϕ) 0 = false.
  Proof.
    apply not_bsvar_occur_level_nest_mu_aux. lia.
  Qed.

  Corollary svar_open_nest_ex_comm ϕ dbi X:
    svar_open dbi X (nest_ex ϕ) = nest_ex (svar_open dbi X ϕ).
  Proof.
    exact (svar_open_nest_ex_aux_comm 0 1 ϕ dbi X).
  Qed.

  Corollary evar_open_nest_mu_comm ϕ dbi X:
    evar_open dbi X (nest_mu ϕ) = nest_mu (evar_open dbi X ϕ).
  Proof.
    exact (evar_open_nest_mu_aux_comm 0 1 ϕ dbi X).
  Qed.
*)

  Corollary evar_is_fresh_in_app_l x ϕ₁ ϕ₂ :
    evar_is_fresh_in x (patt_app ϕ₁ ϕ₂) -> evar_is_fresh_in x ϕ₁.
  Proof.
    unfold evar_is_fresh_in. simpl.
    move/not_elem_of_union => [H1 H2].
    done.
  Qed.

  Corollary svar_is_fresh_in_app_l X ϕ₁ ϕ₂ :
    svar_is_fresh_in X (patt_app ϕ₁ ϕ₂) -> svar_is_fresh_in X ϕ₁.
  Proof.
    unfold svar_is_fresh_in. simpl.
    move/not_elem_of_union => [H1 H2].
    done.
  Qed.
  
  (*Hint Resolve evar_is_fresh_in_app_l : core.*)

  Corollary evar_is_fresh_in_app_r x ϕ₁ ϕ₂ :
    evar_is_fresh_in x (patt_app ϕ₁ ϕ₂) -> evar_is_fresh_in x ϕ₂.
  Proof.
    unfold evar_is_fresh_in. simpl.
    move/not_elem_of_union => [H1 H2].
    done.
  Qed.

  Corollary svar_is_fresh_in_app_r X ϕ₁ ϕ₂ :
    svar_is_fresh_in X (patt_app ϕ₁ ϕ₂) -> svar_is_fresh_in X ϕ₂.
  Proof.
    unfold svar_is_fresh_in. simpl.
    move/not_elem_of_union => [H1 H2].
    done.
  Qed.
  
  Lemma evar_is_fresh_in_app x ϕ₁ ϕ₂ :
    evar_is_fresh_in x (patt_app ϕ₁ ϕ₂)
    <-> (evar_is_fresh_in x ϕ₁ /\ evar_is_fresh_in x ϕ₂).
  Proof.
    split; intros H.
    - split.
      + eapply evar_is_fresh_in_app_l. apply H.
      + eapply evar_is_fresh_in_app_r. apply H.
    - unfold evar_is_fresh_in in *.
      simpl.
      set_solver.
  Qed.

  Lemma svar_is_fresh_in_app X ϕ₁ ϕ₂ :
    svar_is_fresh_in X (patt_app ϕ₁ ϕ₂)
    <-> (svar_is_fresh_in X ϕ₁ /\ svar_is_fresh_in X ϕ₂).
  Proof.
    split; intros H.
    - split.
      + eapply svar_is_fresh_in_app_l. apply H.
      + eapply svar_is_fresh_in_app_r. apply H.
    - unfold svar_is_fresh_in in *.
      simpl.
      set_solver.
  Qed.
  
  (*Hint Resolve evar_is_fresh_in_app_r : core.*)

  Corollary evar_is_fresh_in_imp_l x ϕ₁ ϕ₂ :
    evar_is_fresh_in x (patt_imp ϕ₁ ϕ₂) -> evar_is_fresh_in x ϕ₁.
  Proof.
    unfold evar_is_fresh_in. simpl.
    move/not_elem_of_union => [H1 H2].
    done.
  Qed.

  Corollary svar_is_fresh_in_imp_l X ϕ₁ ϕ₂ :
    svar_is_fresh_in X (patt_imp ϕ₁ ϕ₂) -> svar_is_fresh_in X ϕ₁.
  Proof.
    unfold svar_is_fresh_in. simpl.
    move/not_elem_of_union => [H1 H2].
    done.
  Qed.
  
  (*Hint Resolve evar_is_fresh_in_imp_l : core.*)

  Corollary evar_is_fresh_in_imp_r x ϕ₁ ϕ₂ :
    evar_is_fresh_in x (patt_imp ϕ₁ ϕ₂) -> evar_is_fresh_in x ϕ₂.
  Proof.
    unfold evar_is_fresh_in. simpl.
    move/not_elem_of_union => [H1 H2].
    done.
  Qed.

  Corollary svar_is_fresh_in_imp_r X ϕ₁ ϕ₂ :
    svar_is_fresh_in X (patt_imp ϕ₁ ϕ₂) -> svar_is_fresh_in X ϕ₂.
  Proof.
    unfold svar_is_fresh_in. simpl.
    move/not_elem_of_union => [H1 H2].
    done.
  Qed.

  Lemma evar_is_fresh_in_imp x ϕ₁ ϕ₂ :
    evar_is_fresh_in x (patt_imp ϕ₁ ϕ₂)
    <-> (evar_is_fresh_in x ϕ₁ /\ evar_is_fresh_in x ϕ₂).
  Proof.
    split; intros H.
    - split.
      + eapply evar_is_fresh_in_imp_l. apply H.
      + eapply evar_is_fresh_in_imp_r. apply H.
    - unfold evar_is_fresh_in in *.
      simpl.
      set_solver.
  Qed.

  Lemma svar_is_fresh_in_imp X ϕ₁ ϕ₂ :
    svar_is_fresh_in X (patt_imp ϕ₁ ϕ₂)
    <-> (svar_is_fresh_in X ϕ₁ /\ svar_is_fresh_in X ϕ₂).
  Proof.
    split; intros H.
    - split.
      + eapply svar_is_fresh_in_imp_l. apply H.
      + eapply svar_is_fresh_in_imp_r. apply H.
    - unfold svar_is_fresh_in in *.
      simpl.
      set_solver.
  Qed.

  
  (*Hint Resolve evar_is_fresh_in_imp_r : core.*)

  Corollary evar_is_fresh_in_exists x ϕ :
    evar_is_fresh_in x (patt_exists ϕ) <-> evar_is_fresh_in x ϕ.
  Proof.
    unfold evar_is_fresh_in. simpl. done.
  Qed.

  (*Hint Resolve evar_is_fresh_in_exists : core.*)

  Corollary evar_is_fresh_in_mu x ϕ :
    evar_is_fresh_in x (patt_mu ϕ) <-> evar_is_fresh_in x ϕ.
  Proof.
    unfold evar_is_fresh_in. simpl. done.
  Qed.

  (*Hint Resolve evar_is_fresh_in_mu : core.*)

  Corollary svar_is_fresh_in_exists x ϕ :
    svar_is_fresh_in x (patt_exists ϕ) <-> svar_is_fresh_in x ϕ.
  Proof.
    unfold svar_is_fresh_in. simpl. done.
  Qed.

  Corollary svar_is_fresh_in_mu x ϕ :
    svar_is_fresh_in x (patt_mu ϕ) <-> svar_is_fresh_in x ϕ.
  Proof.
    unfold svar_is_fresh_in. simpl. done.
  Qed.

  Definition simpl_free_evars :=
    (
      (@left_id_L EVarSet  ∅ (@union _ _)),
      (@right_id_L EVarSet ∅ (@union _ _))
(*       @free_evars_nest_ex_aux,
      @evar_open_nest_ex_aux_comm,
      @bevar_subst_nest_ex_aux,
      @free_evars_nest_ex_aux *)
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
      (@right_id_L SVarSet ∅ (@union _ _))
(*       @free_svars_nest_mu_aux,
      @svar_open_nest_mu_aux_comm,
      @bsvar_subst_nest_mu_aux,
      @free_svars_nest_mu_aux *)
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

 (* TODO: deprecated

  Lemma Private_positive_negative_occurrence_db_nest_mu_aux dbi level more ϕ:
    (no_negative_occurrence_db_b dbi (nest_mu_aux level more ϕ)
     = if decide (dbi < level) is left _ then no_negative_occurrence_db_b dbi ϕ
       else if decide (dbi < level + more) is left _ then true
            else no_negative_occurrence_db_b (dbi-more) ϕ
    ) /\ (
      no_positive_occurrence_db_b dbi (nest_mu_aux level more ϕ)
     = if decide (dbi < level) is left _ then no_positive_occurrence_db_b dbi ϕ
       else if decide (dbi < level + more) is left _ then true
            else no_positive_occurrence_db_b (dbi-more) ϕ
    ).
  Proof.
    move: dbi level more.
    induction ϕ; intros dbi level more; simpl;
      destruct (compare_nat dbi level); auto;
        repeat case_match; simpl; try lia; auto;
          try rewrite (proj1 (IHϕ1 _ _ _));
          try rewrite (proj2 (IHϕ1 _ _ _));
          try rewrite (proj1 (IHϕ2 _ _ _));
          try rewrite (proj2 (IHϕ2 _ _ _));
          try rewrite (proj1 (IHϕ _ _ _));
          try rewrite (proj2 (IHϕ _ _ _));
          simpl;
          repeat case_match; simpl; try lia; auto.

    replace (S dbi - more) with (S (dbi - more)) by lia. split; reflexivity.
    replace (S dbi - more) with (S (dbi - more)) by lia. split; reflexivity.
  Qed.

  Lemma no_negative_occurrence_db_nest_mu_aux dbi level more ϕ:
    no_negative_occurrence_db_b dbi (nest_mu_aux level more ϕ)
     = if decide (dbi < level) is left _ then no_negative_occurrence_db_b dbi ϕ
       else if decide (dbi < level + more) is left _ then true
            else no_negative_occurrence_db_b (dbi-more) ϕ.
  Proof.
    apply Private_positive_negative_occurrence_db_nest_mu_aux.
  Qed.

  Lemma no_positive_occurrence_db_nest_mu_aux dbi level more ϕ:
    no_positive_occurrence_db_b dbi (nest_mu_aux level more ϕ)
     = if decide (dbi < level) is left _ then no_positive_occurrence_db_b dbi ϕ
       else if decide (dbi < level + more) is left _ then true
            else no_positive_occurrence_db_b (dbi-more) ϕ.
  Proof.
    apply Private_positive_negative_occurrence_db_nest_mu_aux.
  Qed.

  Lemma well_formed_positive_nest_mu_aux level more ϕ:
    well_formed_positive (nest_mu_aux level more ϕ) = well_formed_positive ϕ.
  Proof.
    move: level.
    induction ϕ; intros level; simpl; auto.
    - rewrite IHϕ1. rewrite IHϕ2. auto.
    - rewrite IHϕ1. rewrite IHϕ2. auto.
    - rewrite IHϕ.
      rewrite no_negative_occurrence_db_nest_mu_aux. simpl.
      reflexivity.
  Qed. *)

  Lemma evar_open_inj : ∀ phi psi x n,
      evar_is_fresh_in x phi → evar_is_fresh_in x psi →
      evar_open n x phi =
      evar_open n x psi
      → phi = psi.
  Proof.
    induction phi; destruct psi;
      intros x' n' H H0 H1;
      try (cbn in H1; congruence);
      try (cbn in H1; case_match; congruence); auto.
    - cbn in H1. case_match; try congruence.
      inversion H1. subst. unfold evar_is_fresh_in in H. simpl in H. apply not_elem_of_singleton_1 in H.
      contradiction.
    - cbn in H1. case_match; try congruence.
      inversion H1. subst. unfold evar_is_fresh_in in H0. simpl in H0. apply not_elem_of_singleton_1 in H0.
      contradiction.
    - cbn in H1.
      repeat case_match; auto; try congruence.
      1-3: inversion H1; subst; try lia. assert (n = n0) by lia. auto.
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
    induction phi; destruct psi;
      intros X' n' H H0 H1;
      try (cbn in H1; congruence);
      try (cbn in H1; case_match; congruence); auto.
    - cbn in H1. case_match; try congruence.
      inversion H1. subst. unfold svar_is_fresh_in in H. simpl in H. set_solver.
    - cbn in H1. case_match; try congruence.
      inversion H1. subst. unfold svar_is_fresh_in in H0. simpl in H0. set_solver.
    - cbn in H1. repeat case_match; auto; try congruence.
      1-3: inversion H1; subst; try lia. assert (n = n0) by lia. auto.
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

 (* TODO: deprecated
 
  Lemma nest_mu_aux_0 level p:
    nest_mu_aux level 0 p = p.
  Proof.
    move: level.
    induction p; intros level; simpl; auto.
    - case_match; auto.
    - by rewrite IHp1 IHp2.
    - by rewrite IHp1 IHp2.
    - by rewrite IHp.
    - by rewrite IHp.
  Defined.

  Lemma nest_ex_aux_0 level p:
    nest_ex_aux level 0 p = p.
  Proof.
    move: level.
    induction p; intros level; simpl; auto.
    - case_match; auto.
    - by rewrite IHp1 IHp2.
    - by rewrite IHp1 IHp2.
    - by rewrite IHp.
    - by rewrite IHp.
  Defined. *)

  (* Example:
  phi = (mu, patt_bound_svar 1)
  level = 0

  nest_mu_aux 0 more' (free_svar_subst' more (mu, patt_bound_svar 1) psi X)
= nest_mu_aux 0 more' (mu, patt_bound_svar 1)
    =? OK
  (mu, patt_bound_svar (1+more')
=  free_svar_subst' more ((mu, patt_bound_svar (1+more')) (nest_mu_aux 0 more' psi) X.
= free_svar_subst' more (nest_mu_aux 0 more' (mu, patt_bound_svar 1)) (nest_mu_aux 0 more' psi) X.


If X does not occur free in phi:

    nest_mu_aux level more' (free_svar_subst' more phi psi X)
    
=?
    free_svar_subst' more (nest_mu_aux level more' phi) (nest_mu_aux level more' psi) X.

   *)
  (*
  Lemma free_svar_subst_nest_mu phi psi X more more' level:
    well_formed_closed_mu_aux psi 0 ->
    nest_mu_aux level more' (free_svar_subst' more phi psi X)
    = free_svar_subst' more (nest_mu_aux level more' phi) (nest_mu_aux level more' psi) X.
  Proof.
    intros Hpsi.

    remember (size' phi) as sz.
    assert (Hsz: size' phi <= sz) by lia.
    clear Heqsz.
    
    move: phi Hsz more more' level.
    induction sz; intros phi Hsz; destruct phi; simpl in *; try lia;
      intros more more' level; simpl; auto.
    - case_match;[|auto]. subst. Print free_svar_subst'.  auto.
      rewrite !nest_mu_aux_wfc_mu; auto.
      all: eapply well_formed_closed_mu_aux_ind; try eassumption; lia.
    - rewrite IHsz. lia. rewrite IHsz. lia. reflexivity.
    - rewrite IHsz. lia. rewrite IHsz. lia. reflexivity.
    - rewrite IHsz. lia. reflexivity.
    - f_equal. unfold nest_mu at 1.
      rewrite IHsz. lia. rewrite [nest_mu_aux 0 1 psi]nest_mu_aux_wfc_mu. assumption.
      rewrite [nest_mu_aux level more' psi]nest_mu_aux_wfc_mu.
      { eapply well_formed_closed_mu_aux_ind. 2: eassumption. lia. }
      unfold nest_mu at 1.
      rewrite IHsz.
      { rewrite size'_nest_mu_aux. lia. }
      rewrite IHsz.
      { rewrite size'_nest_mu_aux. lia. }
      rewrite [nest_mu_aux (S level) more' psi]nest_mu_aux_wfc_mu.
      { eapply well_formed_closed_mu_aux_ind. 2: eassumption. lia. }
      rewrite [nest_mu_aux 0 1 psi]nest_mu_aux_wfc_mu. assumption.
      f_equal. Check pred.
      
  (*
      rewrite nest_mu_aux_twice. rewrite nest_mu_aux_twice.
      f_equal. lia.*)
  Abort.
   *)

(*  TODO: deprecated

 Lemma wfcex_nest_mu psi more level1 level2:
    well_formed_closed_ex_aux psi level2 ->
    well_formed_closed_ex_aux (nest_mu_aux level1 more psi) level2.
  Proof.
    intros H. move: level1 level2 H.
    induction psi; intros level1 level2 H; simpl; auto.
    - simpl in H. destruct_and!.
      specialize (IHpsi1 level1 level2 ltac:(assumption)).
      specialize (IHpsi2 level1 level2 ltac:(assumption)).
      split_and!; auto.
    - simpl in H. destruct_and!.
      specialize (IHpsi1 level1 level2 ltac:(assumption)).
      specialize (IHpsi2 level1 level2 ltac:(assumption)).
      split_and!; auto.
  Qed. *)

  Lemma Private_evar_open_free_svar_subst_comm: ∀ sz phi psi fresh n X,
      ((size phi) <= sz) → (well_formed_closed_ex_aux psi 0) → evar_is_fresh_in fresh phi →
      evar_is_fresh_in fresh (free_svar_subst phi psi X)
      →
      (evar_open n fresh (free_svar_subst phi psi X)) = (free_svar_subst (evar_open n fresh phi) psi X).
  Proof.
    induction sz; destruct phi; intros psi fresh n0 X Hsz Hwf Hfresh1 Hfresh2; try inversion Hsz; auto.
    - simpl. case_match.
      + rewrite -> evar_open_closed. reflexivity.
        assumption.
      + simpl. reflexivity.
    - cbn. case_match; done.
    - simpl. unfold evar_open in *. rewrite -> bevar_subst_app, -> (IHsz phi1), -> (IHsz phi2); try lia; try assumption. reflexivity.
      apply (evar_is_fresh_in_app_r Hfresh1). simpl in Hfresh2.
      apply (evar_is_fresh_in_app_r Hfresh2). apply (evar_is_fresh_in_app_l Hfresh1).
      apply (evar_is_fresh_in_app_l Hfresh2).
      reflexivity.
    - simpl. unfold evar_open in *. rewrite -> bevar_subst_imp, -> (IHsz phi1), -> (IHsz phi2); try lia; try assumption. reflexivity.
      apply (evar_is_fresh_in_imp_r Hfresh1). simpl in Hfresh2.
      apply (evar_is_fresh_in_imp_r Hfresh2). apply (evar_is_fresh_in_app_l Hfresh1).
      apply (evar_is_fresh_in_imp_l Hfresh2).
      reflexivity.
    - simpl. unfold evar_open in *. rewrite -> bevar_subst_exists, -> IHsz. reflexivity. lia. assumption.
      apply evar_is_fresh_in_exists in Hfresh1. assumption.
      simpl in Hfresh2. apply evar_is_fresh_in_exists in Hfresh1. assumption.
      reflexivity.
    - simpl. unfold evar_open in *. rewrite -> bevar_subst_mu.
      f_equal.
      rewrite -> IHsz; auto. lia.
      reflexivity.
  Qed.

  Corollary evar_open_free_svar_subst_comm: ∀ phi psi fresh n X,
      (well_formed_closed_ex_aux psi 0) → evar_is_fresh_in fresh phi →
      evar_is_fresh_in fresh (free_svar_subst phi psi X)
      →
      (evar_open n fresh (free_svar_subst phi psi X)) = (free_svar_subst (evar_open n fresh phi) psi X).
  Proof.
    intros phi psi fresh n X H H0 H1. apply Private_evar_open_free_svar_subst_comm with (sz := (size phi)); try lia; try assumption.
  Qed.

(* TODO: deprecated

  Lemma nest_ex_aux_plus1 level more phi:
    more > 0 ->
    bevar_occur phi level = false ->
    nest_ex_aux level more phi = nest_ex_aux (S level) more phi.
  Proof.
    intros Hmore Hlevel.
    move: level Hlevel.
    induction phi; intros level Hlevel; simpl; auto.
    - unfold bevar_occur in Hlevel.
      repeat case_match; auto; lia.
    - simpl in Hlevel. apply orb_false_iff in Hlevel. destruct Hlevel as [Hlevel1 Hlevel2].
      rewrite IHphi1;[auto|]. rewrite IHphi2;[auto|]. reflexivity.
    - simpl in Hlevel. apply orb_false_iff in Hlevel. destruct Hlevel as [Hlevel1 Hlevel2].
      rewrite IHphi1;[auto|]. rewrite IHphi2;[auto|]. reflexivity.
    - simpl in Hlevel.
      rewrite IHphi;[assumption|]. reflexivity.
    - simpl in Hlevel.
      rewrite IHphi;[assumption|]. reflexivity.
  Qed.

  Lemma nest_mu_aux_plus1 level more phi:
    more > 0 ->
    bsvar_occur phi level = false ->
    nest_mu_aux level more phi = nest_mu_aux (S level) more phi.
  Proof.
    intros Hmore Hlevel.
    move: level Hlevel.
    induction phi; intros level Hlevel; simpl; auto.
    - unfold bsvar_occur in Hlevel.
      repeat case_match; auto; lia.
    - simpl in Hlevel. apply orb_false_iff in Hlevel. destruct Hlevel as [Hlevel1 Hlevel2].
      rewrite IHphi1;[auto|]. rewrite IHphi2;[auto|]. reflexivity.
    - simpl in Hlevel. apply orb_false_iff in Hlevel. destruct Hlevel as [Hlevel1 Hlevel2].
      rewrite IHphi1;[auto|]. rewrite IHphi2;[auto|]. reflexivity.
    - simpl in Hlevel.
      rewrite IHphi;[assumption|]. reflexivity.
    - simpl in Hlevel.
      rewrite IHphi;[assumption|]. reflexivity.
  Qed. *)


(*  TODO: deprecated

Fixpoint no_bsvar_in_range (phi : Pattern) (min_ind_svar max_ind_svar : db_index) : bool :=
    match phi with
    | patt_free_evar _ => true
    | patt_free_svar _ => true
    | patt_bound_evar n => true
    | patt_bound_svar n => if decide (n < max_ind_svar /\ ~ (n < min_ind_svar)) is left _ then false else true
    | patt_sym _ => true
    | patt_app psi1 psi2 => no_bsvar_in_range psi1 min_ind_svar max_ind_svar &&
                            no_bsvar_in_range psi2 min_ind_svar max_ind_svar
    | patt_bott => true
    | patt_imp psi1 psi2 => no_bsvar_in_range psi1 min_ind_svar max_ind_svar &&
                            no_bsvar_in_range psi2 min_ind_svar max_ind_svar
    | patt_exists psi => no_bsvar_in_range psi min_ind_svar max_ind_svar
    | patt_mu psi => no_bsvar_in_range psi (S min_ind_svar) (S max_ind_svar)
    end.

  Fixpoint no_bevar_in_range (phi : Pattern) (min_ind_evar max_ind_evar : db_index) : bool :=
    match phi with
    | patt_free_evar _ => true
    | patt_free_svar _ => true
    | patt_bound_evar n => if decide (n < max_ind_evar /\ ~ (n < min_ind_evar)) is left _ then false else true
    | patt_bound_svar n => true
    | patt_sym _ => true
    | patt_app psi1 psi2 => no_bevar_in_range psi1 min_ind_evar max_ind_evar &&
                            no_bevar_in_range psi2 min_ind_evar max_ind_evar
    | patt_bott => true
    | patt_imp psi1 psi2 => no_bevar_in_range psi1 min_ind_evar max_ind_evar &&
                            no_bevar_in_range psi2 min_ind_evar max_ind_evar
    | patt_exists psi => no_bevar_in_range psi (S min_ind_evar) (S max_ind_evar)
    | patt_mu psi => no_bevar_in_range psi min_ind_evar max_ind_evar
    end.

  Lemma no_bsvar_in_range_nest_mu_aux level more phi:
    no_bsvar_in_range (nest_mu_aux level more phi) level (level + more).
  Proof.
    move: level more.
    induction phi; intros level more; simpl; auto.
    - repeat case_match; auto; lia.
    - split_and!. apply IHphi1. apply IHphi2.
    - split_and!. apply IHphi1. apply IHphi2.
    - apply IHphi.
  Qed.

  Lemma no_bevar_in_range_nest_ex_aux level more phi:
    no_bevar_in_range (nest_ex_aux level more phi) level (level + more).
  Proof.
    move: level more.
    induction phi; intros level more; simpl; auto.
    - repeat case_match; auto; lia.
    - split_and!. apply IHphi1. apply IHphi2.
    - split_and!. apply IHphi1. apply IHphi2.
    - apply IHphi.
  Qed.

  Lemma nest_mu_aux_no_bsvar_in_range level more min_svar max_svar d phi:
    no_bsvar_in_range phi min_svar max_svar ->
    level >= min_svar ->
    level + d <= max_svar ->
    nest_mu_aux level more phi = nest_mu_aux (level + d) more phi.
  Proof.
    intros Hrange Hlevel Hd.
    move: min_svar max_svar Hrange level Hlevel Hd.
    induction phi; intros min_svar max_svar Hrange level Hlevel Hd; simpl; auto.
    - simpl in Hrange. repeat case_match; auto; try lia. congruence.
    - simpl in Hrange. destruct_and!.
      erewrite IHphi1. 2: eassumption. all: auto.
      erewrite IHphi2. 2: eassumption. all: auto.
    - simpl in Hrange. destruct_and!.
      erewrite IHphi1. 2: eassumption. all: auto.
      erewrite IHphi2. 2: eassumption. all: auto.
    - simpl in Hrange.
      erewrite IHphi. 2: eassumption. all: auto.
    - simpl in Hrange.
      erewrite IHphi. 2: eassumption. reflexivity. lia. lia.
  Qed.


  Lemma nest_ex_aux_no_bevar_in_range level more min_evar max_evar d phi:
    no_bevar_in_range phi min_evar max_evar ->
    level >= min_evar ->
    level + d <= max_evar ->
    nest_ex_aux level more phi = nest_ex_aux (level + d) more phi.
  Proof.
    intros Hrange Hlevel Hd.
    move: min_evar max_evar Hrange level Hlevel Hd.
    induction phi; intros min_evar max_evar Hrange level Hlevel Hd; simpl; auto.
    - simpl in Hrange. repeat case_match; auto; try lia. congruence.
    - simpl in Hrange. destruct_and!.
      erewrite IHphi1. 2: eassumption. all: auto.
      erewrite IHphi2. 2: eassumption. all: auto.
    - simpl in Hrange. destruct_and!.
      erewrite IHphi1. 2: eassumption. all: auto.
      erewrite IHphi2. 2: eassumption. all: auto.
    - simpl in Hrange.
      erewrite IHphi. 2: eassumption. all: auto. lia. lia.
    - simpl in Hrange.
      erewrite IHphi. 2: eassumption. all: auto.
  Qed.
  
  Lemma nest_mu_aux_twice level more more' phi:
    nest_mu_aux level more (nest_mu_aux level more' phi) = nest_mu_aux level (more + more') phi.
  Proof.
    move: level more more'.
    induction phi; intros level more more'; simpl; auto.
    - repeat case_match; auto; try lia.
      f_equal. lia.
    - rewrite IHphi1. rewrite IHphi2. reflexivity.
    - rewrite IHphi1. rewrite IHphi2. reflexivity.
    - rewrite IHphi. reflexivity.
    - rewrite IHphi. reflexivity.
  Qed.
  
  Lemma free_svar_subst_nest_mu_1 phi psi X more more':
    free_svar_subst' more phi (nest_mu_aux 0 more' psi) X
    = free_svar_subst' (more+more') phi psi X.
  Proof.
    move: more.
    induction phi; intros more; simpl; auto.
    - case_match; auto. apply nest_mu_aux_twice.
    - rewrite IHphi1. rewrite IHphi2. reflexivity.
    - rewrite IHphi1. rewrite IHphi2. reflexivity.
    - rewrite IHphi. reflexivity.
    - rewrite IHphi. reflexivity.
  Qed.

  Lemma nest_ex_aux_twice level more more' phi:
    nest_ex_aux level more (nest_ex_aux level more' phi) = nest_ex_aux level (more + more') phi.
  Proof.
    move: level more more'.
    induction phi; intros level more more'; simpl; auto.
    - repeat case_match; auto; try lia.
      f_equal. lia.
    - rewrite IHphi1. rewrite IHphi2. reflexivity.
    - rewrite IHphi1. rewrite IHphi2. reflexivity.
    - rewrite IHphi. reflexivity.
    - rewrite IHphi. reflexivity.
  Qed.
  
  Lemma free_evar_subst_nest_ex_1 phi psi x more more':
    free_evar_subst' more phi (nest_ex_aux 0 more' psi) x
    = free_evar_subst' (more+more') phi psi x.
  Proof.
    move: more.
    induction phi; intros more; simpl; auto.
    - case_match; auto. apply nest_ex_aux_twice.
    - rewrite IHphi1. rewrite IHphi2. reflexivity.
    - rewrite IHphi1. rewrite IHphi2. reflexivity.
    - rewrite IHphi. reflexivity.
    - rewrite IHphi. reflexivity.
  Qed.

  
  Lemma nest_mu_aux_wfc_mu level more psi:
    well_formed_closed_mu_aux psi level ->
    nest_mu_aux level more psi = psi.
  Proof.
    move: level.
    induction psi; intros level Hlevel; simpl in *; auto.
    - repeat case_match; auto; congruence.
    - destruct_and!.
      rewrite IHpsi1; auto.
      rewrite IHpsi2; auto.
    - destruct_and!.
      rewrite IHpsi1; auto.
      rewrite IHpsi2; auto.
    - rewrite IHpsi; auto.
    - rewrite IHpsi; auto.
  Qed.

  Lemma nest_ex_aux_wfc_ex level more psi:
    well_formed_closed_ex_aux psi level ->
    nest_ex_aux level more psi = psi.
  Proof.
    move: level.
    induction psi; intros level Hlevel; simpl in *; auto.
    - repeat case_match; auto; congruence.
    - destruct_and!.
      rewrite IHpsi1; auto.
      rewrite IHpsi2; auto.
    - destruct_and!.
      rewrite IHpsi1; auto.
      rewrite IHpsi2; auto.
    - rewrite IHpsi; auto.
    - rewrite IHpsi; auto.
  Qed.

  Lemma size'_nest_mu_aux level more phi:
    size' (nest_mu_aux level more phi) = size' phi.
  Proof.
    move: level.
    induction phi; intros level; simpl; auto.
  Qed.  

  Lemma wfc_mu_nest_mu psi level level' more:
    well_formed_closed_mu_aux psi level ->
    well_formed_closed_mu_aux (nest_mu_aux level' more psi) (level+more).
  Proof.
    intros H.
    move: level level' H.
    induction psi; intros level level' H; simpl in *; auto.
    - repeat case_match; auto; lia.
    - destruct_and!.
      specialize (IHpsi1 level level' ltac:(assumption)).
      specialize (IHpsi2 level level' ltac:(assumption)).
      split_and!; auto.
    - destruct_and!.
      specialize (IHpsi1 level level' ltac:(assumption)).
      specialize (IHpsi2 level level' ltac:(assumption)).
      split_and!; auto.
    - specialize (IHpsi (S level) (S level') ltac:(assumption)).
      simpl in IHpsi. auto.
  Qed.

  Lemma wfc_mu_nest_mu_2 psi level level' more:
    well_formed_closed_mu_aux
      psi
      (if decide (level < level') is left _ then level
       else if decide (level < level' + more) is left _ then level' else level - more)
    ->
    well_formed_closed_mu_aux (nest_mu_aux level' more psi) level.
  Proof.
    intros H.
    move: level level' more H.
    induction psi; intros level level' more H; simpl in *; auto.
    - repeat case_match; auto; lia.
    - destruct_and!.
      specialize (IHpsi1 level level' more ltac:(assumption)).
      specialize (IHpsi2 level level' more ltac:(assumption)).
      split_and!; auto.
    - destruct_and!.
      specialize (IHpsi1 level level' more ltac:(assumption)).
      specialize (IHpsi2 level level' more ltac:(assumption)).
      split_and!; auto.
    - simpl.
      apply IHpsi.
      repeat case_match; auto; try lia.      
      eapply well_formed_closed_mu_aux_ind.
      2: eassumption.
      lia.
  Qed.

  Lemma wfc_ex_nest_ex_2 psi level level' more:
    well_formed_closed_ex_aux
      psi
      (if decide (level < level') is left _ then level
       else if decide (level < level' + more) is left _ then level' else level - more)
    ->
    well_formed_closed_ex_aux (nest_ex_aux level' more psi) level.
  Proof.
    intros H.
    move: level level' more H.
    induction psi; intros level level' more H; simpl in *; auto.
    - repeat case_match; auto; lia.
    - destruct_and!.
      specialize (IHpsi1 level level' more ltac:(assumption)).
      specialize (IHpsi2 level level' more ltac:(assumption)).
      split_and!; auto.
    - destruct_and!.
      specialize (IHpsi1 level level' more ltac:(assumption)).
      specialize (IHpsi2 level level' more ltac:(assumption)).
      split_and!; auto.
    - simpl.
      apply IHpsi.
      repeat case_match; auto; try lia.      
      eapply well_formed_closed_ex_aux_ind.
      2: eassumption.
      lia.
  Qed.
  Lemma free_svars_free_svar_subst_more phi psi X:
    free_svars (free_svar_subst phi psi X)
    = free_svars (free_svar_subst phi psi X).
  Proof.
    move: more more'.
    induction phi; intros more more'; simpl; auto.
    - case_match; auto.
      rewrite ! free_svars_nest_mu_aux.
      reflexivity.
    - erewrite IHphi1. erewrite IHphi2. reflexivity.
    - erewrite IHphi1. erewrite IHphi2. reflexivity.
  Qed.

  Lemma free_evars_free_svar_subst_more phi psi X more more':
    free_evars (free_svar_subst' more phi psi X)
    = free_evars (free_svar_subst' more' phi psi X).
  Proof.
    move: more more'.
    induction phi; intros more more'; simpl; auto.
    - case_match; auto.
      rewrite ! free_evars_nest_mu_aux.
      reflexivity.
    - erewrite IHphi1. erewrite IHphi2. reflexivity.
    - erewrite IHphi1. erewrite IHphi2. reflexivity.
  Qed.

  Lemma svar_is_fresh_in_free_svar_subst_more phi psi X Y more more':
    svar_is_fresh_in Y (free_svar_subst' more phi psi X)
    = svar_is_fresh_in Y (free_svar_subst' more' phi psi X).
  Proof.
    unfold svar_is_fresh_in.
    erewrite free_svars_free_svar_subst_more.
    reflexivity.
  Qed.


  Lemma evar_is_fresh_in_free_svar_subst_more phi psi X Y more more':
    evar_is_fresh_in Y (free_svar_subst' more phi psi X)
    = evar_is_fresh_in Y (free_svar_subst' more' phi psi X).
  Proof.
    unfold evar_is_fresh_in.
    erewrite free_evars_free_svar_subst_more.
    reflexivity.
  Qed.


  Lemma bsvar_occur_nest_mu_aux psi level more dbi:
    dbi >= level ->
    bsvar_occur (nest_mu_aux level more psi) (dbi+more) = bsvar_occur psi dbi.
  Proof.
    intros Hlevel.
    move: dbi more level Hlevel.
    induction psi; intros dbi more level Hlevel; simpl; auto.
    - repeat case_match; auto; try lia.
    - rewrite IHpsi1. lia. rewrite IHpsi2. lia. reflexivity.
    - rewrite IHpsi1. lia. rewrite IHpsi2. lia. reflexivity.
    - simpl. erewrite <- IHpsi. simpl. reflexivity. lia.
  Qed.

  
  Lemma bevar_occur_nest_ex_aux psi level more dbi:
    dbi >= level ->
    bevar_occur (nest_ex_aux level more psi) (dbi+more) = bevar_occur psi dbi.
  Proof.
    intros Hlevel.
    move: dbi more level Hlevel.
    induction psi; intros dbi more level Hlevel; simpl; auto.
    - repeat case_match; auto; try lia.
    - rewrite IHpsi1. lia. rewrite IHpsi2. lia. reflexivity.
    - rewrite IHpsi1. lia. rewrite IHpsi2. lia. reflexivity.
    - simpl. erewrite <- IHpsi. simpl. reflexivity. lia.
  Qed.

  Lemma bsvar_occur_nest_mu_aux_2 dbi more psi level:
    dbi < more + level ->
    dbi >= level ->
    bsvar_occur (nest_mu_aux level more psi) dbi = false.
  Proof.
    intros Hdbi Hlevel.
    move: dbi more level Hdbi Hlevel.
    induction psi; intros dbi more level Hdbi Hlevel; simpl; auto.
    - repeat case_match; auto. lia. lia.
    - rewrite IHpsi1. lia. lia. rewrite IHpsi2. lia. lia. reflexivity.
    - rewrite IHpsi1. lia. lia. rewrite IHpsi2. lia. lia. reflexivity.
    - rewrite IHpsi. lia. lia. reflexivity.
  Qed.
  
  Lemma bevar_occur_nest_ex_aux_2 dbi more psi level:
    dbi < more + level ->
    dbi >= level ->
    bevar_occur (nest_ex_aux level more psi) dbi = false.
  Proof.
    intros Hdbi Hlevel.
    move: dbi more level Hdbi Hlevel.
    induction psi; intros dbi more level Hdbi Hlevel; simpl; auto.
    - repeat case_match; auto. lia. lia.
    - rewrite IHpsi1. lia. lia. rewrite IHpsi2. lia. lia. reflexivity.
    - rewrite IHpsi1. lia. lia. rewrite IHpsi2. lia. lia. reflexivity.
    - rewrite IHpsi. lia. lia. reflexivity.
  Qed.*)

(* TODO: deprecated, probably not provable:


  Lemma bsvar_occur_free_svar_subst_1 phi psi X more dbi:
    dbi < more ->
    bsvar_occur (free_svar_subst' more phi psi X) dbi = bsvar_occur phi dbi.
  Proof.
    intros Hdbi.
    move: more dbi Hdbi.
    induction phi; intros more dbi Hdbi; simpl; auto.
    - case_match; auto. simpl.
      apply bsvar_occur_nest_mu_aux_2. lia. lia.
    - rewrite IHphi1. lia. rewrite IHphi2. lia. reflexivity.
    - rewrite IHphi1. lia. rewrite IHphi2. lia. reflexivity.
    - rewrite IHphi. lia. reflexivity.
  Qed.

 Lemma bevar_occur_free_evar_subst_1 phi psi X more dbi:
    dbi < more ->
    bevar_occur (free_evar_subst' more phi psi X) dbi = bevar_occur phi dbi.
  Proof.
    intros Hdbi.
    move: more dbi Hdbi.
    induction phi; intros more dbi Hdbi; simpl; auto.
    - case_match; auto. simpl.
      apply bevar_occur_nest_ex_aux_2. lia. lia.
    - rewrite IHphi1. lia. rewrite IHphi2. lia. reflexivity.
    - rewrite IHphi1. lia. rewrite IHphi2. lia. reflexivity.
    - rewrite IHphi. lia. reflexivity.
  Qed.
  
  Lemma bsvar_occur_free_svar_subst phi psi X more dbi:
    dbi >= more ->
    bsvar_occur (free_svar_subst' more phi psi X) dbi
    <-> bsvar_occur phi dbi \/ ( X ∈ free_svars phi /\  bsvar_occur psi (dbi-more)).
  Proof.
    intros Hdbi.
    move: dbi more Hdbi.
    induction phi; intros dbi more Hdbi; simpl; auto.
    - set_solver.
    - case_match.
      + subst.
        pose proof (Htmp := @bsvar_occur_nest_mu_aux psi 0 more (dbi - more) ltac:(lia)).
        replace (dbi - more + more) with dbi in Htmp by lia.
        rewrite -Htmp.
        assert (Hx: x ∈ @singleton _ SVarSet _ x) by set_solver.
        split; intros H.
        * right. split; assumption.
        * destruct H. congruence. destruct H. assumption.
      + simpl. set_solver.
    - set_solver.
    - case_match.
      + firstorder.
      + set_solver.
    - set_solver.
    - simpl.
      unfold is_true in *.
      repeat rewrite orb_true_iff.
      rewrite IHphi1;[|lia].
      rewrite IHphi2;[|lia].
      clear. set_solver.
    - set_solver.
    - simpl.
      unfold is_true in *.
      repeat rewrite orb_true_iff.
      rewrite IHphi1;[|lia].
      rewrite IHphi2;[|lia].
      clear. set_solver.
    - rewrite IHphi;[|lia].
      replace (S dbi - S more) with (dbi - more) by lia.
      tauto.
  Qed.
  

  Lemma bevar_occur_free_evar_subst phi psi x more dbi:
    dbi >= more ->
    bevar_occur (free_evar_subst' more phi psi x) dbi
    <-> bevar_occur phi dbi \/ ( x ∈ free_evars phi /\  bevar_occur psi (dbi-more)).
  Proof.
    intros Hdbi.
    move: dbi more Hdbi.
    induction phi; intros dbi more Hdbi; simpl; auto.
    - case_match.
      + subst.
        pose proof (Htmp := @bevar_occur_nest_ex_aux psi 0 more (dbi - more) ltac:(lia)).
        replace (dbi - more + more) with dbi in Htmp by lia.
        rewrite -Htmp.
        assert (Hx: x0 ∈ @singleton _ EVarSet _ x0) by set_solver.
        split; intros H.
        * right. split; assumption.
        * destruct H. congruence. destruct H. assumption.
      + simpl. set_solver.
    - set_solver.
    - case_match.
      + firstorder.
      + set_solver.
    - set_solver.
    - set_solver.
    - simpl.
      unfold is_true in *.
      repeat rewrite orb_true_iff.
      rewrite IHphi1;[|lia].
      rewrite IHphi2;[|lia].
      clear. set_solver.
    - set_solver.
    - simpl.
      unfold is_true in *.
      repeat rewrite orb_true_iff.
      rewrite IHphi1;[|lia].
      rewrite IHphi2;[|lia].
      clear. set_solver.
    - rewrite IHphi;[|lia].
      replace (S dbi - S more) with (dbi - more) by lia.
      tauto.
  Qed.*)

  Lemma Private_svar_open_free_svar_subst_comm : ∀ sz phi psi fresh n X,
      ((size phi) <= sz) → (well_formed_closed_mu_aux psi 0) →  
      svar_is_fresh_in fresh phi → svar_is_fresh_in fresh (free_svar_subst phi psi X) → (fresh ≠ X) 
      →
      (svar_open n fresh (free_svar_subst phi psi X)) = 
      (free_svar_subst (svar_open n fresh phi) psi X).
  Proof.
    unfold free_svar_subst.
    induction sz; destruct phi; intros psi fresh n0 X Hsz Hwf (* Hwfc *) Hfresh1 Hfresh2 Hneq; auto.
    - simpl. case_match; auto.
      rewrite -> svar_open_closed; auto.
    - cbn. case_match; auto. simpl.
      + case_match.
        * congruence.
        * reflexivity.
    - inversion Hsz.
    - inversion Hsz.
    - inversion Hsz.
    - inversion Hsz.
    - simpl. case_match; auto.
      rewrite -> svar_open_closed; auto.
    - cbn. case_match; auto. simpl.
      + case_match.
        * congruence.
        * reflexivity.
    - simpl.
      unfold svar_open in *. rewrite -> bsvar_subst_app, -> (IHsz phi1), -> (IHsz phi2); try lia; try assumption; try lia; try assumption.
      reflexivity.
      simpl in Hsz. lia.
      simpl in Hfresh1. apply svar_is_fresh_in_app_r in Hfresh1. assumption.
      simpl in Hfresh2. apply svar_is_fresh_in_app_r in Hfresh2. assumption.
      simpl in Hsz. lia.
      simpl in Hfresh1. apply svar_is_fresh_in_app_l in Hfresh1. assumption.
      simpl in Hfresh2. apply svar_is_fresh_in_app_l in Hfresh2. assumption.
      reflexivity.
    - simpl.
      unfold svar_open in *. rewrite -> bsvar_subst_imp, -> (IHsz phi1), -> (IHsz phi2); try lia; try assumption; try lia; try assumption.
      reflexivity.
      simpl in Hsz. lia.
      simpl in Hfresh1. apply svar_is_fresh_in_app_r in Hfresh1. assumption.
      simpl in Hfresh2. apply svar_is_fresh_in_app_r in Hfresh2. assumption.
      simpl in Hsz. lia.
      simpl in Hfresh1. apply svar_is_fresh_in_app_l in Hfresh1. assumption.
      simpl in Hfresh2. apply svar_is_fresh_in_app_l in Hfresh2. assumption.
      reflexivity.
    - remember ((free_evars (svar_open n0 fresh (free_svar_subst phi psi X))) ∪
                                                                              (free_evars (free_svar_subst (svar_open n0 fresh phi) psi X))) as B.
      simpl. unfold svar_open in *. rewrite -> bsvar_subst_exists by reflexivity. remember (@evar_fresh (elements B)) as x.
      assert(x ∉ B).
      {
        subst. apply set_evar_fresh_is_fresh'.
      }
      subst B.  apply not_elem_of_union in H. destruct H.

      fold free_svar_subst. (* this is needed *)
      fold (svar_open n0 fresh (free_svar_subst phi psi X)). (* only this is not sufficient *)
      erewrite (@evar_open_inj (svar_open n0 fresh (free_svar_subst phi psi X)) (free_svar_subst (svar_open n0 fresh phi) psi X) x 0 _ _ ).
      reflexivity.
      (*x needs to be fresh in ...*)
      unfold svar_open in *.
      rewrite -> IHsz. reflexivity. simpl in Hsz. lia. assumption. simpl in Hfresh2. apply svar_is_fresh_in_exists in Hfresh1. assumption.
      apply svar_is_fresh_in_exists in Hfresh2. assumption. assumption.
    - remember ((free_svars (svar_open (S n0) fresh (free_svar_subst phi psi X)) ∪
                            (free_svars (free_svar_subst (svar_open (S n0) fresh phi) psi X)))) as B.
      simpl. remember (@svar_fresh (elements B)) as X'.
      assert(X' ∉ B).
      {
        subst. apply set_svar_fresh_is_fresh'.
      }
      subst B.  apply not_elem_of_union in H. destruct H.
      simpl. unfold svar_open in *. rewrite bsvar_subst_mu.

      f_equal.
      fold free_svar_subst.
      fold (svar_open (S n0) fresh (free_svar_subst phi psi X)).
      erewrite (@svar_open_inj (svar_open (S n0) fresh (free_svar_subst phi psi X)) (free_svar_subst (svar_open (S n0) fresh phi) psi X) X' 0 _ _ ).
      { reflexivity. }
      (*x needs to be fresh in ...*)
      unfold svar_open in *.
      rewrite -> IHsz. reflexivity. simpl in Hsz. lia. assumption. simpl in Hfresh2. assumption.
      simpl in Hfresh2.
      apply -> svar_is_fresh_in_mu in Hfresh2. 2: auto.
      fold free_svar_subst in *. auto.
      Unshelve. all: assumption.
  Qed.

  Corollary svar_open_free_svar_subst_comm : ∀ phi psi fresh n X,
      (well_formed_closed_mu_aux psi 0) →  
      svar_is_fresh_in fresh phi → svar_is_fresh_in fresh (free_svar_subst phi psi X) → (fresh ≠ X) 
      →
      (svar_open n fresh (free_svar_subst phi psi X)) = 
      (free_svar_subst (svar_open n fresh phi) psi X).
  Proof.
    intros phi psi fresh n X H H0 H1 H2. apply (Private_svar_open_free_svar_subst_comm) with (sz := (size phi)); try lia; try assumption.
  Qed.

(* TODO: deprecated

  Lemma wfc_mu_nest_ex level level' more q:
    well_formed_closed_mu_aux (nest_ex_aux level' more q) level =
    well_formed_closed_mu_aux q level.
  Proof.
    move: level level' more.
    induction q; intros level level' more; simpl; auto.
    - rewrite IHq1. rewrite IHq2. reflexivity.
    - rewrite IHq1. rewrite IHq2. reflexivity.
  Qed.

  Lemma wfc_ex_nest_mu level level' more q:
    well_formed_closed_ex_aux (nest_mu_aux level' more q) level =
    well_formed_closed_ex_aux q level.
  Proof.
    move: level level' more.
    induction q; intros level level' more; simpl; auto.
    - rewrite IHq1. rewrite IHq2. reflexivity.
    - rewrite IHq1. rewrite IHq2. reflexivity.
  Qed. *)

  Lemma free_evar_subst_preserves_no_negative_occurrence x p q n:
    well_formed_closed_mu_aux q 0 ->
    no_negative_occurrence_db_b n p ->
    no_negative_occurrence_db_b n (free_evar_subst p q x)
  with
  free_evar_subst_preserves_no_positive_occurrence x p q n:
    well_formed_closed_mu_aux q 0 ->
    no_positive_occurrence_db_b n p ->
    no_positive_occurrence_db_b n (free_evar_subst p q x)
  .
  Proof.
    - intros wfq nno.
      unfold free_evar_subst.
      induction p; simpl; auto.
      + destruct (decide (x = x0)); simpl; auto.
        apply wfc_impl_no_neg_occ; auto.
      + simpl in nno. apply andb_prop in nno. destruct nno as [nnop1 nnop2].
        rewrite IHp1. auto. rewrite IHp2. auto. reflexivity.
      + simpl in nno. apply andb_prop in nno. destruct nno as [nnop1 nnop2].
        rewrite IHp2. assumption. rewrite free_evar_subst_preserves_no_positive_occurrence; auto. 
    - intros wfq npo.
      induction p; simpl; auto.
      + destruct (decide (x = x0)); simpl; auto.
        apply wfc_impl_no_pos_occ; auto.
      + simpl in npo. apply andb_prop in npo. destruct npo as [npop1 npop2].
        rewrite IHp1. auto. rewrite IHp2. auto. reflexivity.
      + simpl in npo. apply andb_prop in npo. destruct npo as [npop1 npop2].
        rewrite IHp2. assumption. rewrite free_evar_subst_preserves_no_negative_occurrence; auto.
  Qed.

(*   TODO: deprecated
  Lemma nno_nest_ex_aux level more q db:
    no_negative_occurrence_db_b db (nest_ex_aux level more q)
    = no_negative_occurrence_db_b db q
  with npo_nest_ex_aux level more q db:
    no_positive_occurrence_db_b db (nest_ex_aux level more q)
    = no_positive_occurrence_db_b db q.
  Proof.
    - move: level more db.
      induction q; intros level more db; simpl; auto.
      + rewrite IHq1. rewrite IHq2. reflexivity.
      + rewrite npo_nest_ex_aux. rewrite IHq2. reflexivity.
    - move: level more db.
      induction q; intros level more db; simpl; auto.
      + rewrite IHq1. rewrite IHq2. reflexivity.
      + rewrite nno_nest_ex_aux. rewrite IHq2. reflexivity.
  Qed.
  
        

  Lemma wfp_nest_ex_aux level more q:
    well_formed_positive (nest_ex_aux level more q)
    = well_formed_positive q.
  Proof.
    move: level more.
    induction q; intros level more; simpl; auto.
    - rewrite IHq1. rewrite IHq2. reflexivity.
    - rewrite IHq1. rewrite IHq2. reflexivity.
    - rewrite IHq. rewrite nno_nest_ex_aux. reflexivity.
  Qed. *)
  
  Lemma Private_well_formed_free_evar_subst x p q n1 n2:
    well_formed q ->
    well_formed_positive p && well_formed_closed_mu_aux p n2 && well_formed_closed_ex_aux p n1 ->
    no_negative_occurrence_db_b n2 (free_evar_subst p q x)
    && no_positive_occurrence_db_b n2 (free_evar_subst p q x)
    && well_formed_positive (free_evar_subst p q x)
    && well_formed_closed_mu_aux (free_evar_subst p q x) n2
    && well_formed_closed_ex_aux (free_evar_subst p q x) n1
    = true.
  Proof.
    intros wfq wfp.
    move: n1 n2 wfp.
    induction p; intros n1 n2 wfp; simpl; auto.
    - destruct (decide (x = x0)); simpl; auto.
      unfold well_formed in wfq. apply andb_prop in wfq. destruct wfq as [wfpq wfcq].
      rewrite wfpq.
      (* rewrite wfp_nest_ex_aux.
      rewrite wfpq. simpl in *.*)
      unfold well_formed_closed in wfcq. destruct_and!.
      pose proof (H1' := @well_formed_closed_mu_aux_ind q 0 n2 ltac:(lia) H).
      pose proof (H2' := wfc_impl_no_neg_pos_occ H1').
      destruct_and!.
      
      split_and!; auto.
      + eapply well_formed_closed_ex_aux_ind.
        2: eassumption. lia.
    - simpl in *.
      destruct_and!. split_and!; auto.
      repeat case_match; lia.
    - unfold well_formed, well_formed_closed in *. simpl in *.
      destruct_and!.
      specialize (IHp1 n1 n2). specialize (IHp2 n1 n2).
      feed specialize IHp1.
      { split_and!; auto. }
      feed specialize IHp2.
      { split_and!; auto. }
      destruct_and!.
      split_and!; auto.
    - unfold well_formed, well_formed_closed in *. simpl in *.
      destruct_and!.
      specialize (IHp1 n1 n2). specialize (IHp2 n1 n2).
      feed specialize IHp1.
      { split_and!; auto. }
      feed specialize IHp2.
      { split_and!; auto. }
      destruct_and!.
      split_and!; auto.
    - unfold well_formed, well_formed_closed in *. simpl in *.
      destruct_and!.
      pose proof (IHp' := IHp).
      specialize (IHp n1 (S n2)).
      feed specialize IHp.
      { split_and!; auto. }
      destruct_and!.
      split_and!; auto.
      rewrite free_evar_subst_preserves_no_negative_occurrence; auto.
  Qed.

  Lemma well_formed_free_evar_subst x p q:
    well_formed q = true ->
    well_formed p = true ->
    well_formed (free_evar_subst p q x) = true.
  Proof.
    intros wfq wfp.
    pose proof (H := @Private_well_formed_free_evar_subst x p q 0 0 wfq).
    unfold well_formed,well_formed_closed in *.
    destruct_and!.
    feed specialize H.
    { split_and!; assumption. }
    destruct_and!. split_and!; auto.
  Qed.

  Lemma well_formed_free_evar_subst_0 x p q:
    well_formed q = true ->
    well_formed p = true ->
    well_formed (free_evar_subst p q x) = true.
  Proof.
    intros. apply well_formed_free_evar_subst; assumption.
  Qed.
  
  Fixpoint mu_free (p : Pattern) : bool :=
  match p with
   | patt_free_evar x => true
   | patt_free_svar x => true
   | patt_bound_evar n => true
   | patt_bound_svar n => true
   | patt_sym sigma => true
   | patt_app phi1 phi2 => mu_free phi1 && mu_free phi2
   | patt_bott => true
   | patt_imp phi1 phi2 => mu_free phi1 && mu_free phi2
   | patt_exists phi => mu_free phi
   | patt_mu phi => false
  end.

  (* Fragment of matching logic without set variables and mu *)
  Fixpoint set_free (p : Pattern) : bool :=
  match p with
   | patt_free_evar x => true
   | patt_free_svar x => false
   | patt_bound_evar n => true
   | patt_bound_svar n => false
   | patt_sym sigma => true
   | patt_app phi1 phi2 => set_free phi1 && set_free phi2
   | patt_bott => true
   | patt_imp phi1 phi2 => set_free phi1 && set_free phi2
   | patt_exists phi => set_free phi
   | patt_mu phi => false
  end.

  Lemma set_free_implies_mu_free p:
    set_free p = true -> mu_free p = true.
  Proof.
    intros H.
    induction p; simpl in *; destruct_and?; split_and?; auto.
  Qed.

  Lemma well_formed_positive_bevar_subst φ : forall n ψ,
    mu_free φ ->
    well_formed_positive φ = true -> well_formed_positive ψ = true
  ->
    well_formed_positive (bevar_subst φ ψ n) = true.
  Proof.
    induction φ; intros n' ψ H H0 H1; simpl; auto.
    2-3: apply andb_true_iff in H as [E1 E2];
         simpl in H0; apply eq_sym, andb_true_eq in H0; destruct H0; 
         rewrite -> IHφ1, -> IHφ2; auto.
    * break_match_goal; auto.
  Qed.

  Lemma mu_free_bevar_subst :
    forall φ ψ, mu_free φ -> mu_free ψ -> forall n, mu_free (bevar_subst φ ψ n).
  Proof.
    induction φ; intros ψ H H0 n'; simpl; try now constructor.
    * break_match_goal; auto.
    * simpl in H. apply andb_true_iff in H as [E1 E2]. now rewrite -> IHφ1, -> IHφ2.
    * simpl in H. apply andb_true_iff in H as [E1 E2]. now rewrite -> IHφ1, -> IHφ2.
    * simpl in H. now apply IHφ.
    * inversion H.
  Qed.

  Corollary mu_free_evar_open :
    forall φ, mu_free φ -> forall x n, mu_free (evar_open n x φ).
  Proof.
    intros φ H x n. apply mu_free_bevar_subst; auto.
  Qed.

  Theorem evar_open_free_evar_subst_swap :
    forall φ x n ψ y, x <> y -> well_formed ψ ->
      evar_open n x (free_evar_subst φ ψ y) = free_evar_subst (evar_open n x φ) ψ y.
  Proof.
    induction φ; intros x' n' ψ y H H0; simpl; auto.
    * destruct (decide (y = x)); simpl.
      ** rewrite evar_open_wfc; auto. unfold well_formed,well_formed_closed in H0. destruct_and!.
         assumption.
      ** reflexivity.
    * cbn. break_match_goal; simpl; auto. destruct (decide (y = x')); auto.
      congruence.
    * unfold evar_open in *. now rewrite -> bevar_subst_app, -> IHφ1, -> IHφ2.
    * unfold evar_open in *. now rewrite -> bevar_subst_imp, -> IHφ1, -> IHφ2.
    * unfold evar_open in *. now rewrite -> bevar_subst_exists, -> IHφ.
    * unfold evar_open in *. now rewrite -> bevar_subst_mu, -> IHφ.
  Qed.

  Lemma free_evars_free_evar_subst : forall φ ψ x,
    free_evars (free_evar_subst φ ψ x) ⊆ free_evars φ ∪ free_evars ψ.
  Proof.
    induction φ; intros ψ x'; simpl.
    2-5, 7: apply empty_subseteq.
    * destruct (decide (x' = x)); simpl.
      ** apply union_subseteq_r.
      ** apply union_subseteq_l.
    * specialize (IHφ1 ψ x'). specialize (IHφ2 ψ x').
      set_solver.
    * specialize (IHφ1 ψ x'). specialize (IHφ2 ψ x').
      set_solver.
    * apply IHφ.
    * apply IHφ.
  Qed.


  Lemma bound_to_free_variable_subst :
    forall φ x m n ψ,
      m > n ->
      well_formed_closed_ex_aux ψ 0 ->
      well_formed_closed_ex_aux φ m -> x ∉ free_evars φ ->
      bevar_subst φ ψ n = free_evar_subst (evar_open n x φ) ψ x.
  Proof.
    induction φ; intros x' m n' ψ H WFψ H0 H1; cbn; auto.
    - destruct (decide (x' = x)); simpl.
      + simpl in H1. apply not_elem_of_singleton_1 in H1. congruence.
      + reflexivity.
    - case_match; auto. simpl. case_match; auto; simpl in H0; case_match; auto.
      contradiction. lia.
    - simpl in H1. apply not_elem_of_union in H1. destruct H1. simpl in H0.
      apply andb_true_iff in H0. destruct H0.
      erewrite -> IHφ1, -> IHφ2. reflexivity. all: eassumption.
    - simpl in H1. apply not_elem_of_union in H1. destruct H1. simpl in H0.
      apply andb_true_iff in H0. destruct H0.
      erewrite -> IHφ1, -> IHφ2. reflexivity. all: eassumption.
    - simpl in H0, H1. erewrite IHφ. reflexivity. instantiate (1 := S m). 
      all: try eassumption. lia.
    - simpl in H0, H1. erewrite IHφ. reflexivity. all: eassumption.
  Qed.

  Lemma bound_to_free_set_variable_subst :
    forall φ X m n ψ,
      m > n ->
      well_formed_closed_mu_aux ψ 0 ->
      well_formed_closed_mu_aux φ m -> X ∉ free_svars φ ->
      bsvar_subst φ ψ n = free_svar_subst (svar_open n X φ) ψ X.
  Proof.
    induction φ; intros x' m n' ψ H WFψ H0 H1; cbn; auto.
    - destruct (decide (x' = x)); simpl.
      + simpl in H1. apply not_elem_of_singleton_1 in H1. congruence.
      + reflexivity.
    - case_match; auto. simpl. case_match; auto; simpl in H0; case_match; auto.
      contradiction. lia.
    - simpl in H1. apply not_elem_of_union in H1. destruct H1. simpl in H0.
      apply andb_true_iff in H0. destruct H0.
      erewrite -> IHφ1, -> IHφ2. reflexivity. all: eassumption.
    - simpl in H1. apply not_elem_of_union in H1. destruct H1. simpl in H0.
      apply andb_true_iff in H0. destruct H0.
      erewrite -> IHφ1, -> IHφ2. reflexivity. all: eassumption.
    - simpl in H0, H1. erewrite IHφ. reflexivity. all: eassumption.
    - simpl in H0, H1. erewrite IHφ. reflexivity. instantiate (1 := S m). 
      all: try eassumption. lia.
  Qed.

  Lemma evar_open_no_negative_occurrence :
    forall φ db1 db2 x,
      (no_negative_occurrence_db_b db1 (evar_open db2 x φ) ->
      no_negative_occurrence_db_b db1 φ) /\
      (no_positive_occurrence_db_b db1 (evar_open db2 x φ) ->
      no_positive_occurrence_db_b db1 φ).
  Proof.
    induction φ; intros db1 db2 x'; simpl; auto.
    * split; intros.
      - apply andb_true_iff in H as [E1 E2].
        apply IHφ1 in E1. apply IHφ2 in E2. now rewrite -> E1, -> E2.
      - apply andb_true_iff in H as [E1 E2].
        apply IHφ1 in E1. apply IHφ2 in E2. now rewrite -> E1, -> E2.
    * split; intros.
      - apply andb_true_iff in H as [E1 E2].
        apply IHφ1 in E1. apply IHφ2 in E2. now rewrite -> E1, -> E2.
      - apply andb_true_iff in H as [E1 E2].
        apply IHφ1 in E1. apply IHφ2 in E2. now rewrite -> E1, -> E2.
   * split; intros; eapply IHφ; eassumption.
   * split; intros; eapply IHφ; eassumption.
  Qed.

  Lemma evar_open_positive : forall φ n x,
    well_formed_positive (evar_open n x φ) = true ->
    well_formed_positive φ = true.
  Proof.
    induction φ; intros n' x' H; cbn; auto.
    * simpl in H. apply andb_true_iff in H as [E1 E2].
      erewrite -> IHφ1, -> IHφ2; eauto.
    * simpl in H. apply andb_true_iff in H as [E1 E2].
      erewrite -> IHφ1, -> IHφ2; eauto.
    * simpl in H. eapply IHφ; eauto.
    * simpl in H. apply andb_true_iff in H as [E1 E2].
      apply andb_true_iff. split.
      eapply evar_open_no_negative_occurrence. eassumption.
      eapply IHφ; eauto.
  Qed.

(* TODO: deprecated
  Lemma wf_body_ex_to_wf :
    forall φ, wf_body_ex φ -> well_formed (patt_exists φ) = true.
  Proof.
    intros φ H. unfold well_formed, well_formed_closed. simpl.
    remember (fresh_evar φ) as x.
    assert (x ∉ free_evars φ) by now apply x_eq_fresh_impl_x_notin_free_evars.
    specialize (H x H0).
    apply andb_true_iff in H. destruct H.
    apply evar_open_positive in H.
    unfold well_formed_closed in *.
    destruct_and!.
    apply wfc_ex_aux_body_ex_imp2 in H3.
    apply wfc_mu_aux_body_ex_imp2 in H2.
    split_and!; auto.
  Qed. *)

  Lemma bevar_subst_closed_mu :
    forall φ ψ n m,
    well_formed_closed_mu_aux φ m = true ->
    well_formed_closed_mu_aux ψ m = true
    ->
    well_formed_closed_mu_aux (bevar_subst φ ψ n) m = true.
  Proof.
    induction φ; intros ψ n' m H H0; cbn; auto.
    * break_match_goal; simpl in H0, H; simpl; auto.
    * simpl in H. apply andb_true_iff in H as [E1 E2]. erewrite IHφ1, IHφ2; auto.
    * simpl in H. apply andb_true_iff in H as [E1 E2]. erewrite IHφ1, IHφ2; auto.
    * simpl in H. rewrite -> IHφ; auto. eapply well_formed_closed_mu_aux_ind.
      2: eassumption. lia.
  Qed.

  Lemma bevar_subst_closed_ex :
    forall φ ψ n,
    well_formed_closed_ex_aux φ (S n) = true ->
    well_formed_closed_ex_aux ψ n = true
    ->
    well_formed_closed_ex_aux (bevar_subst φ ψ n) n = true.
  Proof.
    induction φ; intros ψ n' H H0; cbn; auto.
    * break_match_goal; simpl in H0, H; simpl; auto.
      repeat case_match; auto. do 2 case_match; auto; lia.
    * simpl in H. apply andb_true_iff in H as [E1 E2]. erewrite IHφ1, IHφ2; auto.
    * simpl in H. apply andb_true_iff in H as [E1 E2]. erewrite IHφ1, IHφ2; auto.
    * simpl in H. rewrite -> IHφ; auto. eapply well_formed_closed_ex_aux_ind.
      2: eassumption. lia.
  Qed.

  Lemma bevar_subst_positive :
    forall φ ψ n, mu_free φ ->
    well_formed_positive φ = true -> well_formed_positive ψ = true
   ->
    well_formed_positive (bevar_subst φ ψ n) = true.
  Proof.
    induction φ; intros ψ n' H H0 H1; cbn; auto.
    * break_match_goal; auto.
    * simpl in H. apply andb_true_iff in H as [E1 E2].
      apply andb_true_iff in H0 as [E1' E2'].
      rewrite -> IHφ1, -> IHφ2; auto.
    * simpl in H. apply andb_true_iff in H as [E1 E2].
      apply andb_true_iff in H0 as [E1' E2'].
      now rewrite -> IHφ1, -> IHφ2.
  Qed.

  Theorem evar_quantify_closed_ex :
    forall φ x n, well_formed_closed_ex_aux φ n ->
    well_formed_closed_ex_aux (evar_quantify x n φ) (S n) = true.
  Proof.
    induction φ; intros x' n' H; cbn; auto.
    * destruct (decide (x' = x)); simpl; auto.
      case_match; try lia.
    * simpl in H. repeat case_match; auto; lia.
    * simpl in H. apply andb_true_iff in H as [E1 E2]. now rewrite -> IHφ1, -> IHφ2.
    * simpl in H. apply andb_true_iff in H as [E1 E2]. now rewrite -> IHφ1, -> IHφ2. 
  Qed.

  Theorem svar_quantify_closed_mu :
    forall φ X n, well_formed_closed_mu_aux φ n ->
    well_formed_closed_mu_aux (svar_quantify X n φ) (S n) = true.
  Proof.
    induction φ; intros x' n' H; cbn; auto.
    * destruct (decide (x' = x)); simpl; auto.
      case_match; try lia.
    * simpl in H. repeat case_match; auto; lia.
    * simpl in H. apply andb_true_iff in H as [E1 E2]. now rewrite -> IHφ1, -> IHφ2.
    * simpl in H. apply andb_true_iff in H as [E1 E2]. now rewrite -> IHφ1, -> IHφ2. 
  Qed.

  Theorem evar_quantify_closed_mu :
    forall φ x n m, well_formed_closed_mu_aux φ m ->
    well_formed_closed_mu_aux (evar_quantify x n φ) m = true.
  Proof.
    induction φ; intros x' n' m H; cbn; auto.
    - destruct (decide (x' = x)); simpl; auto.
    - simpl in H. repeat case_match; auto.
      destruct_and!. split_and!.
      + apply IHφ1. assumption.
      + apply IHφ2. assumption.
    - simpl in H. apply andb_true_iff in H as [E1 E2]. now rewrite -> IHφ1, -> IHφ2.
  Qed.

  Theorem svar_quantify_closed_ex :
    forall φ X n m, well_formed_closed_ex_aux φ m ->
    well_formed_closed_ex_aux (svar_quantify X n φ) m = true.
  Proof.
    induction φ; intros x' n' m H; cbn; auto.
    - destruct (decide (x' = x)); simpl; auto.
    - simpl in H. repeat case_match; auto.
      destruct_and!. split_and!.
      + apply IHφ1. assumption.
      + apply IHφ2. assumption.
    - simpl in H. apply andb_true_iff in H as [E1 E2]. now rewrite -> IHφ1, -> IHφ2.
  Qed.
  
  Theorem no_occ_quantify : 
    ∀ (φ : Pattern) (db1 db2 : db_index) (x : evar),
    (no_negative_occurrence_db_b db1 φ
     → no_negative_occurrence_db_b db1 (evar_quantify x db2 φ))
    ∧ (no_positive_occurrence_db_b db1 φ
       → no_positive_occurrence_db_b db1 (evar_quantify x db2 φ)).
  Proof.
    induction φ; split; intros H; simpl; auto.
    1-2: destruct (decide (x0 = x)); simpl; auto.
    1-4: simpl in H; apply andb_true_iff in H as [E1 E2];
         specialize (IHφ1 db1 db2 x) as [IH1 IH2];
         specialize (IHφ2 db1 db2 x) as [IH1' IH2'];
         try rewrite -> IH1; try rewrite -> IH1'; 
         try rewrite -> IH2; try rewrite -> IH2'; auto.
    1-4: simpl in H; now apply IHφ.
  Qed.
  
  Theorem evar_quantify_positive :
    forall φ x n, well_formed_positive φ ->
    well_formed_positive (evar_quantify x n φ) = true.
  Proof.
    induction φ; intros x' n' H; cbn; auto.
    * destruct (decide (x' = x)); simpl; auto.
    * simpl in H. apply andb_true_iff in H as [E1 E2]. now rewrite -> IHφ1, -> IHφ2.
    * simpl in H. apply andb_true_iff in H as [E1 E2]. now rewrite -> IHφ1, -> IHφ2.
    * simpl in H. apply andb_true_iff in H as [E1 E2]. apply andb_true_iff. split.
      - now apply no_occ_quantify.
      - now apply IHφ.
  Qed.

  Corollary evar_quantify_well_formed :
    forall φ x, well_formed φ ->
      well_formed (patt_exists (evar_quantify x 0 φ)) = true.
  Proof.
    intros φ x H.
    unfold well_formed, well_formed_closed in *.
    destruct_and!.
    split_and!; simpl.
    - apply evar_quantify_positive. assumption.
    - apply evar_quantify_closed_mu. assumption.
    - apply evar_quantify_closed_ex. assumption.
  Qed.

  Theorem evar_quantify_not_free :
    forall φ x n, x ∉ (free_evars (evar_quantify x n φ)).
  Proof.
    induction φ; intros x' n'; simpl.
    2-5, 7: apply not_elem_of_empty.
    * destruct (decide (x' = x)); simpl.
      - apply not_elem_of_empty.
      - subst. now apply not_elem_of_singleton_2.
    * apply not_elem_of_union. split. apply IHφ1. apply IHφ2.
    * apply not_elem_of_union. split. apply IHφ1. apply IHφ2.
    * apply IHφ.
    * apply IHφ.
  Qed.

  Theorem svar_quantify_not_free :
    forall φ X n, X ∉ (free_svars (svar_quantify X n φ)).
  Proof.
    induction φ; intros x' n'; simpl; try set_solver.
    case_match; simpl; set_solver.
  Qed.

  Fixpoint wf_PatCtx (C : PatCtx) : bool :=
  match C with
   | pctx_box => true
   | pctx_app_l C r => well_formed r && wf_PatCtx C
   | pctx_app_r l C => well_formed l && wf_PatCtx C
   | pctx_imp_l C r => well_formed r && wf_PatCtx C
   | pctx_imp_r l C => well_formed l && wf_PatCtx C
   | pctx_exists x C => wf_PatCtx C
  end.


  Theorem subst_patctx_wf :
    forall C φ, wf_PatCtx C -> well_formed φ
  ->
    well_formed (subst_patctx C φ) = true.
  Proof.
    induction C; intros φ WFC WFφ; simpl; auto.
    * apply andb_true_iff in WFC as [E1 E2]. apply well_formed_app; auto.
    * apply andb_true_iff in WFC as [E1 E2]. apply well_formed_app; auto.
    * apply andb_true_iff in WFC as [E1 E2]. apply well_formed_app; auto.
    * apply andb_true_iff in WFC as [E1 E2]. apply well_formed_app; auto.
    * simpl in WFC. eapply IHC in WFC; eauto.
      now apply evar_quantify_well_formed.
  Qed.

  (* FIXME: rename! *)
  Lemma evar_quantify_noop :
    forall φ x n, count_evar_occurrences x φ = 0 ->
    evar_quantify x n φ = φ.
  Proof.
    induction φ; intros x' n' H; simpl; auto.
    - simpl in H.
      destruct (decide (x = x')).
      + subst x'. destruct (decide (x = x)). simpl in H. inversion H. contradiction.
      + simpl in H. destruct (decide (x' = x)); cbn; auto. congruence.
    - simpl in H. rewrite IHφ1. lia. rewrite IHφ2. lia. reflexivity.
    - simpl in H. rewrite IHφ1. lia. rewrite IHφ2. lia. reflexivity.
    - simpl in H. rewrite IHφ. lia. reflexivity.
    - simpl in H. rewrite IHφ. lia. reflexivity.
  Qed.

End syntax.

Module Notations.
  Declare Scope ml_scope.
  Delimit Scope ml_scope with ml.
  (* TODO: change Bot and Top to unicode symbols *)
  Notation "a $ b" := (patt_app a b) (at level 65, right associativity) : ml_scope.
  Notation "'Bot'" := patt_bott : ml_scope.
  Notation "⊥" := patt_bott : ml_scope.
  Notation "a ---> b"  := (patt_imp a b) (at level 75, right associativity) : ml_scope.
  Notation "'ex' , phi" := (patt_exists phi) (at level 70) : ml_scope.
  Notation "'mu' , phi" := (patt_mu phi) (at level 70) : ml_scope.

  (*Notation "AC [ p ]" := (subst_ctx AC p) (at level 90) : ml_scope.*)
  Notation "C [ p ]" := (emplace C p) (at level 90) : ml_scope.

  Notation "e .[ 'evar:' dbi ↦ e' ]" := (bevar_subst e e' dbi) (at level 2, e' at level 200, left associativity,
   format "e .[ 'evar:' dbi ↦ e' ]" ).
  Notation "e .[ 'svar:' dbi ↦ e' ]" := (bsvar_subst e e' dbi) (at level 2, e' at level 200, left associativity,
   format "e .[ 'svar:' dbi ↦ e' ]" ).
  Notation "e .[[ 'evar:' x ↦ e' ]]" := (free_evar_subst e e' x) (at level 2, e' at level 200, left associativity,
   format "e .[[ 'evar:' x ↦ e' ]]" ).
  Notation "e .[[ 'svar:' X ↦ e' ]]" := (free_svar_subst e e' X) (at level 2, e' at level 200, left associativity,
   format "e .[[ 'svar:' X ↦ e' ]]" ).
  Notation "e . [ e' ]" := (instantiate e e') (at level 2, e' at level 200, left associativity).

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

#[export]
 Hint Extern 0 (is_true (@well_formed _ _)) => unfold is_true : core.

#[export]
 Hint Resolve well_formed_bott : core.

#[export]
 Hint Resolve well_formed_imp : core.

#[export]
 Hint Resolve well_formed_app : core.

#[export]
 Hint Resolve wf_sctx : core.

#[export]
 Hint Resolve well_formed_ex_app : core.

#[export]
 Hint Resolve well_formed_impl_well_formed_ex : core.

#[export]
 Hint Resolve well_formed_free_evar_subst : core.

#[export]
 Hint Resolve well_formed_free_evar_subst_0 : core.

#[export]
 Hint Resolve <- evar_is_fresh_in_exists : core.

#[export]
 Hint Resolve evar_is_fresh_in_evar_quantify : core.

(* Tactics for resolving goals involving sets *)

Ltac simpl_bevar_subst := repeat (rewrite simpl_bevar_subst';[reflexivity|]).
Ltac simpl_bsvar_subst := repeat (rewrite simpl_bsvar_subst';[reflexivity|]).

Tactic Notation "solve_free_evars_inclusion" int_or_var(depth) :=
  simpl;
  (do ? [rewrite simpl_free_evars/=]) ;
  auto;
  clear;
  set_solver.

Tactic Notation "solve_free_svars_inclusion" int_or_var(depth) :=
  simpl;
  (do ? [rewrite simpl_free_svars/=]) ;
  auto;
  clear;
  set_solver.
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

Ltac remember_fresh_evars :=
  unfold fresh_evar in *;
  repeat(
      match goal with
      | |- context G [evar_fresh ?Y] =>
        match goal with
        | H: ?X = evar_fresh Y |- _ => fail 2
        | _ => remember (evar_fresh Y)
        end
      | H1: context G [evar_fresh ?Y] |- _ =>
        match goal with
        | H2: ?X = evar_fresh Y |- _ => fail 2
        | _ => remember (evar_fresh Y)
        end
      end
    ).


(* assumes a goal `x₁ ≠ x₂` and a hypothesis of the shape `x₁ = fresh_evar ...`
     or `x₂ = fresh_evar ...`
 *)
Ltac solve_fresh_neq :=
  subst; remember_fresh_evars;
  repeat (
      match goal with
      | Heq: (eq ?x ?t) |- not (eq ?x ?y) =>
        pose proof (X_eq_evar_fresh_impl_X_notin_S Heq); clear Heq
      | Heq: (eq ?x ?t) |- not (eq ?y ?x) =>
        pose proof (X_eq_evar_fresh_impl_X_notin_S Heq); clear Heq
      end
    );
  (idtac + apply nesym);
  match goal with
  | H: not (elem_of ?x ?S) |- not (eq ?x ?y) =>
    simpl in H;
    (do ? rewrite simpl_free_evars/= in H);
    auto;
    rewrite -?union_assoc_L in H;
    repeat (
        match goal with
        | H: (not (elem_of ?x (singleton ?y))) |- _ =>
          apply not_elem_of_singleton_1 in H;
          first [ exact H | clear H]
        | H: (not (elem_of ?x (union ?l ?r))) |- _ => (apply not_elem_of_union in H; destruct H)
        end
      );
    fail
  end.


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
    auto;
    rewrite -?union_assoc_L in H;
    repeat (
        match goal with
        | H: (not (elem_of ?x (singleton ?y))) |- _ =>
          apply not_elem_of_singleton_1 in H;
          first [ exact H | clear H]
        | H: (not (elem_of ?x (union ?l ?r))) |- _ => (apply not_elem_of_union in H; destruct H)
        end
      );
    fail
  end.

Section with_signature.
  Context {Σ : Signature}.

  Lemma evar_is_fresh_in_subst_ctx x AC p:
    evar_is_fresh_in x (subst_ctx AC p)
    <-> (evar_is_fresh_in x p /\ x ∉ AC_free_evars AC).
  Proof.
    induction AC.
    - simpl. split; set_solver.
    - simpl. split; intros H.
      + assert (Hfr1: evar_is_fresh_in x (subst_ctx AC p)).
        { eapply evar_is_fresh_in_richer. 2: apply H. solve_free_evars_inclusion 5. }
        assert (Hfr2: evar_is_fresh_in x p0).
        { eapply evar_is_fresh_in_richer. 2: apply H. solve_free_evars_inclusion 5. }
        rewrite -> IHAC in Hfr1.
        split; [apply Hfr1|].
        clear -Hfr1 Hfr2.
        unfold evar_is_fresh_in in Hfr2.
        set_solver.
      + destruct H as [H1 H2].
        rewrite -> evar_is_fresh_in_app.
        split.
        * rewrite -> IHAC. set_solver.
        * unfold evar_is_fresh_in. set_solver.
    - simpl. split; intros H.
      + assert (Hfr1: evar_is_fresh_in x (subst_ctx AC p)).
        { eapply evar_is_fresh_in_richer. 2: apply H. solve_free_evars_inclusion 5. }
        assert (Hfr2: evar_is_fresh_in x p0).
        { eapply evar_is_fresh_in_richer. 2: apply H. solve_free_evars_inclusion 5. }
        rewrite -> IHAC in Hfr1.
        split; [apply Hfr1|].
        clear -Hfr1 Hfr2.
        unfold evar_is_fresh_in in Hfr2.
        set_solver.
      + destruct H as [H1 H2].
        rewrite -> evar_is_fresh_in_app.
        split.
        * unfold evar_is_fresh_in. set_solver.
        * rewrite -> IHAC. set_solver.
  Qed.

  Lemma wf_ex_evar_quantify x p:
    well_formed p = true ->
    well_formed (patt_exists (evar_quantify x 0 p)) = true.
  Proof.
    intros Hwf.
    unfold well_formed,well_formed_closed in Hwf. simpl in Hwf.
    apply andb_prop in Hwf.
    destruct Hwf as [Hwfp Hwfc].
    simpl in Hwfp.
    unfold well_formed,well_formed_closed. simpl.
    apply andb_true_intro.
    split.
    - simpl. apply evar_quantify_positive. apply Hwfp.
    - unfold well_formed_closed.
      simpl.
      destruct_and!.
      split_and!.
      + apply evar_quantify_closed_mu. assumption.
      + apply evar_quantify_closed_ex. assumption.
  Qed.

  Lemma wf_ex_eq_sctx_eo AC x p:
    well_formed (patt_exists p) = true ->
    well_formed (patt_exists (evar_quantify x 0 (subst_ctx AC (evar_open 0 x p)))) = true.
  Proof.
    intros Hwf.
    unfold well_formed in Hwf.
    apply andb_prop in Hwf.
    destruct Hwf as [Hwfp Hwfc].
    simpl in Hwfp.
    unfold well_formed.
    apply andb_true_intro.
    split.
    - simpl. apply evar_quantify_positive.
      apply wp_sctx.
      apply wfp_evar_open.
      apply Hwfp.
    - unfold well_formed_closed.
      simpl.
      unfold well_formed_closed in *.
      destruct_and!.
      split_and!; simpl.
      + apply evar_quantify_closed_mu. apply wcmu_sctx.
        apply wfc_mu_aux_body_ex_imp1. simpl in *. assumption.
      + apply evar_quantify_closed_ex. apply wcex_sctx.
        apply wfc_ex_aux_body_ex_imp1. simpl in *. assumption.
  Qed.

  Lemma evar_quantify_fresh x n phi:
    evar_is_fresh_in x phi ->
    (evar_quantify x n phi) = phi.
  Proof.
    intros H.
    move: n H.
    induction phi; intros n' H; cbn; auto.
    - destruct (decide (x = x0)); subst; simpl.
      + unfold evar_is_fresh_in in H. simpl in H. set_solver.
      + reflexivity.
    - apply evar_is_fresh_in_app in H. destruct H as [H1 H2].
      rewrite IHphi1; auto.
      rewrite IHphi2; auto.
    - apply evar_is_fresh_in_imp in H. destruct H as [H1 H2].
      rewrite IHphi1; auto.
      rewrite IHphi2; auto.
    - apply evar_is_fresh_in_exists in H.
      rewrite IHphi; auto.
    - apply evar_is_fresh_in_mu in H.
      rewrite IHphi; auto.
  Qed.

  Lemma svar_quantify_fresh X n phi:
    svar_is_fresh_in X phi ->
    (svar_quantify X n phi) = phi.
  Proof.
    intros H.
    move: n H.
    induction phi; intros n' H; cbn; auto.
    - destruct (decide (X = x)); subst; simpl.
      + unfold svar_is_fresh_in in H. simpl in H. set_solver.
      + reflexivity.
    - apply svar_is_fresh_in_app in H. destruct H as [H1 H2].
      rewrite IHphi1; auto.
      rewrite IHphi2; auto.
    - apply svar_is_fresh_in_imp in H. destruct H as [H1 H2].
      rewrite IHphi1; auto.
      rewrite IHphi2; auto.
    - apply svar_is_fresh_in_exists in H.
      rewrite IHphi; auto.
    - apply svar_is_fresh_in_mu in H.
      rewrite IHphi; auto.
  Qed.

End with_signature.

Lemma wf_imp_wfc {Σ : Signature} ϕ:
  well_formed ϕ -> well_formed_closed ϕ.
Proof.
  intros H. apply andb_prop in H. tauto.
Qed.

#[export]
 Hint Resolve wf_imp_wfc : core.

#[export]
 Hint Resolve wfc_ex_implies_not_bevar_occur : core.

Lemma subst_ctx_bevar_subst {Σ : Signature} AC p q n:
  subst_ctx AC (bevar_subst p q n) = bevar_subst (subst_ctx AC p) q n.
Proof.
  induction AC.
  - reflexivity.
  - simpl. rewrite IHAC. clear IHAC.
    rewrite [bevar_subst p0 q n]bevar_subst_not_occur.
    2: { reflexivity. }
    unfold well_formed,well_formed_closed in Prf.
    destruct_and!.
    auto. eapply well_formed_closed_ex_aux_ind. 2: exact H2. lia.
  - simpl. rewrite IHAC. clear IHAC.
    rewrite [bevar_subst p0 q n]bevar_subst_not_occur.
    2: { reflexivity. }
    unfold well_formed,well_formed_closed in Prf.
    destruct_and!.
    auto. eapply well_formed_closed_ex_aux_ind. 2: exact H2. lia.
Qed.

Lemma free_evars_evar_quantify {Σ : Signature} x n p:
  free_evars (evar_quantify x n p) = free_evars p ∖ {[x]}.
Proof.
  move: n.
  induction p; intros n'; simpl; try set_solver.
  destruct (decide (x = x0)).
    + subst. simpl. set_solver.
    + simpl. set_solver.
Qed.

Lemma free_svars_svar_quantify {Σ : Signature} X n p:
  free_svars (svar_quantify X n p) = free_svars p ∖ {[X]}.
Proof.
  move: n.
  induction p; intros n'; simpl; try set_solver.
  destruct (decide (X = x)).
    + subst. simpl. set_solver.
    + simpl. set_solver.
Qed.

Lemma free_evar_subst_subst_ctx_independent {Σ : Signature} AC ϕ Xfr1 Xfr2:
  Xfr1 ∉ free_evars_ctx AC ->
  Xfr2 ∉ free_evars_ctx AC ->
  free_evar_subst (subst_ctx AC (patt_free_evar Xfr1)) ϕ Xfr1 =
  free_evar_subst (subst_ctx AC (patt_free_evar Xfr2)) ϕ Xfr2.
Proof.
  intros HXfr1 HXfr2.
  induction AC.
  - simpl.
    destruct (decide (Xfr1 = Xfr1)), (decide (Xfr2 = Xfr2)); simpl; try contradiction.
    reflexivity.
  - simpl in HXfr1. simpl in HXfr2.
    feed specialize IHAC.
    { set_solver. }
    { set_solver. }
    simpl. rewrite IHAC.
    rewrite [free_evar_subst p ϕ Xfr1]free_evar_subst_no_occurrence.
    { apply count_evar_occurrences_0. set_solver. }
    rewrite [free_evar_subst p ϕ Xfr2]free_evar_subst_no_occurrence.
    { apply count_evar_occurrences_0. set_solver. }
    reflexivity.
  - simpl in HXfr1. simpl in HXfr2.
    feed specialize IHAC.
    { set_solver. }
    { set_solver. }
    simpl. rewrite IHAC.
    rewrite [free_evar_subst p ϕ Xfr1]free_evar_subst_no_occurrence.
    { apply count_evar_occurrences_0. set_solver. }
    rewrite [free_evar_subst p ϕ Xfr2]free_evar_subst_no_occurrence.
    { apply count_evar_occurrences_0. set_solver. }
    reflexivity.
Qed.


Lemma emplace_subst_ctx {Σ : Signature} AC ϕ:
  emplace (ApplicationContext2PatternCtx AC) ϕ = subst_ctx AC ϕ.
Proof.
  induction AC.
  - unfold ApplicationContext2PatternCtx,ApplicationContext2PatternCtx'.
    unfold emplace. simpl. unfold free_evar_subst. simpl.
    destruct (decide (_ = _)); simpl.
    + reflexivity.
    + contradiction.
  - simpl.
    rewrite -IHAC.
    unfold ApplicationContext2PatternCtx,ApplicationContext2PatternCtx'.
    simpl.
    unfold emplace. unfold free_evar_subst. simpl.
    unfold ApplicationContext2Pattern.
    f_equal.
    2: { fold free_evar_subst.
      rewrite free_evar_subst_no_occurrence.
      2: { reflexivity. }
      apply count_evar_occurrences_0.
      eapply evar_is_fresh_in_richer'.
      2: { apply set_evar_fresh_is_fresh'. }
      clear. set_solver.
    }
    remember (evar_fresh (elements (free_evars_ctx AC ∪ free_evars p))) as Xfr1.
    remember (evar_fresh (elements (free_evars_ctx AC))) as Xfr2.
    apply free_evar_subst_subst_ctx_independent.
    { subst.
      eapply not_elem_of_larger_impl_not_elem_of.
      2: { apply set_evar_fresh_is_fresh'. }
      clear. set_solver.
    }
    { subst.
      eapply not_elem_of_larger_impl_not_elem_of.
      2: { apply set_evar_fresh_is_fresh'. }
      clear. set_solver.
    }
  - simpl.
    rewrite -IHAC.
    unfold ApplicationContext2PatternCtx,ApplicationContext2PatternCtx'.
    simpl.
    unfold emplace. unfold free_evar_subst. simpl.
    unfold ApplicationContext2Pattern.
    f_equal.
    { fold free_evar_subst.
      rewrite free_evar_subst_no_occurrence.
      2: { reflexivity. }
      apply count_evar_occurrences_0.
      eapply evar_is_fresh_in_richer'.
      2: { apply set_evar_fresh_is_fresh'. }
      clear. set_solver.
    }
    remember (evar_fresh (elements (free_evars_ctx AC ∪ free_evars p))) as Xfr1.
    remember (evar_fresh (elements (free_evars_ctx AC))) as Xfr2.
    apply free_evar_subst_subst_ctx_independent.
    { subst.
      eapply not_elem_of_larger_impl_not_elem_of.
      2: { apply set_evar_fresh_is_fresh'. }
      clear. set_solver.
    }
    { subst.
      eapply not_elem_of_larger_impl_not_elem_of.
      2: { apply set_evar_fresh_is_fresh'. }
      clear. set_solver.
    }
Qed.



Definition evar_quantify_ctx {Σ : Signature} (x : evar) (n : db_index) (C : PatternCtx) : PatternCtx :=
  match decide (x = pcEvar C)  with
  | left _ => C
  | right pf => @Build_PatternCtx Σ (pcEvar C) (evar_quantify x n (pcPattern C))
  end.

Lemma is_linear_context_evar_quantify {Σ : Signature} (x : evar) (n : db_index) (C : PatternCtx) :
  is_linear_context C ->
  is_linear_context (evar_quantify_ctx x n C).
Proof.
  intros Hlin. unfold evar_quantify_ctx.
  unfold is_linear_context in *.
  destruct (decide (x = pcEvar C)); simpl.
  - assumption.
  - destruct C. simpl in *.

    assert (count_evar_occurrences pcEvar0 (evar_quantify x n pcPattern0)
            = count_evar_occurrences pcEvar0 pcPattern0).
    {
      clear Hlin.
      move: n.
      induction pcPattern0; intros n'; simpl in *; try lia.
      + destruct (decide (x0 = pcEvar0)); subst; simpl in *.
        * destruct (decide (x = pcEvar0)); try contradiction; simpl in *.
          destruct (decide (pcEvar0 = pcEvar0)); try contradiction. reflexivity.
        * destruct (decide (x = x0)); simpl; try reflexivity.
          destruct (decide (x0 = pcEvar0)); try contradiction.
          reflexivity.
      + rewrite IHpcPattern0_1. rewrite IHpcPattern0_2. reflexivity.
      + rewrite IHpcPattern0_1. rewrite IHpcPattern0_2. reflexivity.
      + rewrite IHpcPattern0. reflexivity.
      + rewrite IHpcPattern0. reflexivity.
    }
    congruence.
Qed.

Definition svar_quantify_ctx {Σ : Signature} (X : svar) (n : db_index) (C : PatternCtx) : PatternCtx :=
  @Build_PatternCtx Σ (pcEvar C) (svar_quantify X n (pcPattern C)).

Lemma is_linear_context_svar_quantify {Σ : Signature} (X : svar) (n : db_index) (C : PatternCtx) :
  is_linear_context C ->
  is_linear_context (svar_quantify_ctx X n C).
Proof.
  intros Hlin. unfold svar_quantify_ctx. unfold is_linear_context in *.
  destruct C. simpl in *.

  assert (count_evar_occurrences pcEvar0 (svar_quantify X n pcPattern0)
          = count_evar_occurrences pcEvar0 pcPattern0).
  {
    clear Hlin.
    move: n.
    induction pcPattern0; intros n'; simpl in *; try lia.
    + case_match; subst; simpl in *; reflexivity.
    + rewrite IHpcPattern0_1. rewrite IHpcPattern0_2. reflexivity.
    + rewrite IHpcPattern0_1. rewrite IHpcPattern0_2. reflexivity.
    + rewrite IHpcPattern0. reflexivity.
    + rewrite IHpcPattern0. reflexivity.
  }
  congruence.
Qed.

(* TODO: deprecated
  Lemma evar_quantify_nest_ex_aux {Σ : Signature} more level x n' ϕ:
  n' >= level ->
  evar_quantify x (n' + more) (nest_ex_aux level more ϕ) = nest_ex_aux level more (evar_quantify x n' ϕ).
Proof.
  intros Hlevel.
  move: more n' level Hlevel.
  induction ϕ; intros more n' level Hlevel; simpl; auto.
  - repeat case_match; simpl. 2: reflexivity. case_match. lia. reflexivity.
  - rewrite IHϕ1. lia. rewrite IHϕ2. lia. reflexivity.
  - rewrite IHϕ1. lia. rewrite IHϕ2. lia. reflexivity.
  - replace (S (n' + more)) with ((S n') + more) by lia.
    rewrite IHϕ. lia. reflexivity.
  - rewrite IHϕ. lia. reflexivity.
Qed.


Lemma svar_quantify_nest_mu_aux {Σ : Signature} more level X n' ϕ:
  n' >= level ->
  svar_quantify X (n' + more) (nest_mu_aux level more ϕ) = nest_mu_aux level more (svar_quantify X n' ϕ).
Proof.
  intros Hlevel.
  move: more n' level Hlevel.
  induction ϕ; intros more n' level Hlevel; simpl; auto.
  - repeat case_match; simpl. 2: reflexivity. case_match. lia. reflexivity.
  - rewrite IHϕ1. lia. rewrite IHϕ2. lia. reflexivity.
  - rewrite IHϕ1. lia. rewrite IHϕ2. lia. reflexivity.
  - rewrite IHϕ. lia. reflexivity.
  - replace (S (n' + more)) with ((S n') + more) by lia.
    rewrite IHϕ. lia. reflexivity.
Qed. *)

(* TODO: deprecated

  Lemma evar_quantify_free_evar_subst {Σ : Signature} ψ ϕ x n:
  evar_quantify x n (free_evar_subst ψ ϕ x) =
  free_evar_subst ψ (evar_quantify x n ϕ) x.
Proof.
  move: n.
  induction ψ; intros n'; simpl; auto.
  - case_match; auto.
    simpl. rewrite Heqs. reflexivity.
  - congruence.
  - congruence.
  - rewrite (IHψ). reflexivity.
  - rewrite IHψ. reflexivity.
Qed.

Lemma svar_quantify_free_svar_subst' {Σ : Signature} ψ ϕ X n :
  svar_quantify X n (free_svar_subst ψ ϕ X) =
  free_svar_subst' ψ (svar_quantify X n ϕ) X.
Proof.
  move: n more.
  induction ψ; intros n' more; simpl; auto.
  - case_match; auto.
    2: { simpl. case_match; try contradiction. reflexivity. }
    rewrite svar_quantify_nest_mu_aux. lia. reflexivity.
  - congruence.
  - congruence.
  - rewrite IHψ. reflexivity.
  - replace (S (n' + more)) with (n' + (S more)) by lia.
    rewrite IHψ. reflexivity.
Qed.

Lemma evar_quantify_free_evar_subst'_2 {Σ : Signature} n more ψ ϕ x y:
  x <> y ->
  evar_quantify x (n+more) (free_evar_subst' more ψ ϕ y)
  = free_evar_subst' more (evar_quantify x (n+more) ψ) (evar_quantify x n ϕ) y.
Proof.
  intros Hxy.
  move: n more.
  induction ψ; intros n' more; simpl; auto.
  - repeat case_match; simpl; auto.
    + congruence.
    + case_match; try congruence.
      apply evar_quantify_nest_ex_aux. lia.
    + case_match; congruence.
    + repeat case_match; auto; congruence.
  - rewrite IHψ1. rewrite IHψ2. reflexivity.
  - rewrite IHψ1. rewrite IHψ2. reflexivity.
  - replace (S (n' + more)) with (n' + (S more)) by lia.
    rewrite IHψ. reflexivity.
  - rewrite IHψ. reflexivity.
Qed.


Lemma svar_quantify_free_svar_subst'_2 {Σ : Signature} n more ψ ϕ X Y:
  X <> Y ->
  svar_quantify X (n+more) (free_svar_subst' more ψ ϕ Y)
  = free_svar_subst' more (svar_quantify X (n+more) ψ) (svar_quantify X n ϕ) Y.
Proof.
  intros Hxy.
  move: n more.
  induction ψ; intros n' more; simpl; auto.
  - repeat case_match; simpl; auto.
    + congruence.
    + case_match; try congruence.
      apply svar_quantify_nest_mu_aux. lia.
    + case_match; congruence.
    + repeat case_match; auto; congruence.
  - rewrite IHψ1. rewrite IHψ2. reflexivity.
  - rewrite IHψ1. rewrite IHψ2. reflexivity.
  - rewrite IHψ. reflexivity.    
  - replace (S (n' + more)) with (n' + (S more)) by lia.
    rewrite IHψ. reflexivity.
Qed.


Lemma evar_quantify_emplace {Σ : Signature} x n C ϕ:
  evar_quantify x n (emplace C ϕ) = emplace (evar_quantify_ctx x n C) (evar_quantify x n ϕ).
Proof.
  destruct C.
  unfold evar_quantify_ctx. simpl.
  case_match.
  { subst x.
    unfold emplace. simpl. unfold free_evar_subst.
    replace n with (n+0) at 1 by lia.
    apply evar_quantify_free_evar_subst'.
  }
  unfold emplace. simpl.
  unfold free_evar_subst.
  replace n with (n+0) at 1 by lia.
  rewrite -> evar_quantify_free_evar_subst'_2. 2: assumption.
  replace (n + 0) with n by lia. reflexivity.
Qed.

Lemma svar_quantify_nest_ex_aux {Σ : Signature} level more ϕ X n:
  svar_quantify X n (nest_ex_aux level more ϕ) = nest_ex_aux level more (svar_quantify X n ϕ).
Proof.
  move: level more n.
  induction ϕ; intros level more n'; simpl; auto.
  - case_match; reflexivity.
  - rewrite IHϕ1. rewrite IHϕ2. reflexivity.
  - rewrite IHϕ1. rewrite IHϕ2. reflexivity.
  - rewrite IHϕ. reflexivity.
  - rewrite IHϕ. reflexivity.
Qed.*)

Lemma svar_quantify_free_evar_subst {Σ : Signature} ψ ϕ x X n:
  svar_quantify X n (free_evar_subst ψ ϕ x) =
  free_evar_subst (svar_quantify X n ψ) (svar_quantify X n ϕ) x.
Proof.
  move: n.
  induction ψ; intros n'; simpl; auto.
  - case_match.
    + auto.
    + simpl. reflexivity.
  - case_match; reflexivity.
  - rewrite IHψ1. rewrite IHψ2. reflexivity.
  - rewrite IHψ1. rewrite IHψ2. reflexivity.
  - rewrite IHψ. reflexivity.
  - rewrite IHψ. Fail reflexivity.
Abort. (* OOPS, does not hold. The problem is that [free_evar_subst'] does not wrap the target
          in nest_mu. *)


Lemma svar_quantify_emplace {Σ : Signature} X n C ϕ:
  svar_quantify X n (emplace C ϕ) = emplace (svar_quantify_ctx X n C) (svar_quantify X n ϕ).
Proof.
  destruct C.
  unfold svar_quantify_ctx,emplace. simpl.
Abort.

Lemma evar_quantify_subst_ctx {Σ : Signature} x n AC ϕ:
  x ∉ AC_free_evars AC ->
  evar_quantify x n (subst_ctx AC ϕ) = subst_ctx AC (evar_quantify x n ϕ).
Proof.
  intros Hx.
  induction AC.
  - reflexivity.
  - simpl. simpl in Hx.
    rewrite IHAC.
    { set_solver. }
    rewrite [evar_quantify x n p]evar_quantify_fresh.
    unfold evar_is_fresh_in. set_solver.
    reflexivity.
  - simpl. simpl in Hx.
    rewrite IHAC.
    { set_solver. }
    rewrite [evar_quantify x n p]evar_quantify_fresh.
    unfold evar_is_fresh_in. set_solver.
    reflexivity.
Qed.

Lemma bevar_subst_evar_quantify_free_evar {Σ : Signature} x dbi ϕ:
  well_formed_closed_ex_aux ϕ dbi ->
  bevar_subst (evar_quantify x dbi ϕ) (patt_free_evar x) dbi  = ϕ.
Proof.
  move: dbi.
  induction ϕ; intros dbi Hwf; simpl in *; auto.
  - case_match; simpl;[|reflexivity].
    case_match; simpl; try lia. subst. auto.
  - do 2 case_match; try lia; auto. congruence. congruence.
  - apply andb_true_iff in Hwf.
    destruct_and!.
    rewrite IHϕ1;[assumption|].
    rewrite IHϕ2;[assumption|].
    reflexivity.
  - apply andb_true_iff in Hwf.
    destruct_and!.
    rewrite IHϕ1;[assumption|].
    rewrite IHϕ2;[assumption|].
    reflexivity.
  - rewrite IHϕ;[assumption|reflexivity].
  - rewrite IHϕ;[assumption|reflexivity].
Qed.

Lemma bsvar_subst_svar_quantify_free_svar {Σ : Signature} X dbi ϕ:
  well_formed_closed_mu_aux ϕ dbi ->
  bsvar_subst (svar_quantify X dbi ϕ) (patt_free_svar X) dbi  = ϕ.
Proof.
  move: dbi.
  induction ϕ; intros dbi Hwf; simpl in *; auto.
  - case_match; simpl;[|reflexivity].
    case_match; simpl; try lia. subst. auto.
  - do 2 case_match; try lia; auto. congruence. congruence.
  - apply andb_true_iff in Hwf.
    destruct_and!.
    rewrite IHϕ1;[assumption|].
    rewrite IHϕ2;[assumption|].
    reflexivity.
  - apply andb_true_iff in Hwf.
    destruct_and!.
    rewrite IHϕ1;[assumption|].
    rewrite IHϕ2;[assumption|].
    reflexivity.
  - rewrite IHϕ;[assumption|reflexivity].
  - rewrite IHϕ;[assumption|reflexivity].
Qed.

Lemma free_evars_subst_ctx {Σ : Signature} AC ϕ:
  free_evars (subst_ctx AC ϕ) = AC_free_evars AC ∪ free_evars ϕ.
Proof.
  induction AC; simpl.
  - set_solver.
  - rewrite IHAC. clear. set_solver.
  - rewrite IHAC. clear. set_solver.
Qed.

Lemma free_svar_subst_fresh {Σ : Signature} phi psi X:
  svar_is_fresh_in X phi ->
  free_svar_subst phi psi X = phi.
Proof.
  intros Hfresh.
  unfold svar_is_fresh_in in Hfresh.
  induction phi; simpl in *; auto.
  - case_match.
    + subst. set_solver.
    + reflexivity.
  - specialize (IHphi1 ltac:(set_solver)).
    specialize (IHphi2 ltac:(set_solver)).
    rewrite IHphi1. rewrite IHphi2.
    reflexivity.
  - specialize (IHphi1 ltac:(set_solver)).
    specialize (IHphi2 ltac:(set_solver)).
    rewrite IHphi1. rewrite IHphi2.
    reflexivity.
  - specialize (IHphi ltac:(assumption)).
    rewrite IHphi.
    reflexivity.
  - specialize (IHphi ltac:(assumption)).
    rewrite IHphi.
    reflexivity.
Qed.

Lemma Private_no_negative_occurrence_svar_quantify {Σ : Signature} ϕ level X:
  (
    no_negative_occurrence_db_b level ϕ = true ->
    svar_has_negative_occurrence X ϕ = false ->
    no_negative_occurrence_db_b level (svar_quantify X level ϕ) = true
  )
  /\
  (
    no_positive_occurrence_db_b level ϕ = true ->
    svar_has_positive_occurrence X ϕ = false ->
    no_positive_occurrence_db_b level (svar_quantify X level ϕ) = true
  ).
Proof.
  move: level.
  induction ϕ; intros level; split; intros HnoX Hnolevel; cbn in *; auto.
  - case_match; reflexivity.
  - case_match; cbn. 2: reflexivity. congruence.
  - apply orb_false_iff in Hnolevel. destruct_and!.
    pose proof (IH1 := IHϕ1 level).
    destruct IH1 as [IH11 _].
    specialize (IH11 ltac:(assumption) ltac:(assumption)).
    pose proof (IH2 := IHϕ2 level).
    destruct IH2 as [IH21 _].
    specialize (IH21 ltac:(assumption) ltac:(assumption)).
    split_and!; assumption.
  - apply orb_false_iff in Hnolevel. destruct_and!.
    pose proof (IH1 := IHϕ1 level).
    destruct IH1 as [_ IH12].
    specialize (IH12 ltac:(assumption) ltac:(assumption)).
    pose proof (IH2 := IHϕ2 level).
    destruct IH2 as [_ IH22].
    specialize (IH22 ltac:(assumption) ltac:(assumption)).
    split_and!; assumption.
  - apply orb_false_iff in Hnolevel. destruct_and!.
    pose proof (IH1 := IHϕ1 level).
    destruct IH1 as [_ IH12].
    specialize (IH12 ltac:(assumption) ltac:(assumption)).
    pose proof (IH2 := IHϕ2 level).
    destruct IH2 as [IH21 _].
    specialize (IH21 ltac:(assumption) ltac:(assumption)).
    split_and!; assumption.
  - apply orb_false_iff in Hnolevel. destruct_and!.
    pose proof (IH1 := IHϕ1 level).
    destruct IH1 as [IH11 _].
    specialize (IH11 ltac:(assumption) ltac:(assumption)).
    pose proof (IH2 := IHϕ2 level).
    destruct IH2 as [_ IH22].
    specialize (IH22 ltac:(assumption) ltac:(assumption)).
    split_and!; assumption.
  - firstorder.
  - firstorder.
  - firstorder.
  - firstorder.
Qed.

Lemma no_negative_occurrence_svar_quantify {Σ : Signature} ϕ level X:
  no_negative_occurrence_db_b level ϕ = true ->
  svar_has_negative_occurrence X ϕ = false ->
  no_negative_occurrence_db_b level (svar_quantify X level ϕ) = true.
Proof.
  intros H1 H2.
  pose proof (Htmp :=Private_no_negative_occurrence_svar_quantify ϕ level X).
  destruct Htmp as [Htmp1 Htmp2].
  auto.
Qed.

Lemma no_positive_occurrence_svar_quantify {Σ : Signature} ϕ level X:
    no_positive_occurrence_db_b level ϕ = true ->
    svar_has_positive_occurrence X ϕ = false ->
    no_positive_occurrence_db_b level (svar_quantify X level ϕ) = true.
Proof.
  intros H1 H2.
  pose proof (Htmp :=Private_no_negative_occurrence_svar_quantify ϕ level X).
  destruct Htmp as [Htmp1 Htmp2].
  auto.
Qed.

#[export]
 Hint Resolve no_positive_occurrence_svar_quantify : core.

#[export]
 Hint Resolve no_negative_occurrence_svar_quantify : core.

#[export]
 Hint Resolve wfc_impl_no_neg_occ : core.


Lemma no_negative_occurrence_svar_quantify_2 {Σ : Signature} X dbi1 dbi2 ϕ:
  dbi1 <> dbi2 ->
  no_negative_occurrence_db_b dbi1 (svar_quantify X dbi2 ϕ) = no_negative_occurrence_db_b dbi1 ϕ
with no_positive_occurrence_svar_quantify_2  {Σ : Signature} X dbi1 dbi2 ϕ:
  dbi1 <> dbi2 ->
  no_positive_occurrence_db_b dbi1 (svar_quantify X dbi2 ϕ) = no_positive_occurrence_db_b dbi1 ϕ.
Proof.
  - move: dbi1 dbi2.
    induction ϕ; intros dbi1 dbi2 Hdbi; simpl; auto.
    + case_match; reflexivity.
    + cbn. rewrite IHϕ1. lia. rewrite IHϕ2. lia. reflexivity.
    + unfold no_negative_occurrence_db_b at 1.
      fold (no_positive_occurrence_db_b dbi1 (svar_quantify X dbi2 ϕ1)).
      fold (no_negative_occurrence_db_b dbi1 (svar_quantify X dbi2 ϕ2)).
      rewrite no_positive_occurrence_svar_quantify_2. lia. rewrite IHϕ2. lia. reflexivity.
    + cbn. rewrite IHϕ. lia. reflexivity.
    + cbn. rewrite IHϕ. lia. reflexivity.
  - move: dbi1 dbi2.
    induction ϕ; intros dbi1 dbi2 Hdbi; simpl; auto.
    + case_match; cbn. 2: reflexivity. case_match; congruence.
    + cbn. rewrite IHϕ1. lia. rewrite IHϕ2. lia. reflexivity.
    + unfold no_positive_occurrence_db_b at 1.
      fold (no_negative_occurrence_db_b dbi1 (svar_quantify X dbi2 ϕ1)).
      fold (no_positive_occurrence_db_b dbi1 (svar_quantify X dbi2 ϕ2)).
      rewrite no_negative_occurrence_svar_quantify_2. lia. rewrite IHϕ2. lia. reflexivity.
    + cbn. rewrite IHϕ. lia. reflexivity.
    + cbn. rewrite IHϕ. lia. reflexivity.
Qed.

Lemma well_formed_positive_svar_quantify {Σ : Signature} X dbi ϕ:
  well_formed_positive ϕ ->
  well_formed_positive (svar_quantify X dbi ϕ) = true.
Proof.
  intros Hϕ.
  move: dbi.
  induction ϕ; intros dbi; simpl; auto.
  - case_match; reflexivity.
  - simpl in Hϕ.
    destruct_and!.
    specialize (IHϕ1 ltac:(assumption)).
    specialize (IHϕ2 ltac:(assumption)).
    rewrite IHϕ1. rewrite IHϕ2.
    reflexivity.
  - simpl in Hϕ.
    destruct_and!.
    specialize (IHϕ1 ltac:(assumption)).
    specialize (IHϕ2 ltac:(assumption)).
    rewrite IHϕ1. rewrite IHϕ2.
    reflexivity.
  - simpl in Hϕ.
    destruct_and!.
    specialize (IHϕ ltac:(assumption)).
    rewrite IHϕ.
    rewrite no_negative_occurrence_svar_quantify_2. lia.
    split_and!; auto.
Qed.

#[export]
 Hint Resolve well_formed_positive_svar_quantify : core.

(* Lemma bevar_occur_positivity {Σ : Signature} ψ dbi :
  bsvar_occur ψ dbi = false ->
  no_negative_occurrence_db_b dbi ψ = true /\ no_positive_occurrence_db_b dbi ψ.
Proof.
  induction ψ; intros H; cbn; auto.
  * simpl in H. case_match; auto.
  * Search bsvar_occur. *)

Lemma nno_free_svar_subst {Σ : Signature} dbi ϕ ψ X:
  well_formed_closed_mu_aux ψ dbi ->
  no_negative_occurrence_db_b dbi (free_svar_subst ϕ ψ X)
  = no_negative_occurrence_db_b dbi ϕ
with npo_free_svar_subst {Σ : Signature} dbi ϕ ψ X:
  well_formed_closed_mu_aux ψ dbi ->
  no_positive_occurrence_db_b dbi (free_svar_subst ϕ ψ X)
  = no_positive_occurrence_db_b dbi ϕ.
Proof.
  - move: dbi.
    induction ϕ; intros dbi Hwf; simpl; auto.
    + case_match; cbn; [|reflexivity].
      eapply Private_wfc_impl_no_neg_pos_occ. exact Hwf. lia.
    + cbn. rewrite IHϕ1; auto. rewrite IHϕ2; auto.
    + cbn.
      fold (no_positive_occurrence_db_b).
      rewrite nno_free_svar_subst; auto.
      rewrite npo_free_svar_subst; auto.
    + cbn.
      rewrite IHϕ; auto.
    + cbn.
      rewrite IHϕ; auto. eapply well_formed_closed_mu_aux_ind. 2: exact Hwf. lia.
  - move: dbi.
    induction ϕ; intros dbi Hwf; simpl; auto.
    + case_match; cbn; [|reflexivity].
      eapply Private_wfc_impl_no_neg_pos_occ. exact Hwf. lia.
    + cbn. rewrite IHϕ1; auto. rewrite IHϕ2; auto.
    + cbn.
      fold (no_negative_occurrence_db_b).
      rewrite nno_free_svar_subst; auto.
      rewrite IHϕ2; auto.
    + cbn.
      rewrite IHϕ; auto.
    + cbn.
      rewrite IHϕ; auto. eapply well_formed_closed_mu_aux_ind. 2: exact Hwf. lia.
Qed.

Lemma wfp_free_svar_subst_1 {Σ : Signature} ϕ ψ X:
  well_formed_closed ψ = true ->
  well_formed_positive ψ = true ->
  well_formed_positive ϕ = true ->
  well_formed_positive (free_svar_subst ϕ ψ X) = true.
Proof.
  intros wfcψ wfpψ wfpϕ.
  induction ϕ; simpl; auto.
  - case_match; auto.
  - simpl in wfpϕ. destruct_and!.
    rewrite -> IHϕ1 by assumption.
    rewrite -> IHϕ2 by assumption.
    reflexivity.
  - simpl in wfpϕ. destruct_and!.
    rewrite -> IHϕ1 by assumption.
    rewrite -> IHϕ2 by assumption.
    reflexivity.
  - simpl in wfpϕ. destruct_and!.
    specialize (IHϕ H0).
    rewrite -> IHϕ.
    rewrite nno_free_svar_subst.
    { apply andb_true_iff in wfcψ. apply wfcψ. }
    rewrite H.
    reflexivity.
Qed.

Lemma wfp_free_svar_subst {Σ : Signature} ϕ ψ X:
  well_formed_closed_mu_aux ψ 0 ->
  well_formed_positive ψ = true ->
  well_formed_positive ϕ = true ->
  svar_has_negative_occurrence X ϕ = false ->
  well_formed_positive (free_svar_subst ϕ ψ X) = true
with wfp_neg_free_svar_subst {Σ : Signature} ϕ ψ X:
  well_formed_closed_mu_aux ψ 0 ->
  well_formed_positive ψ = true ->
  well_formed_positive ϕ = true ->
  svar_has_positive_occurrence X ϕ = false ->
  well_formed_positive (free_svar_subst ϕ ψ X) = true.
Proof.
  - intros Hwfcψ Hwfpψ Hwfpϕ Hnoneg.
    induction ϕ; simpl; auto.
    + case_match; [|reflexivity].
      assumption.
    + cbn in Hnoneg. cbn in Hwfpϕ.
      apply orb_false_iff in Hnoneg.
      destruct_and!.
      specialize (IHϕ1 ltac:(assumption) ltac:(assumption)).
      specialize (IHϕ2 ltac:(assumption) ltac:(assumption)).
      split_and!; auto.
    + cbn in Hnoneg. cbn in Hwfpϕ.
      apply orb_false_iff in Hnoneg.
      destruct_and!.
      pose proof (IH1 := wfp_neg_free_svar_subst Σ ϕ1 ψ X ltac:(assumption)).
      feed specialize IH1.
      { assumption. }
      { assumption. }
      { assumption. }
      specialize (IHϕ2 ltac:(assumption)).
      split_and!; auto.
    + cbn in Hnoneg. cbn in Hwfpϕ. destruct_and!.
      rewrite IHϕ. assumption. assumption. split_and!; auto.
      rewrite nno_free_svar_subst.
      assumption. assumption.
  -
    intros Hwfcψ Hwfpψ Hwfpϕ Hnoneg.
    induction ϕ; simpl; auto.
    + case_match; [|reflexivity].
      assumption.
    + cbn in Hnoneg. cbn in Hwfpϕ.
      apply orb_false_iff in Hnoneg.
      destruct_and!.
      specialize (IHϕ1 ltac:(assumption) ltac:(assumption)).
      specialize (IHϕ2 ltac:(assumption) ltac:(assumption)).
      split_and!; auto.
    + cbn in Hnoneg. cbn in Hwfpϕ.
      apply orb_false_iff in Hnoneg.
      destruct_and!.
      pose proof (IH1 := wfp_free_svar_subst Σ ϕ1 ψ X ltac:(assumption)).
      feed specialize IH1.
      { assumption. }
      { assumption. }
      { assumption. }
      specialize (IHϕ2 ltac:(assumption)).
      split_and!; auto.
    + cbn in Hnoneg. cbn in Hwfpϕ. destruct_and!.
      rewrite IHϕ. assumption. assumption. split_and!; auto.
      rewrite nno_free_svar_subst.
      assumption. assumption.
Qed.

#[export]
 Hint Resolve wfp_free_svar_subst : core.

#[export]
 Hint Resolve wfp_neg_free_svar_subst : core.

Lemma wfc_mu_free_svar_subst {Σ : Signature} level ϕ ψ X:
  well_formed_closed_mu_aux ϕ level ->
  well_formed_closed_mu_aux ψ level ->
  well_formed_closed_mu_aux (free_svar_subst ϕ ψ X) level = true.
Proof.
  intros Hϕ Hψ.
  move: level Hϕ Hψ.
  induction ϕ; intros level Hϕ Hψ; simpl in *; auto.
  - case_match; [|reflexivity].
    assumption.
  - destruct_and!.
    rewrite IHϕ1; auto.
    rewrite IHϕ2; auto.
  - destruct_and!.
    rewrite IHϕ1; auto.
    rewrite IHϕ2; auto.
  - rewrite IHϕ; auto. eapply well_formed_closed_mu_aux_ind. 2: exact Hψ. lia.
Qed.

#[export]
 Hint Resolve wfc_mu_free_svar_subst : core.

Lemma wfc_ex_free_svar_subst {Σ : Signature} level ϕ ψ X:
  well_formed_closed_ex_aux ϕ level ->
  well_formed_closed_ex_aux ψ level ->
  well_formed_closed_ex_aux (free_svar_subst ϕ ψ X) level = true.
Proof.
  intros Hϕ Hψ.
  move: level Hϕ Hψ.
  induction ϕ; intros level Hϕ Hψ; simpl in *; auto.
  - case_match; [|reflexivity].
    assumption.
  - destruct_and!.
    rewrite IHϕ1; auto.
    rewrite IHϕ2; auto.
  - destruct_and!.
    rewrite IHϕ1; auto.
    rewrite IHϕ2; auto.
  - rewrite IHϕ; auto. eapply well_formed_closed_ex_aux_ind. 2: exact Hψ. lia.
Qed.

#[export]
 Hint Resolve wfc_mu_free_svar_subst : core.

Lemma wfc_ex_free_evar_subst_2 {Σ : Signature} level ϕ ψ X:
  well_formed_closed_ex_aux ϕ level ->
  well_formed_closed_ex_aux ψ level ->
  well_formed_closed_ex_aux (free_evar_subst ϕ ψ X) level = true.
Proof.
  intros Hϕ Hψ.
  move: level Hϕ Hψ.
  induction ϕ; intros level Hϕ Hψ; simpl in *; auto.
  - case_match; [|reflexivity].
    repeat case_match; auto.
  - destruct_and!.
    rewrite IHϕ1; auto.
    rewrite IHϕ2; auto.
  - destruct_and!.
    rewrite IHϕ1; auto.
    rewrite IHϕ2; auto.
  - rewrite IHϕ; auto. eapply well_formed_closed_ex_aux_ind. 2: exact Hψ. lia.
Qed.

#[export]
 Hint Resolve wfc_ex_free_evar_subst_2 : core.

#[export]
 Hint Resolve svar_quantify_closed_ex : core.

#[export]
 Hint Resolve svar_quantify_closed_mu : core.
    
#[export]
 Hint Resolve evar_quantify_positive : core.

#[export]
 Hint Resolve evar_quantify_closed_mu : core.

#[export]
 Hint Resolve evar_quantify_closed_ex : core.

Lemma count_evar_occurrences_bevar_subst {Σ : Signature} pcEvar ϕ ψ k:
  count_evar_occurrences pcEvar ψ = 0 ->
  count_evar_occurrences pcEvar (bevar_subst ϕ ψ k) = count_evar_occurrences pcEvar ϕ.
Proof.
  intros H.
  move: k.
  induction ϕ; intros k; simpl; auto.
  - case_match; auto.
Qed.

Lemma count_evar_occurrences_evar_open {Σ : Signature} pcEvar ϕ x:
  pcEvar <> x ->
  count_evar_occurrences pcEvar (evar_open 0 x ϕ) = count_evar_occurrences pcEvar ϕ.
Proof.
  intros H. apply count_evar_occurrences_bevar_subst. simpl. case_match; congruence.
Qed.


      
#[export]
 Hint Resolve wfp_evar_open : core.

#[export]
 Hint Resolve wfc_mu_aux_body_ex_imp1 : core.

#[export]
 Hint Resolve wfc_ex_aux_body_ex_imp1 : core.


Lemma evar_open_size' {Σ : Signature} :
  forall (k : db_index) (n : evar) (p : Pattern),
    size' (evar_open k n p) = size' p.
Proof.
  intros k n p. generalize dependent k.
  induction p; intros k; cbn; try reflexivity.
  break_match_goal; reflexivity.
  rewrite (IHp1 k); rewrite (IHp2 k); reflexivity.
  rewrite (IHp1 k); rewrite (IHp2 k); reflexivity.
  rewrite (IHp (S k)); reflexivity.
  rewrite (IHp k); reflexivity.
Qed.

Lemma svar_open_size' {Σ : Signature} :
  forall (k : db_index) (n : svar) (p : Pattern),
    size' (svar_open k n p) = size' p.
Proof.
  intros k n p. generalize dependent k.
  induction p; intros k; cbn; try reflexivity.
  break_match_goal; reflexivity.
  rewrite (IHp1 k); rewrite (IHp2 k); reflexivity.
  rewrite (IHp1 k); rewrite (IHp2 k); reflexivity.
  rewrite (IHp k); reflexivity.
  rewrite (IHp (S k)); reflexivity.
Qed.

(* TODO: deprecated

Lemma well_formed_positive_nest_ex_aux {Σ : Signature} level more ϕ:
  well_formed_positive (nest_ex_aux level more ϕ) = well_formed_positive ϕ.
Proof.
  move: level.
  induction ϕ; intros level; simpl; auto.
  - rewrite IHϕ1. rewrite IHϕ2. auto.
  - rewrite IHϕ1. rewrite IHϕ2. auto.
  - rewrite IHϕ. rewrite nno_nest_ex_aux. reflexivity.
Qed.
 *)

(* TODO remove the no-negative-ocurrence assumption from the svar version *)
Lemma wfp_free_evar_subst {Σ : Signature} ϕ ψ x:
  well_formed_closed_mu_aux ψ 0 ->
  well_formed_positive ψ = true ->
  well_formed_positive ϕ = true ->
  well_formed_positive (free_evar_subst ϕ ψ x) = true
with wfp_neg_free_evar_subst {Σ : Signature} ϕ ψ x:
  well_formed_closed_mu_aux ψ 0 ->
  well_formed_positive ψ = true ->
  well_formed_positive ϕ = true ->
  well_formed_positive (free_evar_subst ϕ ψ x) = true.
Proof.
  -
    intros Hwfcψ Hwfpψ Hwfpϕ. (* Hnoneg.*)
    induction ϕ; simpl; auto.
    + case_match; [|reflexivity].
      assumption.
    + cbn in Hwfpϕ.
      destruct_and!.
      specialize (IHϕ1 ltac:(assumption)).
      specialize (IHϕ2 ltac:(assumption)).
      split_and!; auto.
    + cbn in Hwfpϕ.
      destruct_and!.
      pose proof (IH1 := wfp_neg_free_evar_subst Σ ϕ1 ψ x ltac:(assumption)).
      feed specialize IH1.
      { assumption. }
      { assumption. }
      specialize (IHϕ2 ltac:(assumption)).
      split_and!; auto.
    + cbn in Hwfpϕ. destruct_and!.
      rewrite IHϕ. assumption. split_and!; auto.
      rewrite free_evar_subst_preserves_no_negative_occurrence; auto.
  -
    intros Hwfcψ Hwfpψ Hwfpϕ.
    induction ϕ; simpl; auto.
    + case_match; [|reflexivity].
      assumption.
    + cbn in Hwfpϕ.
      destruct_and!.
      specialize (IHϕ1 ltac:(assumption)).
      specialize (IHϕ2 ltac:(assumption)).
      split_and!; auto.
    + cbn in Hwfpϕ.
      destruct_and!.
      pose proof (IH1 := wfp_free_evar_subst Σ ϕ1 ψ x ltac:(assumption)).
      feed specialize IH1.
      { assumption. }
      { assumption. }
      specialize (IHϕ2 ltac:(assumption)).
      split_and!; auto.
    + cbn in Hwfpϕ. destruct_and!.
      rewrite IHϕ. assumption. split_and!; auto.
      rewrite free_evar_subst_preserves_no_negative_occurrence; auto.
Qed.

#[export]
 Hint Resolve wfp_free_evar_subst : core.

Lemma no_neg_occ_db_bevar_subst {Σ : Signature} phi psi dbi1 dbi2:
  well_formed_closed_mu_aux psi 0 = true ->
  no_negative_occurrence_db_b dbi1 phi = true ->
  no_negative_occurrence_db_b dbi1 (bevar_subst phi psi dbi2) = true
with no_pos_occ_db_bevar_subst {Σ : Signature} phi psi dbi1 dbi2:
       well_formed_closed_mu_aux psi 0 = true ->
       no_positive_occurrence_db_b dbi1 phi = true ->
       no_positive_occurrence_db_b dbi1 (bevar_subst phi psi dbi2) = true.
Proof.
  - move: dbi1 dbi2.
    induction phi; intros dbi1 dbi2 Hwfcpsi Hnonegphi; cbn in *; auto.
    + case_match; auto.
    + destruct_and!.
      rewrite -> IHphi1, -> IHphi2; auto.
    + destruct_and!.
      fold (no_positive_occurrence_db_b dbi1 (bevar_subst phi1 psi dbi2)).
      rewrite no_pos_occ_db_bevar_subst; auto.
      rewrite -> IHphi2; auto.
  - move: dbi1 dbi2.
    induction phi; intros dbi1 dbi2 Hwfcpsi Hnonegphi; cbn in *; auto.
    + repeat case_match; auto.
      apply wfc_impl_no_pos_occ. assumption.
    + destruct_and!.
      rewrite -> IHphi1, -> IHphi2; auto.
    + destruct_and!.
      fold (no_negative_occurrence_db_b dbi1 (bevar_subst phi1 psi dbi2)).
      rewrite no_neg_occ_db_bevar_subst; auto.
      rewrite -> IHphi2; auto.
Qed.

Lemma bevar_subst_positive_2 {Σ : Signature} :
  forall φ ψ n,
    well_formed_closed_mu_aux ψ 0 = true ->
    well_formed_positive φ = true ->
    well_formed_positive ψ = true ->
    well_formed_positive (bevar_subst φ ψ n) = true.
Proof.
  induction φ; intros ψ n' H0 H1 H2; cbn in *; auto.
  * break_match_goal; auto.
  * destruct_and!. rewrite -> IHφ1, -> IHφ2; auto.
  * destruct_and!. rewrite -> IHφ1, -> IHφ2; auto.
  * destruct_and!.
    rewrite IHφ; auto.
    rewrite no_neg_occ_db_bevar_subst; auto.
Qed.

#[export]
Hint Resolve bevar_subst_positive_2 : core.

#[export]
Hint Resolve wfc_mu_aux_bevar_subst : core.

#[export]
Hint Resolve wfc_ex_aux_bevar_subst : core.

Lemma count_evar_occurrences_svar_open {Σ : Signature} x dbi ϕ ψ:
  count_evar_occurrences x ψ = 0 ->
  count_evar_occurrences x (bsvar_subst ϕ ψ dbi) = count_evar_occurrences x ϕ.
Proof.
  move: dbi.
  induction ϕ; intros dbi H; simpl; auto.
  case_match; auto.
Qed.

#[export]
Hint Resolve wfp_svar_open : core.

Lemma free_evar_subst_bsvar_subst {Σ : Signature} ϕ ψ ξ x dbi:
  well_formed_closed_mu_aux ξ 0 ->
  evar_is_fresh_in x ψ ->
  free_evar_subst (bsvar_subst ϕ ψ dbi) ξ x
  = bsvar_subst (free_evar_subst ϕ ξ x) ψ dbi.
Proof.
  move: dbi.
  induction ϕ; intros dbi H1 H2; simpl; auto.
  - repeat case_match; auto.
    erewrite well_formed_bsvar_subst. reflexivity.
    2: eassumption.
    lia.
  - repeat case_match; auto.
    apply free_evar_subst_no_occurrence.
    apply count_evar_occurrences_0. assumption.
  - rewrite IHϕ1; auto. rewrite IHϕ2; auto.
  - rewrite IHϕ1; auto. rewrite IHϕ2; auto.
  - rewrite IHϕ; auto.
  - rewrite IHϕ; auto.
Qed.

Lemma svar_hno_bsvar_subst {Σ : Signature} X ϕ ψ dbi:
  (svar_has_negative_occurrence X ψ = true -> no_positive_occurrence_db_b dbi ϕ = true) ->
  (svar_has_positive_occurrence X ψ = true -> no_negative_occurrence_db_b dbi ϕ = true) ->
  svar_has_negative_occurrence X ϕ = false ->
  svar_has_negative_occurrence X (bsvar_subst ϕ ψ dbi) = false
with svar_hpo_bsvar_subst {Σ : Signature} X ϕ ψ dbi:
       (svar_has_negative_occurrence X ψ = true -> no_negative_occurrence_db_b dbi ϕ = true) ->
       (svar_has_positive_occurrence X ψ = true -> no_positive_occurrence_db_b dbi ϕ = true) ->
       svar_has_positive_occurrence X ϕ = false ->
       svar_has_positive_occurrence X (bsvar_subst ϕ ψ dbi) = false.
Proof.
  -
    move: dbi.
    induction ϕ; intros dbi H1 H2 H3; cbn in *; auto.
    + case_match; auto. case_match; try lia.
      destruct (decide (svar_has_negative_occurrence X ψ = false)); auto.
      apply not_false_is_true in n0. specialize (H1 n0). congruence. case_match; auto. congruence.
    + apply orb_false_iff in H3.
      destruct_and!.
      rewrite IHϕ1; auto.
      { naive_bsolver. }
      { naive_bsolver. }
      rewrite IHϕ2; auto.
      { naive_bsolver. }
      { naive_bsolver. }
    + fold svar_has_positive_occurrence in *.
      fold no_positive_occurrence_db_b in *.
      fold no_negative_occurrence_db_b in *.
      apply orb_false_iff in H3.
      destruct_and!.
      rewrite svar_hpo_bsvar_subst; auto.
      { naive_bsolver. }
      { naive_bsolver. }
      rewrite IHϕ2; auto.
      { naive_bsolver. }
      { naive_bsolver. }
  -
    move: dbi.
    induction ϕ; intros dbi H1 H2 H3; cbn in *; auto.
    + case_match; auto. case_match; try lia.
      destruct (decide (svar_has_positive_occurrence X ψ = false)); auto.
      apply not_false_is_true in n0. specialize (H2 n0). congruence. case_match; auto. congruence.
    + apply orb_false_iff in H3.
      destruct_and!.
      rewrite IHϕ1; auto.
      { naive_bsolver. }
      { naive_bsolver. }
      rewrite IHϕ2; auto.
      { naive_bsolver. }
      { naive_bsolver. }
    + fold svar_has_positive_occurrence in *.
      fold svar_has_negative_occurrence in *.
      fold no_positive_occurrence_db_b in *.
      fold no_negative_occurrence_db_b in *.
      apply orb_false_iff in H3.
      destruct_and!.
      rewrite svar_hno_bsvar_subst; auto.
      { naive_bsolver. }
      { naive_bsolver. }
      rewrite IHϕ2; auto.
      { naive_bsolver. }
      { naive_bsolver. }
Qed.

Lemma svar_hno_false_if_fresh {Σ : Signature} X ϕ:
  svar_is_fresh_in X ϕ ->
  svar_has_negative_occurrence X ϕ = false
with svar_hpo_false_if_fresh {Σ : Signature} X ϕ:
       svar_is_fresh_in X ϕ ->
       svar_has_positive_occurrence X ϕ = false.
Proof.
  - unfold svar_is_fresh_in.
    induction ϕ; intros H; cbn in *; auto.
    + rewrite -> IHϕ1, -> IHϕ2; try reflexivity; set_solver.
    + fold svar_has_positive_occurrence.
      rewrite -> svar_hpo_false_if_fresh, -> IHϕ2; try reflexivity.
      * set_solver.
      * unfold svar_is_fresh_in. set_solver.
  - unfold svar_is_fresh_in.
    induction ϕ; intros H; cbn in *; auto.
    + case_match; auto. set_solver.
    + rewrite -> IHϕ1, -> IHϕ2; try reflexivity; set_solver.
    + fold svar_has_negative_occurrence.
      rewrite -> svar_hno_false_if_fresh, -> IHϕ2; try reflexivity.
      * set_solver.
      * unfold svar_is_fresh_in. set_solver.
Qed.

Lemma wfc_mu_free_evar_subst {Σ : Signature} level ϕ ψ x:
  well_formed_closed_mu_aux ϕ level ->
  well_formed_closed_mu_aux ψ level ->
  well_formed_closed_mu_aux (free_evar_subst ϕ ψ x) level = true.
Proof.
  intros Hϕ Hψ.
  move: level Hϕ Hψ.
  induction ϕ; intros level Hϕ Hψ; simpl in *; auto.
  - case_match; [|reflexivity].
    assumption.
  - destruct_and!.
    rewrite IHϕ1; auto.
    rewrite IHϕ2; auto.
  - destruct_and!.
    rewrite IHϕ1; auto.
    rewrite IHϕ2; auto.
  - apply IHϕ; auto.
    eapply well_formed_closed_mu_aux_ind.
    2: eassumption. lia.
Qed.


Lemma well_formed_app_proj1 {Σ : Signature} p q:
  well_formed (patt_app p q) ->
  well_formed p.
Proof.
  intros H.
  unfold well_formed,well_formed_closed in *. simpl in *.
  destruct_and!.
  unfold well_formed,well_formed_closed. split_and!; assumption.
Qed.

Lemma well_formed_app_proj2 {Σ : Signature} p q:
  well_formed (patt_app p q) ->
  well_formed q.
Proof.
  intros H.
  unfold well_formed,well_formed_closed in *. simpl in *.
  destruct_and!.
  unfold well_formed,well_formed_closed. split_and!; assumption.
Qed.

Lemma well_formed_imp_proj1 {Σ : Signature} p q:
  well_formed (patt_imp p q) ->
  well_formed p.
Proof.
  intros H.
  unfold well_formed,well_formed_closed in *. simpl in *.
  destruct_and!.
  unfold well_formed,well_formed_closed. split_and!; assumption.
Qed.

Lemma well_formed_imp_proj2 {Σ : Signature} p q:
  well_formed (patt_imp p q) ->
  well_formed q.
Proof.
  intros H.
  unfold well_formed,well_formed_closed in *. simpl in *.
  destruct_and!.
  unfold well_formed,well_formed_closed. split_and!; assumption.
Qed.


Tactic Notation "wf_auto" int_or_var(n)
  := auto n; unfold well_formed, well_formed_closed in *; destruct_and?; simpl in *; split_and?; auto n.
Tactic Notation "wf_auto" := wf_auto 5.

Import Notations.

  Lemma wf_evar_open_from_wf_ex {Σ : Signature} x ϕ:
    well_formed (patt_exists ϕ) ->
    well_formed (evar_open 0 x ϕ).
  Proof.
    intros H. wf_auto.
  Qed.

  Lemma wf_svar_open_from_wf_mu {Σ : Signature} X ϕ:
    well_formed (patt_mu ϕ) ->
    well_formed (svar_open 0 X ϕ).
  Proof.
    intros H. wf_auto;
    destruct_and!;
        [ (apply wfp_svar_open; auto)
        | (apply wfc_mu_aux_body_mu_imp1; assumption)
        | (apply wfc_ex_aux_body_mu_imp1; assumption)
        ].
  Qed.

  Ltac wf_auto2 := unfold is_true in *;
      repeat (try assumption; try (solve [wf_auto]);
      match goal with
      | [ |- ?H -> ?G ]
        => intro

      | [ |- size' (evar_open _ _ _) < _ ]
        => rewrite evar_open_size'

      | [ |- size' (svar_open _ _ _) < _ ]
        => rewrite svar_open_size'

      | [ |- size' _ < size' (patt_app _ _) ]
        => simpl; lia

      | [ |- size' _ < size' (patt_imp _ _) ]
        => simpl; lia

      | [ |- size' _ < size' (patt_exists _) ]
        => simpl; lia

      | [ |- well_formed (patt_imp ?p ?q) = true]
        => apply well_formed_imp

      | [ |- well_formed (patt_app ?p ?q) = true]
        => apply well_formed_app

      | [ H : well_formed (patt_app ?p ?q) = true |- _]
        => assert (well_formed p = true);
          [eapply well_formed_app_proj1; eassumption|];
          assert ( well_formed q = true);
          [eapply well_formed_app_proj2; eassumption|];
          clear H

      | [ H : well_formed (patt_imp ?p ?q) = true |- _]
        => assert (well_formed p = true);
          [eapply well_formed_imp_proj1; eassumption|];
          assert ( well_formed q = true);
          [eapply well_formed_imp_proj2; eassumption|];
          clear H

      | [ |- well_formed (free_evar_subst ?phi ?p ?E) = true ]
        => apply well_formed_free_evar_subst

      | [ |- ?x ∉ ?E ]
        => progress simpl

      | [ |- ?x ∉ free_evars (free_evar_subst _ _ _) ]
        => eapply not_elem_of_larger_impl_not_elem_of;
           [apply free_evars_free_evar_subst|]

      | [frx: ?x ∉ _ |- ?x <> ?E ]
        => clear -frx; set_solver

      | [frx: ?x ∉ _ |- ?x ∉ ?E ]
        => clear -frx; set_solver

      | [ |- well_formed (evar_open _ _ _) = true]
        => apply wf_evar_open_from_wf_ex

        (* fallback *)
      | [ |- well_formed _ = true]
        => unfold well_formed, well_formed_closed in *; simpl in *;
           destruct_and?; split_and?

      | [ |- well_formed_positive (free_evar_subst _ _ _) = true ]
        => apply wfp_free_evar_subst

      | [H: well_formed_positive (patt_exists _) = true |- _]
        => simpl in H

      | [H: well_formed_closed_mu_aux (patt_exists _) _ = true |- _]
        => simpl in H

      | [H: well_formed_closed_ex_aux (patt_exists _) _ = true |- _]
        => simpl in H

      | [ |- well_formed_closed_mu_aux (free_evar_subst _ _ _) _ = true]
        => apply wfc_mu_free_evar_subst

      | [ |- well_formed_closed_ex_aux (free_evar_subst _ _ _) _ = true]
        => apply wfc_ex_free_evar_subst_2; simpl

      | [ |- well_formed_positive (bsvar_subst _ _ _) = true ]
        => apply wfp_bsvar_subst

      | [ |- well_formed_positive _ = true ]
        => progress (simpl; split_and?)

      | [ |- no_negative_occurrence_db_b _ (free_evar_subst _ _ _) = true ]
        => apply free_evar_subst_preserves_no_negative_occurrence

      | [ |- well_formed_closed_mu_aux (bsvar_subst _ _ _) _ = true ]
        => apply wfc_mu_aux_bsvar_subst

      | [ |- well_formed_closed_ex_aux (bsvar_subst _ _ _) _ = true ]
        => apply wfc_ex_aux_bsvar_subst

      | [ |- svar_has_negative_occurrence _ (svar_open _ _ _) = false] =>
        unfold svar_open; apply svar_hno_bsvar_subst

      |[ |- context C [ svar_quantify ?X ?n (svar_open ?n ?X _) ] ]
        => rewrite svar_quantify_svar_open

      | [ |- well_formed_closed_mu_aux (svar_open _ _ _) _ = true] =>
        unfold svar_open; apply wfc_mu_aux_bsvar_subst

      | [ |- well_formed_closed_ex_aux (svar_open _ _ _) _ = true] =>
        unfold svar_open; apply wfc_ex_aux_bsvar_subst

      | [ |- no_negative_occurrence_db_b _ _ = true ]
        => solve [unfold well_formed in *; simpl in *; destruct_and!; assumption]

      | [ |- no_negative_occurrence_db_b _ (free_evar_subst _ _ _) = true ]
        => apply free_evar_subst_preserves_no_negative_occurrence

      (* last option for [svar_has_negative_occurrence] *)
      | [ |- svar_has_negative_occurrence _ _ = false ]
        => apply svar_hno_false_if_fresh

      | [ |- svar_is_fresh_in _ _ ]
        => unfold svar_is_fresh_in

        (* last option for well_formed_closed_ex_aux: try decreasing n *)
      | [ |- well_formed_closed_ex_aux ?p (S ?n) = true ]
        => eapply well_formed_closed_ex_aux_ind with (ind_evar1 := n);[lia|]

        (* last option for well_formed_closed_mu_aux: try decreasing n *)
      | [ |- well_formed_closed_mu_aux ?p (S ?n) = true ]
        => eapply well_formed_closed_mu_aux_ind with (ind_svar1 := n);[lia|]

      end; unfold is_true in *
    ).

Lemma wfcex_after_subst_impl_wfcex_before {Σ : Signature} ϕ ψ x dbi:
  well_formed_closed_ex_aux (free_evar_subst ϕ ψ x) dbi = true ->
  well_formed_closed_ex_aux ϕ dbi = true.
Proof.
  intros Hsubst.
  move: dbi Hsubst.
  induction ϕ; intros dbi Hsubst; simpl in *; auto.
  - apply andb_prop in Hsubst. destruct Hsubst as [Hsubst1 Hsubst2].
    specialize (IHϕ1 dbi Hsubst1).
    specialize (IHϕ2 dbi Hsubst2).
    rewrite IHϕ1 IHϕ2.
    reflexivity.
  - apply andb_prop in Hsubst. destruct Hsubst as [Hsubst1 Hsubst2].
    specialize (IHϕ1 dbi Hsubst1).
    specialize (IHϕ2 dbi Hsubst2).
    rewrite IHϕ1 IHϕ2.
    reflexivity.
Qed.

Lemma wfcmu_after_subst_impl_wfcmu_before {Σ : Signature} ϕ ψ x dbi:
  well_formed_closed_mu_aux (free_evar_subst ϕ ψ x) dbi = true ->
  well_formed_closed_mu_aux ϕ dbi = true.
Proof.
  intros Hsubst.
  move: dbi Hsubst.
  induction ϕ; intros dbi Hsubst; simpl in *; auto.
  - apply andb_prop in Hsubst. destruct Hsubst as [Hsubst1 Hsubst2].
    specialize (IHϕ1 dbi Hsubst1).
    specialize (IHϕ2 dbi Hsubst2).
    rewrite IHϕ1 IHϕ2.
    reflexivity.
  - apply andb_prop in Hsubst. destruct Hsubst as [Hsubst1 Hsubst2].
    specialize (IHϕ1 dbi Hsubst1).
    specialize (IHϕ2 dbi Hsubst2).
    rewrite IHϕ1 IHϕ2.
    reflexivity.
Qed.

Lemma nno_after_subst_impl_nno_before {Σ : Signature} ϕ ψ x dbi:
  no_negative_occurrence_db_b dbi (free_evar_subst ϕ ψ x) = true ->
  no_negative_occurrence_db_b dbi ϕ = true
with npo_after_subst_impl_npo_before {Σ : Signature} ϕ ψ x dbi:
  no_positive_occurrence_db_b dbi (free_evar_subst ϕ ψ x) = true ->
  no_positive_occurrence_db_b dbi ϕ = true.
Proof.
  - move: dbi.
    induction ϕ; intros dbi Hsubst; cbn in *; auto.
    + apply andb_prop in Hsubst. destruct Hsubst as [Hsubst1 Hsubst2].
      specialize (IHϕ1 dbi Hsubst1).
      specialize (IHϕ2 dbi Hsubst2).
      rewrite IHϕ1. rewrite IHϕ2.
      reflexivity.
    + apply andb_prop in Hsubst. destruct Hsubst as [Hsubst1 Hsubst2].
      fold no_positive_occurrence_db_b in Hsubst1.
      fold no_positive_occurrence_db_b.
      specialize (IHϕ2 dbi Hsubst2).
      rewrite IHϕ2.
      erewrite npo_after_subst_impl_npo_before.
      reflexivity. eassumption.
  - move: dbi.
    induction ϕ; intros dbi Hsubst; cbn in *; auto.
    + apply andb_prop in Hsubst. destruct Hsubst as [Hsubst1 Hsubst2].
      specialize (IHϕ1 dbi Hsubst1).
      specialize (IHϕ2 dbi Hsubst2).
      rewrite IHϕ1. rewrite IHϕ2.
      reflexivity.
    + apply andb_prop in Hsubst. destruct Hsubst as [Hsubst1 Hsubst2].
      fold no_negative_occurrence_db_b in Hsubst1.
      fold no_negative_occurrence_db_b.
      specialize (IHϕ2 dbi Hsubst2).
      rewrite IHϕ2.
      erewrite nno_after_subst_impl_nno_before.
      reflexivity. eassumption.
Qed.

#[export]
 Hint Resolve wfc_mu_free_evar_subst : core.

Lemma wfp_after_subst_impl_wfp_before {Σ : Signature} ϕ ψ x:
  well_formed_positive (free_evar_subst ϕ ψ x) = true ->
  well_formed_positive ϕ = true.
Proof.
  intros Hsubst.
  move: Hsubst.
  induction ϕ; intros Hsubst; simpl in *; auto.
  - apply andb_prop in Hsubst. destruct Hsubst as [Hsubst1 Hsubst2].
    specialize (IHϕ1 Hsubst1).
    specialize (IHϕ2 Hsubst2).
    rewrite IHϕ1. rewrite IHϕ2.
    reflexivity.
  - apply andb_prop in Hsubst. destruct Hsubst as [Hsubst1 Hsubst2].
    specialize (IHϕ1 Hsubst1).
    specialize (IHϕ2 Hsubst2).
    rewrite IHϕ1. rewrite IHϕ2.
    reflexivity.
  - apply andb_prop in Hsubst. destruct Hsubst as [Hnno Hsubst]. 
    specialize (IHϕ Hsubst).
    rewrite IHϕ.
    erewrite nno_after_subst_impl_nno_before.
    reflexivity. eassumption.
Qed.

Lemma wf_after_subst_impl_wf_before {Σ : Signature} ϕ ψ x:
  well_formed (free_evar_subst ϕ ψ x) = true ->
  well_formed ϕ = true.
Proof.
  intros H.
  unfold well_formed,well_formed_closed in *.
  destruct_and!.
  split_and!.
  - eapply wfp_after_subst_impl_wfp_before. eassumption.
  - eapply wfcmu_after_subst_impl_wfcmu_before. eassumption.
  - eapply wfcex_after_subst_impl_wfcex_before. eassumption.
Qed.

Lemma wf_emplaced_impl_wf_context {Σ : Signature} (C : PatternCtx) (ψ : Pattern) :
  well_formed (emplace C ψ) = true ->
  PC_wf C.
Proof.
  intros H.
  unfold emplace in H. unfold PC_wf.
  eapply wf_after_subst_impl_wf_before.
  eassumption.
Qed.

Global Instance evar_is_fresh_in_dec {Σ : Signature} (x : evar) (p : Pattern) :
  Decision (evar_is_fresh_in x p).
Proof.
  unfold evar_is_fresh_in.
  apply not_dec. apply gset_elem_of_dec.
Defined.

Definition evar_is_fresh_in_list {Σ : Signature} (x : evar) (l : list Pattern) :=
  Forall (evar_is_fresh_in x) l.

Global Instance evar_is_fresh_in_list_dec {Σ : Signature} (x : evar) (l : list Pattern) :
  Decision (evar_is_fresh_in_list x l).
Proof.
  unfold Decision. unfold evar_is_fresh_in_list.
  apply Forall_dec.
  intros p.
  apply evar_is_fresh_in_dec.
Defined.

Global Instance svar_is_fresh_in_dec {Σ : Signature} (X : svar) (p : Pattern) :
  Decision (svar_is_fresh_in X p).
Proof.
  unfold svar_is_fresh_in.
  apply not_dec. apply gset_elem_of_dec.
Defined.

Definition svar_is_fresh_in_list {Σ : Signature} (X : svar) (l : list Pattern) :=
  Forall (svar_is_fresh_in X) l.

Global Instance svar_is_fresh_in_list_dec {Σ : Signature} (X : svar) (l : list Pattern) :
  Decision (svar_is_fresh_in_list X l).
Proof.
  unfold Decision. unfold svar_is_fresh_in_list.
  apply Forall_dec.
  intros p.
  apply svar_is_fresh_in_dec.
Defined.

Lemma no_neg_occ_quan_impl_no_neg_occ {Σ : Signature} x n1 n2 ϕ:
 no_negative_occurrence_db_b n1 (evar_quantify x n2 ϕ) = true ->
 no_negative_occurrence_db_b n1 ϕ = true
with no_pos_occ_quan_impl_no_pos_occ {Σ : Signature} x n1 n2 ϕ:
 no_positive_occurrence_db_b n1 (evar_quantify x n2 ϕ) = true ->
 no_positive_occurrence_db_b n1 ϕ = true.
Proof.
 - intros H.
   move: n1 n2 H.
   induction ϕ; intros n1 n2 H; simpl in *; auto.
   + unfold no_negative_occurrence_db_b in *. simpl in *. fold no_negative_occurrence_db_b in *.
     destruct_and!.
     erewrite -> IHϕ1 by eassumption.
     erewrite -> IHϕ2 by eassumption.
     reflexivity.
   + unfold no_negative_occurrence_db_b in *. simpl in *.
     fold no_negative_occurrence_db_b no_positive_occurrence_db_b in *.
     destruct_and!.
     erewrite -> no_pos_occ_quan_impl_no_pos_occ by eassumption.
     erewrite -> IHϕ2 by eassumption.
     reflexivity.
   + unfold no_negative_occurrence_db_b in *. simpl in *. fold no_negative_occurrence_db_b in *.
     erewrite -> IHϕ by eassumption.
     reflexivity.
   + unfold no_negative_occurrence_db_b in *. simpl in *. fold no_negative_occurrence_db_b in *.
     erewrite -> IHϕ by eassumption.
     reflexivity.
 - intros H.
   move: n1 n2 H.
   induction ϕ; intros n1 n2 H; simpl in *; auto.
   + unfold no_positive_occurrence_db_b in *. simpl in *. fold no_positive_occurrence_db_b in *.
     destruct_and!.
     erewrite -> IHϕ1 by eassumption.
     erewrite -> IHϕ2 by eassumption.
     reflexivity.
   + unfold no_positive_occurrence_db_b in *. simpl in *.
     fold no_positive_occurrence_db_b no_negative_occurrence_db_b in *.
     destruct_and!.
     erewrite -> no_neg_occ_quan_impl_no_neg_occ by eassumption.
     erewrite -> IHϕ2 by eassumption.
     reflexivity.
   + unfold no_positive_occurrence_db_b in *. simpl in *. fold no_positive_occurrence_db_b in *.
     erewrite -> IHϕ by eassumption.
     reflexivity.
   + unfold no_positive_occurrence_db_b in *. simpl in *. fold no_positive_occurrence_db_b in *.
     erewrite -> IHϕ by eassumption.
     reflexivity.
Qed.

Lemma wfp_evar_quan_impl_wfp {Σ : Signature} x n ϕ:
  well_formed_positive (evar_quantify x n ϕ) = true ->
  well_formed_positive ϕ.
Proof.
  intros H.
  move: n H.
  induction ϕ; intros n' H; simpl in *; auto.
  - destruct_and!.
    erewrite -> IHϕ1 by eassumption.
    erewrite -> IHϕ2 by eassumption.
    reflexivity.
  - destruct_and!.
    erewrite -> IHϕ1 by eassumption.
    erewrite -> IHϕ2 by eassumption.
    reflexivity.
  - erewrite IHϕ by eassumption.
    reflexivity.
  - simpl.
    destruct_and!.
    erewrite -> IHϕ by eassumption.
    erewrite -> no_neg_occ_quan_impl_no_neg_occ by eassumption.
    reflexivity.
Qed.

Lemma wfcex_evar_quan_impl_wfcex {Σ : Signature} x n dbi ϕ:
  well_formed_closed_ex_aux (evar_quantify x n ϕ) dbi = true ->
  well_formed_closed_ex_aux ϕ dbi.
Proof.
  intros H.
  move: n dbi H.
  induction ϕ; intros n' dbi H; simpl in *; auto.
  - destruct_and!.
    erewrite -> IHϕ1 by eassumption.
    erewrite -> IHϕ2 by eassumption.
    reflexivity.
  - destruct_and!.
    erewrite -> IHϕ1 by eassumption.
    erewrite -> IHϕ2 by eassumption.
    reflexivity.
  - erewrite IHϕ by eassumption.
    reflexivity.
  - simpl.
    erewrite -> IHϕ by eassumption.
    reflexivity.
Qed.

Lemma wfcmu_evar_quan_impl_wfcmu {Σ : Signature} x n dbi ϕ:
  well_formed_closed_mu_aux (evar_quantify x n ϕ) dbi = true ->
  well_formed_closed_mu_aux ϕ dbi.
Proof.
  intros H.
  move: n dbi H.
  induction ϕ; intros n' dbi H; simpl in *; auto.
  - destruct_and!.
    erewrite -> IHϕ1 by eassumption.
    erewrite -> IHϕ2 by eassumption.
    reflexivity.
  - destruct_and!.
    erewrite -> IHϕ1 by eassumption.
    erewrite -> IHϕ2 by eassumption.
    reflexivity.
  - erewrite IHϕ by eassumption.
    reflexivity.
  - simpl.
    erewrite -> IHϕ by eassumption.
    reflexivity.
Qed.

Lemma wfc_ex_lower (Σ : Signature) ϕ n:
  bevar_occur ϕ n = false ->
  well_formed_closed_ex_aux ϕ (S n) = true ->
  well_formed_closed_ex_aux ϕ n = true.
Proof.
  intros H1 H2.
  move: n H1 H2.
  induction ϕ; intros n' H1 H2; simpl in *; auto.
  - repeat case_match; auto. lia.
  - apply orb_false_elim in H1. destruct_and!.
    erewrite -> IHϕ1 by eassumption.
    erewrite -> IHϕ2 by eassumption.
    reflexivity.
  - apply orb_false_elim in H1. destruct_and!.
    erewrite -> IHϕ1 by eassumption.
    erewrite -> IHϕ2 by eassumption.
    reflexivity.
Qed.

Lemma wfc_mu_lower (Σ : Signature) ϕ n:
  bsvar_occur ϕ n = false ->
  well_formed_closed_mu_aux ϕ (S n) = true ->
  well_formed_closed_mu_aux ϕ n = true.
Proof.
  intros H1 H2.
  move: n H1 H2.
  induction ϕ; intros n' H1 H2; simpl in *; auto.
  - repeat case_match; auto. lia.
  - apply orb_false_elim in H1. destruct_and!.
    erewrite -> IHϕ1 by eassumption.
    erewrite -> IHϕ2 by eassumption.
    reflexivity.
  - apply orb_false_elim in H1. destruct_and!.
    erewrite -> IHϕ1 by eassumption.
    erewrite -> IHϕ2 by eassumption.
    reflexivity.
Qed.

Lemma wf_ex_quan_impl_wf {Σ : Signature} (x : evar) (ϕ : Pattern):
  bevar_occur ϕ 0 = false ->
  well_formed (exists_quantify x ϕ) = true ->
  well_formed ϕ = true.
Proof.
  intros H0 H. unfold exists_quantify in H.
  unfold well_formed, well_formed_closed in *. destruct_and!. simpl in *.
  split_and!.
  - eapply wfp_evar_quan_impl_wfp. eassumption.
  - eapply wfcmu_evar_quan_impl_wfcmu. eassumption.
  - apply wfcex_evar_quan_impl_wfcex in H3.
    apply wfc_ex_lower; assumption.
Qed.

Lemma bevar_occur_evar_open_2 {Σ : Signature} dbi x ϕ:
  well_formed_closed_ex_aux ϕ dbi ->
  bevar_occur (evar_open dbi x ϕ) dbi = false.
Proof.
  move: dbi.
  unfold evar_open.
  induction ϕ; intros dbi Hwf; simpl; try reflexivity.
  - case_match; simpl; auto.
    case_match; try lia. simpl in Hwf. case_match; [lia | congruence ].
  - simpl in Hwf. destruct_and!.
    rewrite IHϕ1; auto. rewrite IHϕ2; auto.
  - simpl in Hwf. destruct_and!.
    rewrite IHϕ1; auto. rewrite IHϕ2; auto.
  - rewrite IHϕ; auto.
  - rewrite IHϕ; auto.
Qed.

Lemma bsvar_occur_svar_open_2 {Σ : Signature} dbi X ϕ:
  well_formed_closed_mu_aux ϕ dbi ->
  bsvar_occur (svar_open dbi X ϕ) dbi = false.
Proof.
  move: dbi.
  unfold svar_open.
  induction ϕ; intros dbi Hwf; simpl; try reflexivity.
  - case_match; simpl; auto.
    case_match; try lia. simpl in Hwf. case_match; [lia | congruence ].
  - simpl in Hwf. destruct_and!.
    rewrite IHϕ1; auto. rewrite IHϕ2; auto.
  - simpl in Hwf. destruct_and!.
    rewrite IHϕ1; auto. rewrite IHϕ2; auto.
  - rewrite IHϕ; auto.
  - rewrite IHϕ; auto.
Qed.

