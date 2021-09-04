From Coq Require Import ssreflect ssrfun ssrbool.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import Setoid.
Require Import List.
Require Import Ensembles.
Require Import Coq.Strings.String.
Require Import extralibrary.

From Coq Require Import Logic.Classical_Prop.
From stdpp Require Import countable infinite.
From stdpp Require Import pmap gmap mapset fin_sets.
Require Import stdpp_ext.

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
                           | Nat_greater _ _ _ => patt_bound_evar n (* (pred n) in Leroy's paper *)
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
    | patt_free_evar x' => if decide (x = x') then psi else patt_free_evar x'
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
  Fixpoint free_svar_subst (phi psi : Pattern) (X : svar) :=
    match phi with
    | patt_free_evar x => patt_free_evar x
    | patt_free_svar X' => if decide (X = X') then psi else patt_free_svar X'
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

  (* replace element varial x with de Bruijn index level *)
  Fixpoint evar_quantify (x : evar) (level : db_index)
           (p : Pattern) : Pattern :=
    match p with
    | patt_free_evar x' => if decide (x = x') then patt_bound_evar level else patt_free_evar x'
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

  (* replace de Bruijn index k with element variable n *)
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

  (* evar_open is identity if n does not occur in phi *)
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
  
  (* replace de Bruijn index k with set variable n *)
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

  (* More trivial but useful lemmas *)
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
    intros k n p. generalize dependent k.
    induction p; intros k; simpl; try reflexivity.
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
    intros k n p. generalize dependent k.
    induction p; intros k; simpl; try reflexivity.
    destruct (n0 =? k); reflexivity.
    rewrite (IHp1 k); rewrite (IHp2 k); reflexivity.
    rewrite (IHp1 k); rewrite (IHp2 k); reflexivity.
    rewrite (IHp k); reflexivity.
    rewrite (IHp (S k)); reflexivity.
  Qed.

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
    induction phi; intros db1 db2 x'; simpl; split; try constructor; try inversion H; subst; try firstorder.
    * destruct (n =? db2); intros. constructor. assumption.
    * destruct (n =? db2); intros. constructor. assumption.
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
    intros H H0 H1.
    generalize dependent ind_evar1. generalize dependent ind_evar2.
    generalize dependent ind_svar1. generalize dependent ind_svar2.
    induction phi; intros ind_svar_2 ind_svar_1 Hleqsvar ind_evar_2 ind_evar_1 Heqevar H;
      simpl in *; try lia; auto.
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
    - induction phi; intros n' n'' x' H; try lia; auto.
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
    intros phi WFE.
    unfold wfc_body_ex. intros x H.
    unfold well_formed_closed in *. simpl in WFE.
    apply wfc_aux_body_ex_imp1. auto.
  Qed.

  Lemma well_formed_bott:
    well_formed patt_bott.
  Proof.
    unfold well_formed. simpl.
    unfold well_formed_closed. simpl.
    reflexivity.
  Qed.

  Lemma well_formed_imp ϕ₁ ϕ₂:
    well_formed ϕ₁ ->
    well_formed ϕ₂ ->
    well_formed (patt_imp ϕ₁ ϕ₂).
  Proof.
    unfold well_formed. unfold well_formed_closed. simpl.
    intros H1 H2.
    apply andb_prop in H1. destruct H1 as [H11 H12].
    apply andb_prop in H2. destruct H2 as [H21 H22].
    rewrite !(H11,H12,H21,H22).
    reflexivity.
  Qed.

  Lemma well_formed_app ϕ₁ ϕ₂:
    well_formed ϕ₁ ->
    well_formed ϕ₂ ->
    well_formed (patt_app ϕ₁ ϕ₂).
  Proof.
    unfold well_formed. unfold well_formed_closed. simpl.
    intros H1 H2.
    apply andb_prop in H1. destruct H1 as [H11 H12].
    apply andb_prop in H2. destruct H2 as [H21 H22].
    rewrite !(H11,H12,H21,H22).
    reflexivity.
  Qed.

  Lemma well_formed_ex_app ϕ₁ ϕ₂:
    well_formed (patt_exists ϕ₁) ->
    well_formed (patt_exists ϕ₂) ->
    well_formed (patt_exists (patt_app ϕ₁ ϕ₂)).
  Proof.
    intros Hwf1 Hwf2.
    unfold well_formed in *.
    apply andb_prop in Hwf1. apply andb_prop in Hwf2.
    destruct Hwf1 as [Hwfp1 Hwfc1]. destruct Hwf2 as [Hwfp2 Hwfc2].
    simpl in *. rewrite Hwfp1 Hwfp2. simpl. clear Hwfp1 Hwfp2.
    unfold well_formed_closed in *. simpl in *.
    rewrite Hwfc1. rewrite Hwfc2.
    reflexivity.
  Qed.

  Lemma well_formed_impl_well_formed_ex ϕ:
    well_formed ϕ ->
    well_formed (patt_exists ϕ).
  Proof.
    intros H. unfold well_formed in *. apply andb_prop in H. destruct H as [Hwfp Hwfc].
    simpl in *. rewrite Hwfp. clear Hwfp. simpl.
    unfold well_formed_closed in *. simpl.
    eapply well_formed_closed_aux_ind. 3: apply Hwfc. all: lia.
  Qed.

  (* fresh variables *)
  
  Definition evar_fresh (l : list evar) : evar := @infinite_fresh _ evar_infinite l.
  Definition svar_fresh (l : list svar) : svar := @infinite_fresh _ svar_infinite l.
  
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

  Lemma evar_is_fresh_in_evar_quantify x n phi:
    evar_is_fresh_in x (evar_quantify x n phi).
  Proof.
    move: n.
    unfold evar_is_fresh_in.
    induction phi; intros n'; simpl; try apply not_elem_of_empty.
    - destruct (decide (x = x0)); simpl.
      + apply not_elem_of_empty.
      + apply not_elem_of_singleton_2. assumption.
    - apply not_elem_of_union.
      split; auto.
    - apply not_elem_of_union.
      split; auto.
    - auto.
    - auto.
  Qed.

  (* Lemmas about wfc_ex and wfc_mu *)

  (*If phi is a closed body, then (ex, phi) is closed too*)
  Lemma wfc_body_to_wfc_ex:
    forall phi, wfc_body_ex phi -> well_formed_closed (patt_exists phi).
  Proof.
    intros phi WFE. unfold wfc_body_ex in WFE. unfold well_formed_closed. simpl.
    unfold well_formed_closed in WFE.
    apply (@wfc_aux_body_ex_imp2 phi 0 0 (fresh_evar phi)) in WFE. exact WFE.
    clear WFE.
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

  (* Helper for wfc_mu_to_wfc_body *)
  Lemma wfc_aux_body_mu_imp1:
    forall phi n n' X,
      well_formed_closed_aux phi n (S n')
      ->
      well_formed_closed_aux (svar_open n' X phi) n n'.
  Proof.
    - induction phi; intros n' n'' X H; try lia; auto.
      * simpl. inversion H. apply Nat.ltb_lt in H1. destruct (n=?n'') eqn:Heq.
        -- reflexivity.
        -- simpl. apply Nat.ltb_lt. apply beq_nat_false in Heq. lia.
      * simpl. simpl in H. apply andb_true_iff in H. destruct H as [H1 H2].
        rewrite IHphi1. apply H1. rewrite IHphi2. apply H2. reflexivity.
      * simpl. simpl in H. apply andb_true_iff in H. destruct H as [H1 H2].
        rewrite IHphi1. apply H1. rewrite IHphi2. apply H2. reflexivity.
      * simpl. simpl in H. rewrite IHphi. apply H. reflexivity.
      * simpl. simpl in H. rewrite IHphi. apply H. reflexivity.
  Qed.

  (* Helper for wfc_body_to_wfc_mu *)
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
    intros phi n n' m m' H H0 H1.
    generalize dependent n. generalize dependent n'.
    generalize dependent m. generalize dependent m'.
    induction phi; intros m' m'' H n' n'' H0 H1; try lia; auto.
    * simpl. apply Nat.ltb_lt. apply Nat.ltb_lt in H0. lia.
    * simpl. apply Nat.ltb_lt. apply Nat.ltb_lt in H0. lia.
    * simpl. simpl in H0. apply andb_true_iff in H0. destruct H0 as [H2 H3].
      apply andb_true_iff. split. erewrite IHphi1; eauto. erewrite IHphi2; eauto.
    * simpl. simpl in H0. apply andb_true_iff in H0. destruct H0 as [H2 H3].
      apply andb_true_iff. split. erewrite IHphi1; eauto. erewrite IHphi2; eauto.
    * simpl. simpl in H0. erewrite IHphi with (n' := S n') (m' := m'); eauto. lia.
    * simpl. simpl in H0. erewrite IHphi with (n' := n') (m' := S m').
      3: exact H0. all: auto; lia.
  Qed.

  Lemma wfc_aux_body_mu_imp_bsvar_subst:
    forall phi psi n n',
      well_formed_closed_aux phi n (S n')
      -> well_formed_closed_aux psi n n'
      -> well_formed_closed_aux (bsvar_subst phi psi n') n n'.
  Proof.
    intros phi psi n n' H H0. 
    generalize dependent n. generalize dependent n'. generalize dependent psi.
    induction phi; intros psi n' n'' H H0; try lia; auto.
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
    intros phi H.
    unfold wfc_body_mu. intros.
    unfold well_formed_closed in *. simpl in H.
    apply wfc_aux_body_mu_imp1. auto.
  Qed.

  (*If phi is a closed body, then (mu, phi) is closed too*)
  Lemma wfc_body_to_wfc_mu:
    forall phi, wfc_body_mu phi -> well_formed_closed (patt_mu phi).
  Proof.
    intros phi H. unfold wfc_body_mu in H. unfold well_formed_closed. simpl.
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
    - simpl. destruct (n =? n') eqn:P.
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
    unfold wfp_body_ex. intros phi H x H0.
    apply wfp_evar_open. simpl in H. assumption.
  Qed.

  (* Connection between bodies and well-formedness *)
  Definition wf_body_ex phi := forall x, 
      x ∉ (free_evars phi) -> well_formed (evar_open 0 x phi).

  (* This might be useful in soundness cases prop_ex_left/right *)
  Lemma wf_ex_to_wf_body: forall phi,
      well_formed (patt_exists phi) ->
      wf_body_ex phi.
  Proof.
    unfold wf_body_ex. intros phi H x H0. unfold well_formed in *.
    apply andb_true_iff in H.
    destruct H as [H1 H2].
    rewrite (@wfp_ex_to_wfp_body phi H1). assumption.
    rewrite (@wfc_ex_to_wfc_body phi H2). assumption.
    reflexivity.
  Qed.


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
    intros phi H. induction H; simpl; auto.
    - unfold well_formed_closed. simpl. unfold well_formed_closed in *.
      rewrite IHwell_formed_closed_induc1.
      rewrite IHwell_formed_closed_induc2. reflexivity.
    - unfold well_formed_closed. simpl. unfold well_formed_closed in *.
      rewrite IHwell_formed_closed_induc1.
      rewrite IHwell_formed_closed_induc2. reflexivity. 
    - apply wfc_body_to_wfc_ex. unfold wfc_body_ex. assumption.
    - apply wfc_body_to_wfc_mu. unfold wfc_body_mu. assumption.
  Qed.

  (* Additional lemmas: evar_open, svar_open, freshness, well_formedness, etc. *)

  (* evar_open and evar_quantify are inverses *)
  Lemma evar_open_evar_quantify x n n' phi:
    well_formed_closed_aux phi n n' ->
    (evar_open n x (evar_quantify x n phi)) = phi.
  Proof.
    intros H.
    (*apply wfc_wfc_ind in H.*)
    move: n n' H.
    induction phi; intros n' n'' H; simpl; auto.
    - destruct (decide (x = x0)); simpl.
      + rewrite Nat.eqb_refl. subst. reflexivity.
      + reflexivity.
    - simpl in *. apply Nat.ltb_lt in H.
      destruct (n =? n') eqn:Heq.
      + apply Nat.eqb_eq in Heq. subst. lia.
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

  Lemma evar_quantify_evar_open x m n n' phi: n < m ->
    x ∉ free_evars phi -> well_formed_closed_aux phi m n' ->
    (evar_quantify x n (evar_open n x phi)) = phi.
  Proof.
    revert m n n'.
    induction phi; intros m' n' n'' H H0 H1; simpl; auto.
    - destruct (decide (x = x0)); simpl.
      + subst. simpl in H0. apply sets.not_elem_of_singleton_1 in H0. congruence.
      + reflexivity.
    - simpl in *. apply Nat.ltb_lt in H1.
      destruct (n =? n') eqn:Heq.
      + apply Nat.eqb_eq in Heq. subst. simpl. destruct (decide (x = x)); auto.
        congruence.
      + reflexivity.
    - simpl in H.
      apply andb_true_iff in H1. destruct H1 as [F1 F2].
      apply sets.not_elem_of_union in H0. destruct H0 as [E1 E2].
      erewrite -> IHphi1, IHphi2.
      reflexivity.
      all: eauto.
    - simpl in H.
      apply andb_true_iff in H1. destruct H1 as [F1 F2].
      apply sets.not_elem_of_union in H0. destruct H0 as [E1 E2].
      erewrite -> IHphi1, IHphi2.
      reflexivity.
      all: eauto.
    - simpl in H0. simpl in H1.
      erewrite -> IHphi. reflexivity. instantiate (1 := S m'). lia.
      auto. apply H1.
    - simpl in H0. simpl in H1.
      erewrite -> IHphi. reflexivity. exact H.
      auto. apply H1.
  Qed.

  Lemma double_evar_quantify φ : forall x n,
    evar_quantify x n (evar_quantify x n φ) = evar_quantify x n φ.
  Proof.
    induction φ; intros x' n'; simpl; auto.
    * break_match_goal; simpl; auto. rewrite Heqb. auto.
    * now rewrite -> IHφ1, -> IHφ2.
    * now rewrite -> IHφ1, -> IHφ2.
    * now rewrite IHφ.
    * now rewrite IHφ.
  Qed.

  Lemma well_formed_bevar_subst φ : forall ψ n k m,
    m >= n -> well_formed_closed_aux φ n k
  ->
    bevar_subst φ ψ m = φ.
  Proof.
    induction φ; intros ψ n' k' m' H H0; simpl; auto.
    * simpl in H0. break_match_goal; auto. apply NPeano.Nat.ltb_lt in H0. lia.
    * simpl in H0. apply eq_sym, andb_true_eq in H0. destruct H0. erewrite IHφ1, IHφ2.
      3: apply eq_sym, H1.
      4: apply eq_sym, H0. all: auto.
    * simpl in H0. apply eq_sym, andb_true_eq in H0. destruct H0. erewrite IHφ1, IHφ2.
      3: apply eq_sym, H1.
      4: apply eq_sym, H0. all: auto.
    * simpl in H0. erewrite IHφ. 3: apply H0. auto. lia.
    * simpl in H0. erewrite IHφ. 3: apply H0. all: auto.
  Qed.

  Lemma double_bevar_subst φ : forall ψ n k,
    well_formed_closed_aux ψ n k ->
    bevar_subst (bevar_subst φ ψ n) ψ n = bevar_subst φ ψ n.
  Proof.
    induction φ; intros ψ n' k' H; simpl; auto.
    * break_match_goal; simpl; auto.
      - rewrite Heqc. auto.
      - erewrite well_formed_bevar_subst. 3: exact H. all: auto. 
      - rewrite Heqc. auto.
    * erewrite IHφ1, IHφ2; eauto.
    * erewrite IHφ1, IHφ2; eauto.
    * erewrite IHφ. auto. eapply wfc_aux_extend. exact H. lia. auto.
    * erewrite IHφ. auto. eapply wfc_aux_extend. exact H. lia. auto.
  Qed.

  Lemma bevar_subst_well_formedness φ : forall n m ψ,
    well_formed_closed_aux φ (S n) m -> well_formed_closed_aux ψ n m
  ->
    well_formed_closed_aux (bevar_subst φ ψ n) n m.
  Proof.
    induction φ; intros n' m' ψ H H0; simpl; auto.
    * break_match_goal; auto. simpl in H. simpl. apply NPeano.Nat.ltb_lt. auto.
      simpl in H. apply NPeano.Nat.ltb_lt in H. lia.
    * simpl in H. apply eq_sym, andb_true_eq in H. destruct H. rewrite -> IHφ1, -> IHφ2; auto.
    * simpl in H. apply eq_sym, andb_true_eq in H. destruct H. rewrite -> IHφ1, -> IHφ2; auto.
    * simpl. rewrite IHφ; auto.
      eapply wfc_aux_extend. exact H0. all: lia.
    * simpl. simpl in H. rewrite IHφ; auto.
      eapply wfc_aux_extend. exact H0. all: lia.
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

  Lemma svar_open_evar_open_comm
    : forall (phi : Pattern) (dbi1 : db_index)(x : evar)(dbi2 : db_index)(X : svar),
      evar_open dbi1 x (svar_open dbi2 X phi) = svar_open dbi2 X (evar_open dbi1 x phi).
  Proof.
    induction phi; intros dbi1' x' dbi2' X'; simpl; try reflexivity.
    * destruct (n =? dbi1'); reflexivity.
    * destruct (n =? dbi2'); reflexivity.
    * rewrite -> IHphi1. rewrite -> IHphi2. reflexivity.
    * rewrite -> IHphi1. rewrite -> IHphi2. reflexivity.
    * rewrite -> IHphi. reflexivity.
    * rewrite -> IHphi. reflexivity.
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
    induction psi; intros dbi X; simpl; try reflexivity.
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
    * unfold not. intros H0. apply H. apply elem_of_singleton_2. symmetry. assumption.
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
    induction ϕ; intros dbi x'; simpl; try reflexivity.
    * destruct (n =? dbi); reflexivity.
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
      (positive_occurrence_db dbi phi ->
       positive_occurrence_named X phi ->
       positive_occurrence_named X (svar_open dbi X phi))
      /\ (negative_occurrence_db dbi phi ->
          negative_occurrence_named X phi ->
          negative_occurrence_named X (svar_open dbi X phi)).
  Proof.
    induction phi; intros dbi X; split; simpl; try firstorder.
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
  
  Lemma positive_negative_occurrence_evar_open : forall (ϕ : Pattern) (X : svar) (dbi : db_index) (x : evar),
      (positive_occurrence_named X (evar_open dbi x ϕ) <-> positive_occurrence_named X ϕ)
      /\ (negative_occurrence_named X (evar_open dbi x ϕ) <-> negative_occurrence_named X ϕ).
  Proof.
    induction ϕ; intros X dbi x'; simpl; split; try reflexivity.
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
    intros ϕ X dbi x.
    pose proof (P := positive_negative_occurrence_evar_open ϕ X dbi x).
    destruct P as [P _]. exact P.
  Qed.

  Lemma negative_occurrence_evar_open : forall (ϕ : Pattern) (X : svar) (dbi : db_index) (x : evar),
      negative_occurrence_named X (evar_open dbi x ϕ) <-> negative_occurrence_named X ϕ.
  Proof.
    intros ϕ X dbi x.
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
    induction phi; intros dbi X; simpl; split; intros; try constructor; try inversion H; try firstorder.
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
    induction phi; intros dbi1 dbi2 X Hneq; split; intros H; inversion H; subst; simpl in *; auto.
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
    induction phi; simpl; intros dbi X H.
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
      unfold not. intros H0. assert (X = Y). symmetry. assumption.
      unfold not in XneY. destruct (XneY H).
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
    intros H.
    unfold well_formed_closed in H.
    apply evar_open_wfc_aux with (X := X)(db2 := m) in H.
    2: lia.
    auto.
  Qed.

  Lemma svar_open_wfc_aux db1 db2 dbs X phi :
    db1 <= db2 ->
    well_formed_closed_aux phi dbs db1 ->
    svar_open db2 X phi = phi.
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
      rewrite -> IHphi with (dbs := S dbs)(db1 := db1). 3: auto. 2: auto. auto.
    * apply f_equal. rewrite -> IHphi with (dbs := dbs)(db1 := S db1). auto. lia. auto.
  Qed.

  Lemma svar_open_wfc m X phi : well_formed_closed phi -> svar_open m X phi = phi.
  Proof.
    intros H.
    unfold well_formed_closed in H.
    apply svar_open_wfc_aux with (X := X)(db2 := m) in H.
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

    Lemma svar_open_bevar_subst m phi1 phi2 dbi X
    : well_formed_closed phi2 ->
      svar_open m X (bevar_subst phi1 phi2 dbi)
      = bevar_subst (svar_open m X phi1) phi2 dbi.
  Proof.
    generalize dependent dbi. generalize dependent m. induction phi1; intros m dbi Hwfc; auto.
    - simpl. destruct (compare_nat n dbi); simpl; auto. auto using svar_open_wfc.
    - simpl. destruct (n =? m) eqn:Heq, (compare_nat n (S dbi)) eqn:Hdbi; simpl; auto.
    - simpl. rewrite -> IHphi1_1. rewrite -> IHphi1_2. auto. auto. auto.
    - simpl. rewrite -> IHphi1_1. rewrite -> IHphi1_2. auto. auto. auto.
    - simpl. apply f_equal. rewrite -> IHphi1. auto. auto.
    - simpl. rewrite -> IHphi1. auto. auto.
  Qed.

  Lemma svar_open_bsvar_subst m phi1 phi2 dbi X
    : well_formed_closed phi2 ->
      m <> dbi ->
      svar_open m X (bsvar_subst phi1 phi2 dbi)
      = bsvar_subst (svar_open m X phi1) phi2 dbi.
  Proof.
    generalize dependent dbi. generalize dependent m. induction phi1; intros m dbi Hwfc Hneq; auto.
    - simpl. destruct (n =? m) eqn:Heq, (compare_nat n dbi) eqn:Hdbi; simpl; auto.
      + rewrite Heq. reflexivity.
      + apply beq_nat_true in Heq. lia.
      + rewrite Heq. reflexivity.
      + rewrite Heq. rewrite Hdbi. reflexivity.
      + rewrite Hdbi. apply svar_open_wfc. assumption.
      + rewrite Heq. rewrite Hdbi. reflexivity.
    - simpl. rewrite -> IHphi1_1; auto. rewrite -> IHphi1_2; auto.
    - simpl. rewrite -> IHphi1_1; auto. rewrite -> IHphi1_2; auto.
    - simpl. apply f_equal. rewrite -> IHphi1; auto.
    - simpl. rewrite -> IHphi1; auto.
  Qed.

  Lemma evar_open_bevar_subst m phi1 phi2 dbi X
    : well_formed_closed phi2 ->
      m < dbi ->
      evar_open m X (bevar_subst phi1 phi2 dbi)
      = bevar_subst (evar_open m X phi1) phi2 dbi.
  Proof.
    generalize dependent dbi. generalize dependent m. induction phi1; intros m dbi Hwfc Hneq; auto.
    - simpl. destruct (n =? m) eqn:Heq, (compare_nat n dbi) eqn:Hdbi; simpl; auto.
      + rewrite Heq. reflexivity.
      + apply beq_nat_true in Heq. lia.
      + apply beq_nat_true in Heq. lia.
      + rewrite Heq. rewrite Hdbi. reflexivity.
      + rewrite Hdbi. apply evar_open_wfc. assumption.
      + destruct (Init.Nat.pred n =? m) eqn:Hpred; rewrite Hdbi.
        * apply beq_nat_true in Hpred. lia.
        * rewrite Heq. reflexivity.
    - simpl. rewrite -> IHphi1_1; auto. rewrite -> IHphi1_2; auto.
    - simpl. rewrite -> IHphi1_1; auto. rewrite -> IHphi1_2; auto.
    - simpl. apply f_equal. rewrite -> IHphi1; auto. lia.
    - simpl. rewrite -> IHphi1; auto.
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

  Fixpoint count_evar_occurrences (x : evar) (p : Pattern) :=
    match p with
    | patt_free_evar x' => if decide (x' = x) then 1 else 0 
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

  Lemma free_evar_subst_no_occurrence x p q:
    count_evar_occurrences x p = 0 ->
    free_evar_subst p q x = p.
  Proof.
    intros H.
    induction p; simpl; auto.
    - simpl in H.
      destruct (decide (x = x0)).
      + subst x0. destruct (decide (x = x)). simpl in H. inversion H. contradiction.
      + reflexivity.
    - simpl in H. rewrite IHp1. lia. rewrite IHp2. lia. reflexivity.
    - simpl in H. rewrite IHp1. lia. rewrite IHp2. lia. reflexivity.
    - simpl in H. rewrite IHp. lia. reflexivity.
    - simpl in H. rewrite IHp. lia. reflexivity.
  Qed.


  Lemma wfc_impl_no_neg_pos_occ p n m:
    well_formed_closed_aux p n m ->
    (no_negative_occurrence_db_b m p && no_positive_occurrence_db_b m p) = true.
  Proof.
    intros H.
    move: n m H.
    induction p; intros n' m H; simpl; simpl in H; auto.
    - apply negb_true_iff. apply PeanoNat.Nat.eqb_neq.
      apply Nat.ltb_lt in H. lia.
    - apply andb_prop in H. destruct H as [H1 H2].
      specialize (IHp1 n' m H1). specialize (IHp2 n' m H2).
      apply andb_prop in IHp1. destruct IHp1 as [IHp11 IHp12].
      apply andb_prop in IHp2. destruct IHp2 as [IHp21 IHp22].
      rewrite IHp11 IHp12 IHp21 IHp22. reflexivity.
    - apply andb_prop in H. destruct H as [H1 H2].
      specialize (IHp1 n' m H1). specialize (IHp2 n' m H2).
      apply andb_prop in IHp1. destruct IHp1 as [IHp11 IHp12].
      apply andb_prop in IHp2. destruct IHp2 as [IHp21 IHp22].
      rewrite IHp11 IHp12 IHp21 IHp22. reflexivity.
    - specialize (IHp (S n') m H).
      apply IHp.
    - specialize (IHp n' (S m) H). apply IHp.
  Qed.
    
  Record PatternCtx : Type :=
    { pcEvar : evar ;
      pcPattern : Pattern;
      pcPattern_wf : well_formed pcPattern ;
      pcOneOcc : count_evar_occurrences pcEvar pcPattern = 1  ;
    }.


  Definition emplace (ctx : PatternCtx) (p : Pattern) : Pattern :=
    free_evar_subst (pcPattern ctx) p (pcEvar ctx).

  
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

  Lemma wf_sctx (C : Application_context) (A : Pattern) :
    well_formed A -> well_formed (subst_ctx C A).
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
      unfold well_formed_closed. simpl.
      unfold well_formed_closed in IHC2. rewrite IHC2. simpl.
      fold (well_formed_closed p). rewrite Prf2.
      reflexivity.
    - unfold well_formed in *. simpl.
      apply andb_true_iff in Prf. destruct Prf as [Prf1 Prf2].
      rewrite Prf1. simpl.
      apply andb_true_iff in IHC. destruct IHC as [IHC1 IHC2].
      rewrite IHC1. simpl.
      unfold well_formed_closed in *. simpl.
      rewrite Prf2. simpl.
      rewrite IHC2. reflexivity.
  Qed.

  Lemma wp_sctx (C : Application_context) (A : Pattern) :
    well_formed_positive A -> well_formed_positive (subst_ctx C A).
  Proof.
    intros H.
    induction C.
    - auto.
    - simpl. rewrite IHC. simpl.
      unfold well_formed in Prf. apply andb_true_iff in Prf. destruct Prf. exact H0.
    - simpl. unfold well_formed in Prf. apply andb_true_iff in Prf.
      destruct Prf. rewrite H0. rewrite IHC. reflexivity.
  Qed.

  Lemma wc_sctx (C : Application_context) (A : Pattern) idx1 idx2 :
    well_formed_closed_aux A idx1 idx2 -> well_formed_closed_aux (subst_ctx C A) idx1 idx2.
  Proof.
    intros H.
    induction C.
    - auto.
    - simpl. rewrite IHC. simpl.
      unfold well_formed in Prf. apply andb_true_iff in Prf.
      destruct Prf. unfold well_formed_closed in H1.
      eapply well_formed_closed_aux_ind. 3: eassumption. all: lia.
    - simpl. rewrite IHC.
      unfold well_formed in Prf. apply andb_true_iff in Prf.
      destruct Prf. unfold well_formed_closed in H1.
      eapply (@well_formed_closed_aux_ind _ 0 idx1 0 idx2) in H1. 2,3: lia. rewrite H1. reflexivity.
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
    pcOneOcc := ApplicationContext2Pattern_one_occ pf
    |}.
  Next Obligation.
    intros boxvar AC H.
    apply wf_sctx.
    reflexivity.
  Defined.

  Definition ApplicationContext2PatternCtx (AC : Application_context) : PatternCtx :=
    let boxvar := (evar_fresh (elements (free_evars_ctx AC))) in
    @ApplicationContext2PatternCtx' boxvar AC (@set_evar_fresh_is_fresh' _).

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
                    | patt_free_evar x' => if decide (x' = x) then true else false
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
      if decide (count_evar_occurrences box_evar p1 = 0) then
        @ctx_app_r p1 (@PatternCtx2ApplicationContext' box_evar p2 (well_formed_app_2 wf)) (well_formed_app_1 wf)
      else if decide (count_evar_occurrences box_evar p2 = 0) then
             @ctx_app_l (@PatternCtx2ApplicationContext' box_evar p1 (well_formed_app_1 wf)) p2 (well_formed_app_2 wf)
           else
             box
    | _ => fun _ => box
    end
    ) wf
  .
  

  Definition PatternCtx2ApplicationContext (C : PatternCtx) : Application_context :=
    @PatternCtx2ApplicationContext' (pcEvar C) (pcPattern C) (pcPattern_wf C).

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
    PatternCtx2ApplicationContext' boxvar (pcPattern_wf C) = AC.
  Proof.
    simpl.
    move: (ApplicationContext2PatternCtx'_obligation_1 boxvar AC).
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
    PatternCtx2ApplicationContext (ApplicationContext2PatternCtx AC) = AC.
  Proof.
    unfold PatternCtx2ApplicationContext, ApplicationContext2PatternCtx.
    apply ApplicationContext2PatternCtx2ApplicationContext'.
  Qed.

  Fixpoint is_implicative_context' (box_evar : evar) (phi : Pattern) : bool :=
    match phi with
    | patt_bott => true
    | patt_free_evar _ => true
    | patt_imp phi1 phi2 =>
      (if decide(count_evar_occurrences box_evar phi1 <> 0)
       then is_implicative_context' box_evar phi1 else true) &&
      (if decide(count_evar_occurrences box_evar phi2 <> 0)
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

  Lemma bevar_subst_contains_subformula ϕ₁ ϕ₂ dbi :
    bevar_occur ϕ₁ dbi = true ->
    is_subformula_of_ind ϕ₂ (bevar_subst ϕ₁ ϕ₂ dbi).
  Proof.
    generalize dependent dbi.
    induction ϕ₁; intros dbi H; simpl; simpl in H; try inversion H.
    - case_bool_decide; destruct (compare_nat n dbi); try inversion H1.
      + lia.
      + constructor. reflexivity.
      + lia.
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
    1,2: (destruct (n=? dbi2); reflexivity).
  Qed.

  Lemma bsvar_occur_evar_open dbi1 dbi2 X phi:
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
    1,2: (destruct (n =? dbi2); reflexivity).
  Qed.

  Lemma bevar_occur_svar_open dbi1 dbi2 X phi:
    bevar_occur phi dbi1 = false ->
    bevar_occur (svar_open dbi2 X phi) dbi1 = false.
  Proof.
    apply Private_bevar_occur_svar_open with (sz := size phi). lia.
  Qed.

  Lemma Private_bevar_occur_evar_open sz dbi1 dbi2 X phi:
    size phi <= sz ->
    bevar_occur phi dbi1 = false ->
    bevar_occur (evar_open dbi2 X phi) dbi1 = false.
  Proof.
    move: phi dbi1 dbi2.
    induction sz; move=> phi; destruct phi; simpl; move=> dbi1 dbi2 Hsz H; try rewrite !IHsz; auto; try lia; try apply orb_false_elim in H; firstorder.
    1,2: (destruct (n=? dbi2); auto).
  Qed.

  Lemma bevar_occur_evar_open dbi1 dbi2 X phi:
    bevar_occur phi dbi1 = false ->
    bevar_occur (evar_open dbi2 X phi) dbi1 = false.
  Proof.
    apply Private_bevar_occur_evar_open with (sz := size phi). lia.
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

    Lemma free_svars_bevar_subst ϕ₁ ϕ₂ dbi:
    free_svars (bevar_subst ϕ₁ ϕ₂ dbi) ⊆ free_svars ϕ₁ ∪ free_svars ϕ₂.
  Proof.
    generalize dependent dbi.
    induction ϕ₁; intros db; simpl.
    - apply empty_subseteq.
    - apply union_subseteq_l.
    - destruct (compare_nat n db); simpl.
      + apply empty_subseteq.
      + apply union_subseteq_r.
      +  apply empty_subseteq.
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

  Lemma free_svars_bevar_subst_eq ϕ₁ ϕ₂ dbi:
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

  Lemma bevar_subst_not_occur_is_noop ϕ₁ ϕ₂ dbi:
    bevar_occur ϕ₁ dbi = false ->
    bevar_subst ϕ₁ ϕ₂ dbi = ϕ₁.
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
    intros H.
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
    induction phi; destruct psi; intros x' n' H H0 H1; try (simpl in H1; congruence); try (simpl in H1; destruct (n =? n') eqn:P; congruence); auto.
    - simpl in H1. destruct (n =? n') eqn:P.
      + inversion H1. subst. unfold evar_is_fresh_in in H. simpl in H. apply not_elem_of_singleton_1 in H.
        congruence.
      + congruence.
    - simpl in H1. destruct (n =? n') eqn:P.
      + inversion H1. subst. unfold evar_is_fresh_in in H0. simpl in H0. apply not_elem_of_singleton_1 in H0.
        congruence.
      + congruence.
    - simpl in H1. destruct (n =? n') eqn:P; destruct (n0 =? n') eqn:P2.
      + apply Nat.eqb_eq in P. apply Nat.eqb_eq in P2. subst. reflexivity.
      + congruence.
      + congruence.
      + inversion H1. reflexivity.
    - simpl in H1. destruct (n0 =? n') eqn:P.
      + inversion H1.
      + congruence.
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
    induction phi; destruct psi; intros X' n' H H0 H1; try (simpl in H1; congruence); try (simpl in H1; destruct (n =? n') eqn:P; congruence); auto.
    - simpl in H1. destruct (n =? n') eqn:P.
      + inversion H1. subst. unfold svar_is_fresh_in in H. simpl in H. apply not_elem_of_singleton_1 in H.
        congruence.
      + congruence.
    - inversion H1. destruct (n0 =? n') eqn:P.
      + inversion H3.
      + assumption.
    - simpl in H1. destruct (n =? n') eqn:P.
      + inversion H1. subst. unfold svar_is_fresh_in in H0. simpl in H0. apply not_elem_of_singleton_1 in H0.
        congruence.
      + congruence.
    - simpl in H1. destruct (n =? n') eqn:P; destruct (n0 =? n') eqn:P2.
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
    - simpl. destruct (ssrbool.is_left (decide (X = x))) eqn:P.
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
    intros phi psi fresh n X H H0 H1. apply Private_evar_open_free_svar_subst_comm with (sz := (size phi)); try lia; try assumption.
  Qed.

  Lemma Private_svar_open_free_svar_subst_comm : ∀ sz phi psi fresh n X,
      (le (size phi) sz) → (well_formed_closed psi) (* → well_formed_closed (svar_open n fresh phi)  *)→  
      svar_is_fresh_in fresh phi → svar_is_fresh_in fresh (free_svar_subst phi psi X) → (fresh ≠ X) 
      →
      (svar_open n fresh (free_svar_subst phi psi X)) = 
      (free_svar_subst (svar_open n fresh phi) psi X).
  Proof.
    induction sz; destruct phi; intros psi fresh n0 X Hsz Hwf (* Hwfc *) Hfresh1 Hfresh2 Hneq; try inversion Hsz; auto.
    - simpl. destruct (ssrbool.is_left (decide (X = x))) eqn:P.
      + rewrite -> svar_open_fresh. reflexivity. assumption.
      + simpl. reflexivity.
    - (* simpl in Hwfc. *) simpl. destruct (n =? n0) eqn:P.
      + simpl. destruct (decide (X = fresh)) eqn:D.
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
      simpl. remember (@evar_fresh (elements B)) as x.
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
      simpl. remember (@svar_fresh (elements B)) as X'.
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
    intros phi psi fresh n X H H0 H1 H2. apply (Private_svar_open_free_svar_subst_comm) with (sz := (size phi)); try lia; try assumption.
  Qed.

  Lemma free_evar_subst_preserves_no_negative_occurrence x p q n:
    well_formed q ->
    no_negative_occurrence_db_b n p ->
    no_negative_occurrence_db_b n (free_evar_subst p q x)
  with
  free_evar_subst_preserves_no_positive_occurrence x p q n:
    well_formed q ->
    no_positive_occurrence_db_b n p ->
    no_positive_occurrence_db_b n (free_evar_subst p q x)
  .
  Proof.
    - intros wfq nno.
      induction p; simpl; auto.
      + destruct (decide (x = x0)); simpl; auto.
        apply andb_prop in wfq. destruct wfq as [wfpq wfcq].
        apply wfc_impl_no_neg_occ. apply wfcq.
      + simpl in nno. apply andb_prop in nno. destruct nno as [nnop1 nnop2].
        rewrite IHp1. auto. rewrite IHp2. auto. reflexivity.
      + simpl in nno. apply andb_prop in nno. destruct nno as [nnop1 nnop2].
        rewrite IHp2. assumption. rewrite free_evar_subst_preserves_no_positive_occurrence; auto.
    - intros wfq npo.
      induction p; simpl; auto.
      + destruct (decide (x = x0)); simpl; auto.
        apply andb_prop in wfq. destruct wfq as [wfpq wfcq].
        apply wfc_impl_no_pos_occ. apply wfcq.
      + simpl in npo. apply andb_prop in npo. destruct npo as [npop1 npop2].
        rewrite IHp1. auto. rewrite IHp2. auto. reflexivity.
      + simpl in npo. apply andb_prop in npo. destruct npo as [npop1 npop2].
        rewrite IHp2. assumption. rewrite free_evar_subst_preserves_no_negative_occurrence; auto.
  Qed.
      

  Lemma Private_well_formed_free_evar_subst' x p q n1 n2:
    well_formed q ->
    well_formed_positive p && well_formed_closed_aux p n1 n2 ->
    no_negative_occurrence_db_b n2 (free_evar_subst p q x) && no_positive_occurrence_db_b n2 (free_evar_subst p q x) &&
    well_formed_positive (free_evar_subst p q x) && well_formed_closed_aux (free_evar_subst p q x) n1 n2 = true.
  Proof.
    intros wfq wfp.
    move: n1 n2 wfp.
    induction p; intros n1 n2 wfp; simpl; auto.
    - destruct (decide (x = x0)); simpl; auto.
      unfold well_formed in wfq. apply andb_prop in wfq. destruct wfq as [wfpq wfcq].
      rewrite wfpq. simpl in *.
      pose proof (H1 := @well_formed_closed_aux_ind q 0 0 0 n2 ltac:(lia) ltac:(lia) wfcq).
      pose proof (H2 := wfc_impl_no_neg_pos_occ H1).
      rewrite H2. simpl.
      eapply well_formed_closed_aux_ind.
      3: apply wfcq. all: lia.
    - simpl in *. rewrite wfp.
      rewrite !andbT.
      apply negb_true_iff. apply PeanoNat.Nat.eqb_neq.
      apply Nat.ltb_lt in wfp. lia.
    - unfold well_formed, well_formed_closed in *. simpl in *.
      apply andb_prop in wfp. destruct wfp as [wfpp wfcp].
      apply andb_prop in wfpp. destruct wfpp as [wfpp1 wfpp2].
      apply andb_prop in wfcp. destruct wfcp as [wfcp1 wfcp2].
      specialize (IHp1 n1 n2). specialize (IHp2 n1 n2).
      rewrite wfpp1 wfcp1 in IHp1.
      rewrite wfpp2 wfcp2 in IHp2.
      simpl in *.
      specialize (IHp1 ltac:(auto)).
      specialize (IHp2 ltac:(auto)).
      apply andb_prop in IHp1. destruct IHp1 as [IHp1 IHc1].
      apply andb_prop in IHp1. destruct IHp1 as [IHn1 IHp1].
      rewrite IHp1 IHc1. apply andb_prop in IHn1. destruct IHn1 as [IHn11 IHn12].
      rewrite IHn11 IHn12. simpl.
      apply andb_prop in IHp2. destruct IHp2 as [IHp2 IHc2].
      apply andb_prop in IHp2. destruct IHp2 as [IHn2 IHp2].
      rewrite IHp2 IHc2. apply andb_prop in IHn2. destruct IHn2 as [IHn21 IHn22].
      rewrite IHn21 IHn22.
      reflexivity.
    - unfold well_formed, well_formed_closed in *. simpl in *.
      apply andb_prop in wfp. destruct wfp as [wfpp wfcp].
      apply andb_prop in wfpp. destruct wfpp as [wfpp1 wfpp2].
      apply andb_prop in wfcp. destruct wfcp as [wfcp1 wfcp2].
      specialize (IHp1 n1 n2). specialize (IHp2 n1 n2).
      rewrite wfpp1 wfcp1 in IHp1.
      rewrite wfpp2 wfcp2 in IHp2.
      simpl in *.
      specialize (IHp1 ltac:(auto)).
      specialize (IHp2 ltac:(auto)).
      apply andb_prop in IHp1. destruct IHp1 as [IHp1 IHc1].
      apply andb_prop in IHp1. destruct IHp1 as [IHn1 IHp1].
      rewrite IHp1 IHc1. apply andb_prop in IHn1. destruct IHn1 as [IHn11 IHn12].
      rewrite IHn11 IHn12. simpl.
      apply andb_prop in IHp2. destruct IHp2 as [IHp2 IHc2].
      apply andb_prop in IHp2. destruct IHp2 as [IHn2 IHp2].
      rewrite IHp2 IHc2. apply andb_prop in IHn2. destruct IHn2 as [IHn21 IHn22].
      rewrite IHn21 IHn22.
      reflexivity.
    - simpl in wfp.
      unfold well_formed, well_formed_closed in *. simpl in *.
      apply andb_prop in wfp. destruct wfp as [wfpp wfcp].
      pose proof (IHp' := IHp).
      specialize (IHp n1 (S n2)).
      apply andb_prop in wfpp. destruct wfpp as [nnop wfpp].
      rewrite wfpp in IHp. simpl in IHp. rewrite wfcp in IHp.
      specialize (IHp ltac:(auto)).
      apply andb_prop in IHp. destruct IHp as [IHp IHc].
      apply andb_prop in IHp. destruct IHp as [IHn1 IHn2].
      apply andb_prop in IHn1. destruct IHn1 as [IHn11 IHn12].
      rewrite IHn12 IHn11. simpl. rewrite IHn2.
      rewrite IHc.
      rewrite free_evar_subst_preserves_no_negative_occurrence; auto.
  Qed.

  Lemma well_formed_free_evar_subst x p q:
    well_formed q ->
    well_formed p ->
    well_formed (free_evar_subst p q x).
  Proof.
    intros wfp wfq.
    pose proof (H := Private_well_formed_free_evar_subst' x wfp wfq).
    unfold well_formed, well_formed_closed.
    apply andb_prop in H. destruct H as [H H2]. rewrite H2. clear H2.
    apply andb_prop in H. destruct H as [H H2]. rewrite H2. reflexivity.
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


  Lemma well_formed_positive_bevar_subst φ : forall n ψ,
    mu_free φ ->
    well_formed_positive φ -> well_formed_positive ψ
  ->
    well_formed_positive (bevar_subst φ ψ n).
  Proof.
    induction φ; intros n' ψ H H0 H1; simpl; auto.
    2-3: apply andb_true_iff in H as [E1 E2];
         simpl in H0; apply eq_sym, andb_true_eq in H0; destruct H0; 
         rewrite -> IHφ1, -> IHφ2; auto.
    * break_match_goal; auto.
  Qed.

  Lemma mu_free_evar_open :
    forall φ, mu_free φ -> forall x n, mu_free (evar_open n x φ).
  Proof.
    induction φ; intros H x' n'; simpl; try now constructor.
    * break_match_goal; constructor.
    * simpl in H. apply andb_true_iff in H as [E1 E2]. now rewrite -> IHφ1, -> IHφ2.
    * simpl in H. apply andb_true_iff in H as [E1 E2]. now rewrite -> IHφ1, -> IHφ2.
    * simpl in H. now apply IHφ.
    * inversion H.
  Qed.

  Theorem evar_open_bevar_subst_same :
    forall x phi n, evar_open n x phi = bevar_subst phi (patt_free_evar x) n.
  Proof.
    induction phi; intros n'; auto; simpl.
    * break_match_goal.
      - apply Nat.eqb_eq in Heqb. subst. break_match_goal; auto; lia.
      - apply Nat.eqb_neq in Heqb. subst. break_match_goal; auto; lia.
    * rewrite -> IHphi1, -> IHphi2; auto.
    * rewrite -> IHphi1, -> IHphi2; auto.
    * rewrite -> IHphi; auto.
    * rewrite -> IHphi; auto.
  Qed.


  Theorem evar_open_free_evar_subst_swap :
    forall φ x n ψ y, x <> y -> well_formed ψ ->
      evar_open n x (free_evar_subst φ ψ y) = free_evar_subst (evar_open n x φ) ψ y.
  Proof.
    induction φ; intros x' n' ψ y H H0; cbn; auto.
    * destruct (decide (y = x)); simpl.
      - rewrite evar_open_wfc; auto. now apply andb_true_iff in H0.
      - reflexivity.
    * break_match_goal; simpl; auto. destruct (decide (y = x')); auto.
      congruence.
    * now rewrite -> IHφ1, -> IHφ2.
    * now rewrite -> IHφ1, -> IHφ2.
    * now rewrite IHφ.
    * now rewrite IHφ.
  Qed.

  Lemma free_evars_free_evar_subst : forall φ ψ x,
    free_evars (free_evar_subst φ ψ x) ⊆ free_evars φ ∪ free_evars ψ.
  Proof.
    induction φ; intros ψ x'; simpl.
    2-5, 7: apply empty_subseteq.
    * destruct (decide (x' = x)); simpl.
      - apply union_subseteq_r.
      - apply union_subseteq_l.
    * specialize (IHφ1 ψ x'). specialize (IHφ2 ψ x').
      set_solver.
    * specialize (IHφ1 ψ x'). specialize (IHφ2 ψ x').
      set_solver.
    * apply IHφ.
    * apply IHφ.
  Qed.

  Lemma bound_to_free_variable_subst :
    forall φ x m n n' ψ, m > n ->
      well_formed_closed_aux φ m n' -> x ∉ free_evars φ
    ->
      bevar_subst φ ψ n = free_evar_subst (evar_open n x φ) ψ x.
  Proof.
    induction φ; intros x' m n' n'' ψ H H0 H1; cbn; auto.
    * destruct (decide (x' = x)); simpl.
      - simpl in H1. apply not_elem_of_singleton_1 in H1. congruence.
      - reflexivity.
    * destruct (extralibrary.compare_nat n n').
      - assert (n =? n' = false). { apply Nat.eqb_neq. lia. } now rewrite H2.
      - subst. rewrite Nat.eqb_refl. simpl. destruct (decide (x' = x')); auto. congruence.
      - assert (n =? n' = false). { apply Nat.eqb_neq. lia. } now rewrite H2.
    * simpl in H1. apply not_elem_of_union in H1. destruct H1. simpl in H0.
      apply andb_true_iff in H0. destruct H0.
      erewrite -> IHφ1, -> IHφ2. reflexivity. all: eassumption.
    * simpl in H1. apply not_elem_of_union in H1. destruct H1. simpl in H0.
      apply andb_true_iff in H0. destruct H0.
      erewrite -> IHφ1, -> IHφ2. reflexivity. all: eassumption.
    * simpl in H0, H1. erewrite IHφ. reflexivity. instantiate (1 := S m). 
      all: try eassumption. lia.
    * simpl in H0, H1. erewrite IHφ. reflexivity. all: eassumption.
  Qed.

  Lemma evar_open_no_negative_occurrence :
    forall φ db1 db2 x,
      (no_negative_occurrence_db_b db1 (evar_open db2 x φ) ->
      no_negative_occurrence_db_b db1 φ) /\
      (no_positive_occurrence_db_b db1 (evar_open db2 x φ) ->
      no_positive_occurrence_db_b db1 φ).
  Proof.
    induction φ; intros db1 db2 x'; cbn; auto.
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
  Qed.

  Lemma evar_open_positive : forall φ n x,
    well_formed_positive (evar_open n x φ) ->
    well_formed_positive φ.
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

  Lemma wf_body_ex_to_wf :
    forall φ, wf_body_ex φ -> well_formed (patt_exists φ).
  Proof.
    intros φ H. unfold well_formed, well_formed_closed. simpl.
    remember (fresh_evar φ) as x.
    assert (x ∉ free_evars φ) by now apply x_eq_fresh_impl_x_notin_free_evars.
    specialize (H x H0).
    apply andb_true_iff in H. destruct H.
    apply evar_open_positive in H.
    apply wfc_aux_body_ex_imp2 in H1.
    now rewrite -> H, -> H1.
  Qed.

  Lemma bevar_subst_closed :
    forall φ ψ n m,
    well_formed_closed_aux φ (S n) m ->
    well_formed_closed_aux ψ n m
    ->
    well_formed_closed_aux (bevar_subst φ ψ n) n m.
  Proof.
    induction φ; intros ψ n' m H H0; cbn; auto.
    * break_match_goal; simpl in H0, H; simpl; auto.
      all: apply Nat.ltb_lt. auto. apply Nat.ltb_lt in H. lia.
    * simpl in H. apply andb_true_iff in H as [E1 E2]. erewrite IHφ1, IHφ2; auto.
    * simpl in H. apply andb_true_iff in H as [E1 E2]. erewrite IHφ1, IHφ2; auto.
    * simpl in H. rewrite -> IHφ; auto. eapply wfc_aux_extend.
      eassumption. lia. lia.
    * simpl in H. rewrite -> IHφ; auto. eapply wfc_aux_extend.
      eassumption. lia. lia.
  Qed.

  Lemma bevar_subst_positive :
    forall φ ψ n, mu_free φ ->
    well_formed_positive φ -> well_formed_positive ψ
   ->
    well_formed_positive (bevar_subst φ ψ n).
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

  Lemma free_evars_bevar_subst :
    forall φ ψ n,
    free_evars (bevar_subst φ ψ n) ⊆ free_evars φ ∪ free_evars ψ.
  Proof.
    induction φ; intros ψ n'; simpl; auto.
    * apply union_subseteq_l.
    * apply empty_subseteq.
    * destruct (extralibrary.compare_nat n n'); simpl.
      - apply empty_subseteq.
      - apply union_subseteq_r.
      - apply empty_subseteq.
    * apply empty_subseteq.
    * apply empty_subseteq.
    * specialize (IHφ1 ψ n'). specialize (IHφ2 ψ n').
      set_solver.
    * apply empty_subseteq.
    * specialize (IHφ1 ψ n'). specialize (IHφ2 ψ n').
      set_solver.
  Qed.

  Theorem evar_quantify_closed :
    forall φ x n m, well_formed_closed_aux φ n m ->
    well_formed_closed_aux (evar_quantify x n φ) (S n) m.
  Proof.
    induction φ; intros x' n' m H; cbn; auto.
    * destruct (decide (x' = x)); simpl; auto. apply Nat.ltb_lt. lia.
    * simpl in H. apply Nat.leb_le. apply Nat.ltb_lt in H. lia.
    * simpl in H. apply andb_true_iff in H as [E1 E2]. now rewrite -> IHφ1, -> IHφ2.
    * simpl in H. apply andb_true_iff in H as [E1 E2]. now rewrite -> IHφ1, -> IHφ2. 
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
    well_formed_positive (evar_quantify x n φ).
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
      well_formed (patt_exists (evar_quantify x 0 φ)).
  Proof.
    intros φ x H.
    unfold well_formed, well_formed_closed.
    apply andb_true_iff in H as [E1 E2]. simpl.
    now erewrite -> evar_quantify_closed, -> evar_quantify_positive.
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
    well_formed (subst_patctx C φ).
  Proof.
    induction C; intros φ WFC WFφ; simpl; auto.
    * apply andb_true_iff in WFC as [E1 E2]. apply well_formed_app; auto.
    * apply andb_true_iff in WFC as [E1 E2]. apply well_formed_app; auto.
    * apply andb_true_iff in WFC as [E1 E2]. apply well_formed_app; auto.
    * apply andb_true_iff in WFC as [E1 E2]. apply well_formed_app; auto.
    * simpl in WFC. eapply IHC in WFC; eauto.
      now apply evar_quantify_well_formed.
  Qed.

    Lemma evar_quantify_free_evar_subst :
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
  Notation "⊥" := patt_bott : ml_scope.
  Notation "a ---> b"  := (patt_imp a b) (at level 90, right associativity,
                                          b at level 200) : ml_scope.
  Notation "'ex' , phi" := (patt_exists phi) (at level 70) : ml_scope.
  Notation "'mu' , phi" := (patt_mu phi) (at level 70) : ml_scope.

  (*Notation "AC [ p ]" := (subst_ctx AC p) (at level 90) : ml_scope.*)
  Notation "C [ p ]" := (emplace C p) (at level 90) : ml_scope.

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

(* Tactics for resolving goals involving sets *)

Tactic Notation "solve_free_evars_inclusion" int_or_var(depth) :=
  simpl;
  (do ? [rewrite simpl_free_evars/=]) ;
  solve_set_inclusion depth.

Tactic Notation "solve_free_svars_inclusion" int_or_var(depth) :=
  simpl;
  (do ? [rewrite simpl_free_svars/=]) ;
  solve_set_inclusion depth.
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
