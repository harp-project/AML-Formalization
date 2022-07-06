From MatchingLogic Require Export Logic 
                                  Theories.Definedness_Syntax
                                  Theories.Definedness_ProofSystem
                                  DerivedOperators_Syntax
                                  Theories.Sorts_Syntax
                                  Theories.Sorts_ProofSystem
                                  NamedAxioms
                                  ProofMode
                                  wftactics
                                  .
Import MatchingLogic.Syntax.Notations MatchingLogic.DerivedOperators_Syntax.Notations.
From Coq Require Import ssreflect ssrfun ssrbool.
Require Export Coq.Program.Wf 
               Lia 
               FunctionalExtensionality
               Logic.PropExtensionality
               Program.Equality.
From stdpp Require Import countable finite sets.
From MatchingLogic Require Export Utils.extralibrary.
Require Export Vector PeanoNat String Arith.Lt.

Ltac separate :=
match goal with
| [H : is_true (andb _ _) |- _] => apply andb_true_iff in H as [?E1 ?E2]
| |- is_true (andb _ _) => apply andb_true_iff
end.

Definition vec {A : Set} := @t A.

Lemma Forall_map (T : Set) n (l : vec n) : forall (P : T -> Prop) (f : T -> T),
  (forall x, P x -> P (f x))
->
  Forall P l -> Forall P (map f l).
Proof.
  induction l; intros P f H; constructor;
  inversion H0; subst. auto.
  apply IHl; auto. simpl_existT. subst. auto.
Qed.

Theorem fold_left_map  (T Q : Set) n (v : vec n) :
   forall (App : Q -> T -> Q) (start : Q) f,
  fold_left App start (map f v) = @fold_left T Q (fun Acc x => App Acc (f x)) start _ v.
Proof.
  induction v; intros App start f; simpl; auto.
Qed.

Lemma map_Forall (T : Set) n (l : vec n) : forall (P : T -> Prop) (f : T -> T),
  (forall x, P (f x) -> P x)
->
  Forall P (map f l) -> Forall P l.
Proof.
  induction l; intros P f H; constructor;
  inversion H0; subst. auto.
  eapply IHl; eauto. simpl_existT. now subst.
Qed.

Lemma Forall_map_ext (T : Set) n (l : vec n) : forall (P : T -> Prop) (f : T -> T),
  (forall x, In x l -> P x -> P (f x))
->
  Forall P l -> Forall P (map f l).
Proof.
  induction l; intros P f H; constructor;
  inversion H0; subst. auto. apply H. constructor. auto.
  apply IHl; auto. intros x H1 H2. apply H. constructor 2. auto. auto. simpl_existT. now subst.
Qed.

Lemma map_Forall_ext (T : Set) n (l : vec n) : forall (P : T -> Prop) (f : T -> T),
  (forall x, In x l -> P (f x) -> P x)
->
  Forall P (map f l) -> Forall P l.
Proof.
  induction l; intros P f H; constructor;
  inversion H0; subst. auto. apply H. constructor; auto. auto.
  eapply IHl; auto. intros x H1 H2. apply H. constructor 2. auto. exact H2. simpl_existT.
  now subst.
Qed.

Lemma Forall_impl_ext  (A : Set) (P Q : A → Prop) n (l : vec n) :
   (∀ a : A, In a l -> P a → Q a) → Forall P l → Forall Q l.
Proof.
  induction l; intros H H0; constructor; inversion H0; subst.
  apply H. constructor; auto. auto.
  apply IHl; auto. intros a H1 H2. apply H; auto. constructor 2. auto.
  simpl_existT. now subst.
Qed.

Global Hint Constructors Forall : core.

Class funcs_signature :=
  { funs : Set; funs_eqdec : EqDecision funs; ar_funs : funs -> nat }.

Coercion funs : funcs_signature >-> Sortclass.

Class preds_signature :=
  { preds : Set; preds_eqdec : EqDecision preds; ar_preds : preds -> nat }.

Class FOL_variables :=
  {
    vars : Set;
    var_eqdec :> EqDecision vars;
    var_countable :> Countable vars;
    var_infinite :> Infinite vars;
  }.

Coercion preds : preds_signature >-> Sortclass.

Section fix_signature.

  Context {Σ_vars : FOL_variables}.
  Context {Σ_funcs : funcs_signature}.
  
  Definition var_fresh (l : list vars) : vars := @infinite_fresh _ var_infinite l.

  Unset Elimination Schemes.
  Inductive term  : Set :=
  | bvar : nat -> term
  | fvar : vars -> term
  | func : forall (f : funs), @vec term (ar_funs f) -> term.
  Set Elimination Schemes.

  Fixpoint fsubst_term (t0 t : term) (n : vars) : term :=
  match t0 with
  | fvar t' => if decide (t' = n) is left _ then t else t0
  | bvar _ => t0
  | func f v => func f (map (fun x => fsubst_term x t n) v)
  end.

  Fixpoint bsubst_term (t0 t : term) (n : nat) : term :=
  match t0 with
  | bvar t' => match compare_nat t' n with
               | Nat_less _ _ _ => bvar t'
               | Nat_equal _ _ _ => t
               | Nat_greater _ _ _ => bvar (pred t')
               end
  | fvar _ => t0
  | func f v => func f (map (fun x => bsubst_term x t n) v)
  end.

  Context {Σ_preds : preds_signature}.

  Inductive form  : Type :=
  | fal : form
  | atom : forall (P : preds), @vec term (ar_preds P) -> form
  | impl : form  -> form  -> form
  | exs : form  -> form.

  Fixpoint fsubst_form (phi : form) (t : term) (n: vars) : form :=
    match phi with
    | fal => fal
    | atom P v => atom P (map (fun x => fsubst_term x t n) v)
    | impl phi1 phi2 => impl (fsubst_form phi1 t n) (fsubst_form phi2 t n)
    | exs phi => exs (fsubst_form phi t n)
    end.

  Fixpoint bsubst_form (phi : form) (t : term) (n: nat) : form :=
    match phi with
    | fal => fal
    | atom P v => atom P (map (fun x => bsubst_term x t n) v)
    | impl phi1 phi2 => impl (bsubst_form phi1 t n) (bsubst_form phi2 t n)
    | exs phi => exs (bsubst_form phi t (S n))
    end.

  Inductive ForallT {A : Set} (P : A -> Type) : forall {n}, vec n -> Type :=
  | ForallT_nil : ForallT P (nil)
  | ForallT_cons : forall n (x : A) (l : vec n), P x -> ForallT P l -> ForallT P (@cons A x n l).

  Inductive vec_in {A : Set} (a : A) : forall {n}, vec n -> Type :=
  | vec_inB {n} (v : vec n) : vec_in a (@cons _ a n v)
  | vec_inS a' {n} (v : vec n) : vec_in a v -> vec_in a (@cons _ a' n v).
  Hint Constructors vec_in : core.
  
  Lemma term_rect' (p : term -> Set) :
    (forall x, p (fvar x)) ->
    (forall x, p (bvar x)) -> 
    (forall F v, (ForallT p v) -> p (func F v)) -> forall (t : term), p t.
  Proof.
    intros f1 f2 f3. fix strong_term_ind' 1. destruct t as [n|n|F v].
    - apply f2.
    - apply f1.
    - apply f3. induction v.
      + econstructor.
      + econstructor. now eapply strong_term_ind'. eauto.
  Qed.

  Lemma term_rect (p : term -> Set) :
    (forall x, p (fvar x)) -> (forall x, p (bvar x)) -> (forall F v, (forall t, vec_in t v -> p t) -> p (func F v)) -> forall (t : term), p t.
  Proof.
    intros f1 f2 f3. eapply term_rect'.
    - apply f1.
    - apply f2.
    - intros F v H. apply f3. intros t. induction 1; inversion H; subst; eauto.
      apply Eqdep_dec.inj_pair2_eq_dec in H4; subst; eauto. decide equality.
  Qed.

  Lemma term_ind (p : term -> Prop) :
    (forall x, p (fvar x)) -> (forall x, p (bvar x)) -> (forall F v (IH : forall t, In t v -> p t), p (func F v)) -> forall (t : term), p t.
  Proof.
    intros f1 f2 f3. eapply term_rect'.
    - apply f1.
    - apply f2.
    - intros F v H. apply f3. intros t. induction 1; inversion H; subst; eauto.
      apply Eqdep_dec.inj_pair2_eq_dec in H4; subst; eauto. decide equality.
  Qed.

  Fixpoint wf_term (t : term) (n : nat) : bool :=
  match t with
   | bvar x => if decide (x < n) is left _ then true else false
   | fvar x => true
   | func f x => fold_right (fun t Acc => andb Acc (wf_term t n)) x true
  end.

  Fixpoint wf_form (F : form) (n : nat) : bool :=
  match F with
   | fal => true
   | atom P x => fold_right (fun t Acc => andb Acc (wf_term t n)) x true
   | impl x x0 => wf_form x n && wf_form x0 n
   | exs x => wf_form x (S n)
  end.

  Theorem wf_increase_term :
    forall t n, wf_term t n -> forall n', n' >= n -> wf_term t n'.
  Proof.
    induction t; intros n H n' H0; auto.
    * simpl in *. repeat case_match; auto. lia.
    * simpl in *. induction v; auto; simpl.
      simpl in H. do 2 separate.
      erewrite IH. split; auto. apply IHv; auto.
      - intros t H n1 H1 n'0 H2. eapply IH. now constructor. exact H1. auto.
      - constructor.
      - exact E2.
      - auto.
  Qed.

  Theorem wf_increase :
    forall φ n, wf_form φ n -> forall n', n' >= n -> wf_form φ n'.
  Proof.
    induction φ; intros n H n' H0; auto.
    * simpl in *. induction v; auto; simpl.
      simpl in H. do 2 separate.
      erewrite wf_increase_term. split; auto. apply IHv; auto.
      - eapply wf_increase_term. exact E2. auto.
      - auto.
    * simpl in *. apply andb_true_iff in H as [E1 E2].
      erewrite IHφ1, IHφ2; [ auto | | | |]; eassumption.
    * simpl in *. erewrite IHφ. 2: exact H. auto. lia.
  Qed.

  Theorem wf_term_subst :
    forall b t n, wf_term b (S n) -> wf_term t n ->
      wf_term (bsubst_term b t n) n.
  Proof.
    induction b; intros t n H H0; subst.
    * reflexivity.
    * simpl. repeat case_match; auto; simpl; case_match; auto. simpl in H. case_match. lia. congruence.
    * simpl in *; induction v; simpl in *; auto.
      do 2 separate. rewrite IH; auto. constructor. split; auto.
      apply IHv; auto. intros t0 H. apply IH. now constructor 2.
  Qed.

  Theorem wf_form_subst :
    forall φ t n, wf_form φ (S n) -> wf_term t n ->
      wf_form (bsubst_form φ t n) n.
  Proof.
    induction φ; intros t n H H0; simpl; auto.
    * simpl in *; induction v; simpl in *; auto. do 2 separate.
      rewrite wf_term_subst; auto. split; auto.
      apply IHv; auto.
    * simpl in H. separate. rewrite IHφ1; auto. rewrite IHφ2; auto.
    * simpl in H. subst. apply IHφ; auto. eapply wf_increase_term. exact H0.
      lia.
  Qed.

End fix_signature.

Section semantics.
  Context {Σ_vars : FOL_variables}.
  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.
  Variable domain : Set.

  Class interp := B_I
    {
      i_f : forall f : funs, @vec domain (ar_funs f) -> domain ;
      i_P : forall P : preds, @vec domain (ar_preds P) -> bool ; (* for decidability *)
    }.
    Context {I : interp }.
    Definition env := vars -> domain. (* for free vars *)
    Variable failure : domain. (* for wrong evaluation!!! *)

    Fixpoint mmap {A B : Type} (f : A -> option B) {n : nat} (v : t A n) : 
      option (t B n) :=
    match v in (t _ n0) return (option (t B n0)) with
    | nil => Some nil
    | @cons _ a n0 v' => match f a with
                         | None => None
                         | Some x => match mmap f v' with
                                     | None => None
                                     | Some xs => Some (cons x xs)
                                     end
                         end
    end.

    Fixpoint eval (rho : env) (t : term) : domain :=
    match t with
    | fvar s => rho s
    | bvar s => failure (* for wf terms, this is never used *)
    | func f v => i_f f (Vector.map (eval rho) v)
    end.

    Definition update_env (ρ : env) (x : vars) (d : domain) : env :=
      fun v => if decide (v = x) then d else ρ v.

    Import List.
    Import ListNotations.

    Fixpoint term_vars (t : term) : list vars :=
    match t with
     | bvar x => []
     | fvar x => [x]
     | func f x => Vector.fold_right (fun t Acc => term_vars t ++ Acc) x []
    end.

    Fixpoint form_vars (f : form) : list vars :=
    match f with
     | fal => []
     | atom P x => Vector.fold_right (fun t Acc => term_vars t ++ Acc) x []
     | impl x x0 => form_vars x ++ form_vars x0
     | exs x => form_vars x
    end.

    Fixpoint form_size (f : form) : nat :=
    match f with
     | fal => 0
     | atom P x => 0
     | impl x x0 => S (form_size x + form_size x0)
     | exs x => S (form_size x)
    end.

    Theorem subst_var_size :
      forall f x y, form_size f = form_size (bsubst_form f (fvar x) y).
    Proof.
      induction f; intros x y; auto; simpl.
      - now rewrite -> (IHf1 x y), -> (IHf2 x y).
      - now rewrite -> (IHf x (S y)).
    Qed.

    Program Fixpoint sat (rho : env) (phi : form) {measure (form_size phi)} : Prop :=
    match phi with
    | atom P v => i_P P (Vector.map (eval rho) v) = true
    | fal => False
    | impl phi psi => sat rho phi -> sat rho psi
    | exs phi => let x := var_fresh (form_vars phi) in
      exists d : domain, sat (update_env rho x d) (bsubst_form phi (fvar x) 0)
    end.
    Next Obligation. intros. subst. simpl; lia. Defined.
    Next Obligation. intros. subst. simpl; lia. Defined.
    Next Obligation. intros. subst. simpl. rewrite <- subst_var_size. lia. Defined.
    Next Obligation. Tactics.program_simpl. Defined.

    Proposition sat_atom : forall ρ P v, sat ρ (atom P v) = 
                                            (i_P P (Vector.map (eval ρ) v) = true).
    Proof. reflexivity. Qed.
    Proposition sat_fal : forall ρ, sat ρ fal = False.
    Proof. reflexivity. Qed.
    Proposition sat_impl : forall ρ φ₁ φ₂, sat ρ (impl φ₁ φ₂) = 
                                            (sat ρ φ₁ -> sat ρ φ₂).
    Proof.
      intros ρ φ₁ φ₂. unfold sat, sat_func.
      rewrite fix_sub_eq.
      Tactics.program_simpl. unfold projT1, projT2.
      destruct X; auto with f_equal.
      { f_equal. apply propositional_extensionality.
        epose proof (H _). epose proof (H _).
        apply ZifyClasses.eq_iff in H0. apply ZifyClasses.eq_iff in H1. split; intros.
        - eapply H0 in H2. exact H2. apply H1. auto.
        - eapply H0 in H2. exact H2. apply H1. auto. 
      }
      { f_equal. apply functional_extensionality; auto. }
      { f_equal. }
    Qed.
    Proposition sat_exs : forall ρ φ, sat ρ (exs φ) = 
                        (let x := var_fresh (form_vars φ) in
      exists d : domain, sat (update_env ρ x d) (bsubst_form φ (fvar x) 0)).
    Proof.
      intros ρ φ. unfold sat, sat_func.
      rewrite fix_sub_eq.
      Tactics.program_simpl. unfold projT1, projT2.
      destruct X; auto with f_equal.
      { f_equal. apply propositional_extensionality.
        epose proof (H _). epose proof (H _).
        apply ZifyClasses.eq_iff in H0. apply ZifyClasses.eq_iff in H1. split; intros.
        - eapply H0 in H2. exact H2. apply H1. auto.
        - eapply H0 in H2. exact H2. apply H1. auto. 
      }
      { f_equal. apply functional_extensionality; auto. }
      { f_equal. }
    Qed.

    Notation "rho ⊨ phi" := (sat rho phi) (at level 20).

  Theorem sat_dec : forall sz φ, form_size φ <= sz -> forall ρ, {ρ ⊨ φ} + {~ ρ ⊨ φ}.
  Proof.
    induction sz; intros φ H; destruct φ; simpl in H; try lia; intros ρ.
    * right. auto.
    * rewrite sat_atom. apply bool_dec.
    * right. auto.
    * rewrite sat_atom. apply bool_dec.
    * destruct (IHsz φ1 ltac:(lia) ρ), (IHsz φ2 ltac:(lia) ρ).
      1, 3-4: left; rewrite sat_impl; intros; auto.
      congruence.
      right. rewrite sat_impl. intros. auto.
    * rewrite sat_exs. simpl.
      epose proof (IHsz (bsubst_form φ (fvar (var_fresh (form_vars φ))) 0) _).
      admit. (* TODO: not trivial, maybe using size based induction *)
  Abort.

End semantics.

Section proof_system.
  Context {Σ_vars : FOL_variables}.
  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.

  Fixpoint quantify_term (t : term) (v : vars) (n : nat) : term :=
  match t with
   | bvar x => bvar x
   | fvar x => if decide (v = x) then bvar n else fvar x
   | func f x => func f (Vector.map (fun t => quantify_term t v n) x)
  end.


  Fixpoint quantify_form (φ : form) (v : vars) (n : nat) : form :=
  match φ with
   | fal => fal
   | atom P x => atom P (Vector.map (fun t => quantify_term t v n) x)
   | impl x x0 => impl (quantify_form x v n) (quantify_form x0 v n)
   | exs x => exs (quantify_form x v (S n))
  end.


  Reserved Notation "Γ ⊢_FOL form" (at level 50).
  Inductive Hilbert_proof_sys (Γ : (list form)): form -> Set :=
  | AX (φ : form)             : wf_form φ 0 -> List.In φ Γ -> Γ ⊢_FOL φ
  | P1F (φ ψ : form)          : wf_form φ 0 -> wf_form ψ 0 -> Γ ⊢_FOL impl φ (impl ψ φ)
  | P2F (φ ψ ξ : form)        : wf_form φ 0 -> wf_form ψ 0 -> wf_form ξ 0 ->
    Γ ⊢_FOL impl (impl φ (impl ψ ξ)) (impl (impl φ ψ) (impl φ  ξ))
  | P3F (φ : form)            : wf_form φ 0 ->
    Γ ⊢_FOL impl (impl (impl φ fal) fal) φ
  | MPF (φ1 φ2 : form)        : wf_form φ1 0 -> wf_form (impl φ1 φ2) 0 ->
    Γ ⊢_FOL φ1 -> Γ ⊢_FOL impl φ1 φ2 -> Γ ⊢_FOL φ2
  | Q5F (φ : form) (t : term) :
    wf_form (exs φ) 0 -> wf_term t 0 ->
    Γ ⊢_FOL impl (bsubst_form φ t 0) (exs φ)
  | Q6F (φ ψ : form)(x : vars) : 
    wf_form φ 0 -> wf_form ψ 0 -> Γ ⊢_FOL impl φ ψ ->
    ~List.In x (form_vars ψ)
  ->
    Γ ⊢_FOL impl (exs (quantify_form φ x 0)) ψ
  where "Γ ⊢_FOL form" := (Hilbert_proof_sys Γ form).

End proof_system.

Section soundness_completeness.
  Context {Σ_vars : FOL_variables}.
  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.
  Notation "rho ⊨_FOL phi" := (sat _ _ _ rho phi) (at level 50).
  Notation "Γ ⊢_FOL form" := (Hilbert_proof_sys Γ form) (at level 50).

  Definition valid A phi :=
    forall (D : Set) (fail : D) (I : interp D) (rho : vars -> D),
    (forall Phi rho', List.In Phi A -> sat D fail rho' Phi)
      -> sat D fail rho phi.

  Theorem plugging_terms :
    forall t0 t D (I : interp D) fail rho x dbi,
    ~List.In x (term_vars t0) ->
    eval D fail rho (bsubst_term t0 t dbi) =
    eval D fail (update_env D rho x (eval D fail rho t)) (bsubst_term t0 (fvar x) dbi).
  Proof.
    induction t0; intros t D I fail rho x0 dbi Fresh; simpl.
    * unfold update_env. destruct decide; simpl in *; subst; auto. intuition.
    * case_match; simpl; auto.
      subst. unfold update_env. destruct decide; simpl; auto. congruence.
    * do 2 rewrite map_map. f_equal.
      apply map_ext_in. intros. apply IH. exact H.
      simpl in *.
      clear IH. induction v. inversion H.
      inversion H; subst.
      - simpl_existT. subst. simpl in Fresh.
        now apply notin_app_l in Fresh.
      - simpl_existT. subst. simpl in Fresh.
        apply notin_app_r in Fresh. apply IHv; intros; auto.
  Qed.

  Lemma update_env_comm :
    forall D x y d1 d2 rho, x <> y ->
      (update_env D (update_env D rho x d1) y d2) =
      (update_env D (update_env D rho y d2) x d1).
  Proof.
     intros. extensionality z.
     unfold update_env. repeat destruct decide; simpl; auto. congruence.
  Qed.

  Lemma wf_elements :
    forall (T : Set) (P : T -> bool) n (v : @vec T n),
      is_true (fold_right (λ t Acc, Acc && P t) v true) ->
      forall (e : T), In e v -> is_true (P e).
  Proof.
    induction v; intros H e HIn; inversion HIn; simpl_existT; subst.
    * simpl in H. apply andb_true_iff in H. apply H.
    * apply IHv; auto. apply andb_true_iff in H. apply H.
  Qed.

  Lemma bsubst_term_wf :
    forall t0 t n m, wf_term t0 m -> m <= n -> bsubst_term t0 t n = t0.
  Proof.
    induction t0; intros t n m Wf Le; simpl; auto.
    * repeat case_match; subst; simpl in Wf; auto; case_match; try lia; congruence.
    * erewrite map_ext_in with (g := id). now rewrite VectorSpec.map_id.
      intros. eapply IH in H; eauto. simpl in Wf. eapply wf_elements in Wf. exact Wf.
      auto.
  Qed.

  Lemma bsubst_form_wf :
    forall φ t n m, wf_form φ m -> m <= n -> bsubst_form φ t n = φ.
  Proof.
    induction φ; intros t n m Wf Le; simpl; auto.
    * erewrite map_ext_in with (g := id). now rewrite VectorSpec.map_id.
      intros. eapply bsubst_term_wf. simpl in Wf. eapply wf_elements in Wf. exact Wf.
      auto. auto.
    * simpl in Wf. apply andb_true_iff in Wf. erewrite IHφ1, IHφ2; auto;
      eapply wf_increase; try apply Wf; auto.
    * erewrite IHφ; auto. simpl in Wf. eapply wf_increase. exact Wf. lia.
  Qed.

  Lemma bsubst_term_comm_lower:
    forall t0 t1 t2 n m,
    n <= m
    → wf_term t1 0
      → wf_term t2 0
        → bsubst_term (bsubst_term t0 t1 n) t2 m =
          bsubst_term (bsubst_term t0 t2 (S m)) t1 n.
  Proof.
    induction t0; intros t1 t2 n m Hlt Wf1 Wf2; simpl; auto.
    * repeat case_match; simpl; try rewrite -> Heqc; try rewrite -> Heqc0; auto;
        subst; try congruence.
      all:  repeat case_match; try lia; auto.
      1-2: erewrite bsubst_term_wf; eauto; lia.
    * simpl. do 2 rewrite map_map. f_equal. apply map_ext_in.
      intros. eapply IH in H; eauto.
  Qed.

  Lemma bsubst_form_comm_lower:
    forall φ t1 t2 n m,
    n <= m
    → wf_term t1 0
      → wf_term t2 0
        → bsubst_form (bsubst_form φ t1 n) t2 m =
          bsubst_form (bsubst_form φ t2 (S m)) t1 n.
  Proof.
    induction φ; intros t1 t2 n m Hlt Wf1 Wf2; simpl; auto.
    * simpl. do 2 rewrite map_map. f_equal. apply map_ext_in.
      intros. eapply bsubst_term_comm_lower; eauto.
    * erewrite IHφ1, IHφ2; eauto.
    * erewrite IHφ; eauto. lia.
  Qed.

  Theorem fresh_irrelevant_term :
    forall (t : term) D fail (I : interp D) rho d x, ~List.In x (term_vars t) ->
      eval D fail (update_env D rho x d) t = eval D fail rho t.
  Proof.
    induction t; intros D fail I rho d x0 HNIn; simpl; auto.
    * unfold update_env. simpl in HNIn. destruct decide; simpl; auto.
      exfalso. apply HNIn; auto.
    * f_equal. apply VectorSpec.map_ext_in. intros.
      apply IH; auto. simpl in *.
      clear IH.
      induction v; inversion H; simpl_existT; subst.
      - simpl in HNIn. now apply notin_app_l in HNIn.
      - apply IHv; auto. now apply notin_app_r in HNIn.
  Qed.

  Theorem fresh_irrelevant_form :
    forall (φ : form) D fail (I : interp D) rho d x, ~List.In x (form_vars φ) ->
      sat D fail (update_env D rho x d) φ <-> sat D fail rho φ.
  Proof.
    induction φ; intros D fail I rho d x0 HNIn; simpl; auto.
    * do 2 rewrite sat_atom. erewrite VectorSpec.map_ext_in. reflexivity.
      intros. apply fresh_irrelevant_term. simpl in HNIn.
      induction v; inversion H; simpl_existT; subst.
      - simpl in HNIn. now apply notin_app_l in HNIn.
      - apply IHv; auto. now apply notin_app_r in HNIn.
    * do 2 rewrite sat_impl. apply notin_app_r in HNIn as HNIn2. apply notin_app_l in HNIn.
      now rewrite -> IHφ1, -> IHφ2.
    * do 2 rewrite sat_exs. simpl.
      split; intros H; destruct H as [d0 H]; exists d0.
      - rewrite update_env_comm in H.
        { admit. }
        specialize (IHφ D fail I (update_env D rho (var_fresh (form_vars φ)) d0) 
                        d x0 HNIn).
        destruct IHφ.
        (* TODO: use size-based induction here! *)
  (* Admitted. *)
  Abort.

  Theorem plugging_forms :
    forall φ t D (I : interp D) fail rho x dbi,
    ~List.In x (form_vars φ) ->
    sat D fail rho (bsubst_form φ t dbi) <->
    sat D fail (update_env D rho x (eval D fail rho t)) (bsubst_form φ (fvar x) dbi).
  Proof.
    induction φ; intros t D I fail rho x dbi Fresh; simpl in *.
    * split; intro Sat; now rewrite sat_fal in Sat.
    * split; intro Sat;
      rewrite sat_atom in Sat; rewrite sat_atom;
      rewrite map_map in Sat; rewrite map_map.
      - erewrite map_ext_in. exact Sat. intros. simpl.
        symmetry. apply plugging_terms.
        clear Sat.
        induction v. inversion H.
        inversion H; subst.
        + simpl_existT. subst. simpl in Fresh.
          now apply notin_app_l in Fresh.
        + simpl_existT. subst. simpl in Fresh.
          apply notin_app_r in Fresh. apply IHv; intros; auto.

      - erewrite map_ext_in. exact Sat. intros. simpl.
        apply plugging_terms.
        clear Sat.
        induction v. inversion H.
        inversion H; subst.
        + simpl_existT. subst. simpl in Fresh.
          now apply notin_app_l in Fresh.
        + simpl_existT. subst. simpl in Fresh.
          apply notin_app_r in Fresh. apply IHv; intros; auto.
    * do 2 rewrite sat_impl. intros. apply notin_app_l in Fresh as Fresh2.
      apply notin_app_r in Fresh.
      split; intros H H0.
      - apply (proj1 (IHφ2 t D I fail rho x dbi Fresh)).
        apply H. now apply (proj2 (IHφ1 t D I fail rho x dbi Fresh2)).
      - apply (proj2 (IHφ2 t D I fail rho x dbi Fresh)).
        apply H. now apply (proj1 (IHφ1 t D I fail rho x dbi Fresh2)).
    * do 2 rewrite sat_exs.
      simpl. split; intro H; destruct H; exists x0;
      remember (var_fresh (form_vars (bsubst_form φ (fvar x) (S dbi)))) as F1;
      remember (var_fresh (form_vars (bsubst_form φ t (S dbi)))) as F2.
      - rewrite update_env_comm.
        { admit. }
        rewrite <- bsubst_form_comm_lower; auto. 2: lia.
        specialize (IHφ t D I fail (update_env D rho F1 x0) x dbi Fresh).
        destruct IHφ.
      (* TODO: use size-based induction here! *)
      (* TODO: fresh variable operations should be supported here too! *)
  Abort.

  Theorem soundness :
    forall φ Γ, Γ ⊢_FOL φ -> valid Γ φ.
  Proof.
    intros φ Γ H. induction H; subst; unfold valid; intros.
    * now apply H.
    * do 2 rewrite sat_impl. intros. auto.
    * repeat rewrite sat_impl. intros. apply H0; auto.
    * repeat rewrite sat_impl. intros.
      rewrite sat_fal in H0.
      now apply Classical_Prop.NNPP. (* depends on ClassicalProp.classic axiom *)
    * unfold valid in *.
      eapply IHHilbert_proof_sys1 in H1 as IH1.
      eapply IHHilbert_proof_sys2 in H1 as IH2. rewrite sat_impl in IH2.
      apply IH2. exact IH1.
    * rewrite -> sat_impl, -> sat_exs. intros.
      exists (eval D fail rho t).
      (* eapply (proj1 (plugging_forms _ _ _ _ _ _ _ _ _)). exact H0. *)
      Unshelve. admit. (* TODO: fresh variable operations should be supported here too! *)
    * rewrite -> sat_impl, -> sat_exs. intros. unfold valid in *.
      destruct H1.
      remember (var_fresh (form_vars (quantify_form φ x 0))) as FF.
      apply IHHilbert_proof_sys with (rho := (update_env D rho x x0)) in H0.
      rewrite sat_impl in H0.
      (* rewrite <- fresh_irrelevant_form. apply H0. *)
      (* TODO: variable replacement is consistent with update replacement *)
      (* replace x0 with (eval D I ).
      rewrite <- plugging_forms in H1. *)
  Abort.

  Theorem completeness :
    forall φ Γ, valid Γ φ -> Γ ⊢_FOL φ.
  Proof.
  Abort.

End soundness_completeness.

Section FOL_ML_correspondence.
  Context {Σ_vars : FOL_variables}.
  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.

  Context {preds_countable : @Countable (@preds Σ_preds) preds_eqdec}
          {funs_countable : @Countable (@funs Σ_funcs) funs_eqdec}.

  Inductive Symbols : Set :=
  | sym_fun   (name : funs)
  | sym_pred  (name : preds)
  | sym_import_definedness (d : Definedness_Syntax.Symbols).

  Instance Symbols_dec : EqDecision Symbols.
  Proof.
    unfold EqDecision. intros x y. unfold Decision.
    repeat decide equality.
    apply Σ_funcs.
    apply Σ_preds.
  Defined.

  Instance Symbols_countable : Countable Symbols.
  Proof.
    destruct preds_countable as [encp decp PDE].
    inversion funs_countable as [encf decf FDE].
    set (enc :=
         fun (s : Symbols) =>
         match s with
           | sym_fun name  => inl name
           | sym_pred name => inr (inl name)
           | sym_import_definedness d => (inr (inr ()))
           end
        ).
    set (dec :=
         fun (c : funs + (preds + unit)) =>
         match c with
           | inl name       => Some (sym_fun name)
           | inr (inl name) => Some (sym_pred name)
           | (inr (inr ())) => Some (sym_import_definedness (Definedness_Syntax.definedness))
           end
        ).
    refine (inj_countable enc dec _).
    destruct x; simpl; auto.
    now destruct d.
  Defined.

  Instance FOLVars : MLVariables := 
  {|
    Signature.evar := vars;
    Signature.svar := vars;
    evar_eqdec := var_eqdec;
    svar_eqdec := var_eqdec;
    evar_countable := var_countable;
    svar_countable := var_countable;
    evar_infinite := var_infinite;
    svar_infinite := var_infinite;
  |}.

  Instance sig : Signature := 
  {|
    variables := FOLVars;
    symbols := Symbols;
    sym_countable := Symbols_countable;
  |}.

  Instance definedness_syntax : Definedness_Syntax.Syntax :=
  {|
     Definedness_Syntax.inj := sym_import_definedness;
  |}.

  Fixpoint convert_term (t : term) : Pattern :=
  match t with
   | bvar x => patt_bound_evar x
   | fvar x => patt_free_evar x
   | func f x => fold_left (fun Acc t => patt_app Acc (convert_term t)) 
                  (patt_sym (sym_fun f)) x
  end.

  Fixpoint convert_form (f : form) : Pattern :=
  match f with
   | fal => patt_bott
   | atom P x => fold_left (fun Acc t => patt_app Acc (convert_term t))
                  (patt_sym (sym_pred P)) x
   | impl x x0 => patt_imp (convert_form x) (convert_form x0)
   | exs x => patt_exists (convert_form x)
  end.

  Inductive AxName :=
  | AxDefinedness (name : Definedness_Syntax.AxiomName)
  | AxFun (f : funs)
  | AxPred (p : preds).

  Fixpoint add_forall_prefix (n : nat) (base : Pattern) {struct n} : Pattern :=
  match n with
  | 0 => base
  | S n' => patt_forall (add_forall_prefix n' base)
  end.

  Fixpoint make_list1 (n : nat) : list nat :=
  match n with
  | 0 => []
  | S n' => n :: make_list1 n'
  end.

  Fixpoint make_list0 (n : nat) : list nat :=
  match n with
  | 0 => []
  | S n' => n' :: make_list0 n'
  end.

  Definition axiom (name : AxName) : Pattern :=
  match name with 
  | AxDefinedness name' => Definedness_Syntax.axiom name'
  | AxFun f             => add_forall_prefix (ar_funs f) (patt_exists (patt_equal 
                          (List.fold_left
                            (fun Acc (x : nat) => patt_app Acc (patt_bound_evar x)) 
                            (make_list1 (ar_funs f)) (patt_sym (sym_fun f)))
                          (patt_bound_evar 0)))

  | AxPred p            => let φ := (List.fold_left
                            (fun Acc (x : nat) => patt_app Acc (patt_bound_evar x)) 
                            (make_list0 (ar_preds p)) (patt_sym (sym_pred p))) in
                          add_forall_prefix (ar_preds p) 
                            (patt_or (patt_equal φ patt_top) (patt_equal φ patt_bott))
  end.

  Theorem closed_ex_term_FOL_ML : forall t n,
    wf_term t n -> well_formed_closed_ex_aux (convert_term t) n.
  Proof.
    induction t; intros n H; auto.
    * simpl in *.
      remember (@patt_sym sig (sym_fun F)) as start.
      assert (is_true (well_formed_closed_ex_aux start n)). { rewrite Heqstart. auto. }
      clear Heqstart. generalize dependent start. induction v.
      - simpl. auto.
      - intros start H0. simpl. simpl in H. separate.
        apply IHv; auto.
        intros t H1 n1 H2. apply IH. now constructor 2. auto.
        simpl. rewrite -> H0, -> IH; auto. constructor.
  Qed.

  Theorem closed_mu_term_FOL_ML : forall t n m,
    wf_term t n -> well_formed_closed_mu_aux (convert_term t) m.
  Proof.
    induction t; intros n m H; auto.
    * simpl in *.
      remember (@patt_sym sig (sym_fun F)) as start.
      assert (is_true (well_formed_closed_mu_aux start m)). { rewrite Heqstart. auto. }
      clear Heqstart. generalize dependent start. induction v.
      - simpl. auto.
      - intros start H0. simpl. simpl in H. separate.
        apply IHv; auto.
        intros t H1 n1 m0 H2. eapply IH. now constructor 2. auto.
        simpl. eassumption. simpl. rewrite -> H0, -> IH; auto. constructor. eassumption.
  Qed.

  
  Theorem closed_ex_form_FOL_ML : forall φ n,
    wf_form φ n -> well_formed_closed_ex_aux (convert_form φ) n.
  Proof.
    induction φ; intros n H; simpl; auto.
    * simpl in *.
      remember (@patt_sym sig (sym_pred P)) as start.
      assert (is_true (well_formed_closed_ex_aux start n)). { rewrite Heqstart. auto. }
      clear Heqstart. generalize dependent start. induction v.
      - simpl. auto.
      - simpl in *. separate. intros start H.
        apply IHv; auto. simpl. rewrite -> closed_ex_term_FOL_ML, -> H; auto.
    * simpl in *. separate. subst. rewrite -> IHφ1, -> IHφ2; auto.
  Qed.

  Theorem closed_form_FOL_ML : forall φ n m,
    wf_form φ n -> well_formed_closed_mu_aux (convert_form φ) m.
  Proof.
    induction φ; intros n m H; simpl; auto.
    - simpl in *.
      remember (@patt_sym sig (sym_pred P)) as start.
      assert (is_true (well_formed_closed_mu_aux start m)). { rewrite Heqstart. auto. }
      clear Heqstart. generalize dependent start. induction v.
      + simpl. auto.
      + simpl in *. separate. intros start H.
        apply IHv; auto. simpl. rewrite -> closed_mu_term_FOL_ML, -> H; auto. eassumption.
    - simpl in *. separate. subst. rewrite -> IHφ1, -> IHφ2; auto; eassumption.
    - simpl in H. eapply IHφ. eassumption.
  Qed.

  
  Theorem positive_term_FOL_ML : forall t,
    well_formed_positive (convert_term t).
  Proof.
    induction t; auto.
    * simpl. remember (@patt_sym sig (sym_fun F)) as start.
      assert (is_true (well_formed_positive start)) by now rewrite Heqstart.
      clear Heqstart. generalize dependent start.
      induction v; intros start H; auto.
      simpl. apply IHv.
      - intros. apply IH; auto. now constructor 2.
      - simpl. rewrite -> H, -> IH; auto. constructor.
  Qed.

  Theorem positive_form_FOL_ML : forall φ,
    well_formed_positive (convert_form φ).
  Proof.
    induction φ; auto.
    * simpl. remember (@patt_sym sig (sym_pred P)) as start.
      assert (is_true (well_formed_positive start)) by now rewrite Heqstart.
      clear Heqstart. generalize dependent start. induction v; intros start H; auto.
      simpl. apply IHv.
      simpl. rewrite -> H, -> positive_term_FOL_ML; auto.
    * simpl. rewrite -> IHφ1, -> IHφ2; auto.
  Qed.

  Corollary wf_term_FOL_ML : forall t,
    wf_term t 0 -> well_formed (convert_term t).
  Proof.
    intros t H. unfold well_formed. separate. split.
    - apply positive_term_FOL_ML.
    - unfold well_formed_closed. split_and!.
      + eapply closed_mu_term_FOL_ML. eassumption.
      + apply closed_ex_term_FOL_ML. assumption.
  Qed.

  Corollary wf_form_FOL_ML : forall φ,
    wf_form φ 0 -> well_formed (convert_form φ).
  Proof.
    intros φ H. unfold well_formed. separate. split.
    - apply positive_form_FOL_ML.
    - unfold well_formed_closed. split_and!.
      + eapply closed_form_FOL_ML. eassumption.
      + apply closed_ex_form_FOL_ML. assumption.
  Qed.


  Lemma well_formed_closed_ex_prefix φ : forall n k,
    is_true (well_formed_closed_ex_aux (add_forall_prefix n φ) k) <-> 
    is_true (well_formed_closed_ex_aux φ (n + k)).
  Proof.
    induction n; simpl; auto; intros.
    do 2 rewrite andb_true_r.
    rewrite -> IHn, -> NPeano.Nat.add_succ_r. auto.
  Qed.

  Lemma well_formed_closed_prefix φ : forall n m,
    is_true (well_formed_closed_mu_aux (add_forall_prefix n φ) m) <-> 
    is_true (well_formed_closed_mu_aux φ m).
  Proof.
    induction n; simpl; auto; intros.
    do 2 rewrite andb_true_r.
    rewrite -> IHn. auto.
  Qed.
  
  Lemma well_formed_positive_prefix φ : forall n,
    is_true (well_formed_positive (add_forall_prefix n φ)) <-> 
    is_true (well_formed_positive φ).
  Proof.
    induction n; simpl; auto.
    do 2 rewrite andb_true_r. auto.
  Qed.

  Lemma well_formed_closed_ex_list n : forall start m, m > n ->
    is_true (well_formed_closed_ex_aux start m) ->
    is_true (well_formed_closed_ex_aux
     (List.fold_left
        (λ (Acc : Pattern) (x : nat), (Acc $ patt_bound_evar x)%ml)
        (make_list1 n) start )
     m).
  Proof.
    induction n; intros start m H H0; simpl; auto.
    apply (IHn). lia. simpl. rewrite H0. simpl.
    case_match; auto.
  Qed.

  Lemma well_formed_closed_list n : forall start k,
    is_true (well_formed_closed_mu_aux start k) ->
    is_true (well_formed_closed_mu_aux
     (List.fold_left
        (λ (Acc : Pattern) (x : nat), (Acc $ patt_bound_evar x)%ml)
        (make_list1 n) start )
     k).
  Proof.
    induction n; intros start k H; simpl; auto.
    apply (IHn). simpl. rewrite H. reflexivity.
  Qed.
  
  Lemma well_formed_positive_list n : forall start,
    is_true (well_formed_positive start) ->
    is_true (well_formed_positive
     (List.fold_left
        (λ (Acc : Pattern) (x : nat), (Acc $ patt_bound_evar x)%ml)
        (make_list1 n) start)).
  Proof.
    induction n; intros; simpl; auto.
    apply (IHn). simpl. rewrite H. auto.
  Qed.

  Lemma well_formed_closed_ex_list0 n : forall start m, m >= n ->
    is_true (well_formed_closed_ex_aux start m) ->
    is_true (well_formed_closed_ex_aux
     (List.fold_left
        (λ (Acc : Pattern) (x : nat), (Acc $ patt_bound_evar x)%ml)
        (make_list0 n) start)
     m).
  Proof.
    induction n; intros start m H H0; simpl; auto.
    apply (IHn). lia. simpl. rewrite H0. simpl.
    case_match; auto.
  Qed.


  Lemma well_formed_closed_mu_list0 n : forall start k,
    is_true (well_formed_closed_mu_aux start k) ->
    is_true (well_formed_closed_mu_aux
     (List.fold_left
        (λ (Acc : Pattern) (x : nat), (Acc $ patt_bound_evar x)%ml)
        (make_list0 n) start)
     k).
  Proof.
    induction n; intros start k H; simpl; auto.
    apply (IHn). simpl. rewrite H. reflexivity.
  Qed.
  
  Lemma well_formed_positive_list0 n : forall start,
    is_true (well_formed_positive start) ->
    is_true (well_formed_positive
     (List.fold_left
        (λ (Acc : Pattern) (x : nat), (Acc $ patt_bound_evar x)%ml)
        (make_list0 n) start)).
  Proof.
    induction n; intros start H; simpl; auto.
    apply (IHn). simpl. rewrite H. auto.
  Qed.


  Theorem ax_wf :
    forall F, is_true (well_formed (axiom F)).
  Proof.
    
    unfold axiom. intros F.
    break_match_goal.
    - unfold Definedness_Syntax.axiom. destruct name. simpl. constructor.
    - unfold well_formed, well_formed_closed. apply andb_true_intro. split.
      + apply well_formed_positive_prefix. simpl. rewrite well_formed_positive_list. auto.
        auto.
      + split_and!.
        * apply well_formed_closed_prefix. simpl. rewrite well_formed_closed_list.
          simpl. auto.  all: now simpl.
        * apply well_formed_closed_ex_prefix. simpl. rewrite well_formed_closed_ex_list.
          simpl. auto. lia. all: now simpl.
          
    - unfold well_formed, well_formed_closed. apply andb_true_intro. split.
      + apply well_formed_positive_prefix. simpl. rewrite well_formed_positive_list0. auto.
        auto.
      + split_and!.
        * apply well_formed_closed_prefix. simpl. rewrite well_formed_closed_mu_list0.
          2: reflexivity.
          simpl. auto.
        * apply well_formed_closed_ex_prefix. simpl. rewrite well_formed_closed_ex_list0.
          simpl. auto. lia. all: now simpl.
  Qed.


  Program Definition named_axioms : NamedAxioms := {| NAName := AxName; NAAxiom := axiom; |}.
  Next Obligation.
    intros name. apply ax_wf.
  Qed.
  
  Definition base_FOL_theory : Theory := theory_of_NamedAxioms named_axioms.

  Definition from_FOL_theory (Γ : list form) : Theory :=
    List.fold_right (fun x Acc => {[ convert_form x ]} ∪ Acc) base_FOL_theory Γ.

  Lemma have_base_FOL_theory Γ:
    base_FOL_theory ⊆ from_FOL_theory Γ.
  Proof.
    unfold from_FOL_theory.
    induction Γ.
    - simpl. set_solver.
    - simpl. set_solver.
  Qed.

  Lemma have_definedness Γ:
    Definedness_Syntax.theory ⊆ from_FOL_theory Γ.
  Proof.
    simpl.
    assert (Definedness_Syntax.theory ⊆ base_FOL_theory).
    { 
      unfold theory.
      unfold base_FOL_theory.
      unfold theory_of_NamedAxioms.
      apply elem_of_subseteq. intros ax Hax.
      inversion Hax. subst. clear Hax.
      unfold elem_of.
      apply propset.elem_of_PropSet. simpl. simpl in x.
      exists (AxDefinedness x). simpl. reflexivity.
    }
    pose proof (have_base_FOL_theory Γ).
    set_solver.
  Qed.
  
  
  Notation "Γ ⊢_FOL form" := (Hilbert_proof_sys Γ form) (at level 50).
  Notation "Γ ⊢_ML form" := (ML_proof_system Γ form) (at level 50).

  Theorem in_FOL_theory : forall Γ x,
    List.In x Γ -> convert_form x ∈ from_FOL_theory Γ.
  Proof.
    induction Γ; intros x H.
    * inversion H.
    * simpl. inversion H; subst.
      - apply sets.elem_of_union_l. now apply sets.elem_of_singleton_2.
      - apply IHΓ in H0.
        now apply sets.elem_of_union_r.
  Qed.

  Hint Resolve wf_form_FOL_ML : core.
  Hint Resolve wf_term_FOL_ML : core.

  Lemma pointwise_fold : forall n0 (v : @vec term n0) start (F : Pattern -> Pattern),
    (forall (p1 p2 : Pattern), F (patt_app p1 p2) = patt_app (F p1) (F p2)) ->
    F (fold_left (λ (Acc : Pattern) (t : term), (Acc $ convert_term t)%ml)
     start v) =
  (fold_left (λ (Acc : Pattern) (t : term), (Acc $ F (convert_term t))%ml)
     (F start) v).
  Proof.
    induction v; intros start F H.
    * simpl. auto.
    * simpl. rewrite -> IHv, -> H. auto. apply H.
  Qed.

  Corollary evar_quantify_fold : forall n0 (v : @vec term n0) start x n,
    evar_quantify x n (fold_left (λ (Acc : Pattern) (t : term), (Acc $ convert_term t)%ml)
     start v) =
  (fold_left (λ (Acc : Pattern) (t : term), (Acc $ evar_quantify x n (convert_term t))%ml)
     (evar_quantify x n start) v).
  Proof.
    intros. apply pointwise_fold. intros. auto.
  Qed.

  (** This is boiler-plate *)
  Corollary bevar_subst_fold : forall n0 (v : @vec term n0) start x n,
    bevar_subst (fold_left (λ (Acc : Pattern) (t : term), (Acc $ convert_term t)%ml)
     start v) x n =
  (fold_left (λ (Acc : Pattern) (t : term), (Acc $ bevar_subst (convert_term t) x n)%ml)
     (bevar_subst start x n) v).
  Proof.
    induction v; intros.
    * simpl. auto.
    * simpl. rewrite IHv. auto.
  Qed.

  Theorem quantify_term_correspondence :
    forall t n x, convert_term (quantify_term t x n) = 
                  evar_quantify x n (convert_term t).
  Proof.
    induction t; intros n x'; auto; cbn.
    * now destruct (decide (x' = x)).
    * remember (@patt_sym sig (sym_fun F)) as start.
      rewrite fold_left_map.
      assert (start = evar_quantify x' n start) by now rewrite Heqstart.
      clear Heqstart.
      generalize dependent start.
      induction v; intros; simpl; auto.
      rewrite IHv.
      - intros. apply IH. now constructor 2.
      - simpl. rewrite <- H, IH, double_evar_quantify; auto. constructor.
      - do 2 rewrite evar_quantify_fold.
        simpl. rewrite -> IH, -> double_evar_quantify. auto. simpl.
        constructor.
  Qed.

  Theorem quantify_form_correspondence :
    forall φ n x, convert_form (quantify_form φ x n) = 
                  evar_quantify x n (convert_form φ).
  Proof.
    induction φ; intros n x'; auto; cbn.
    * remember (@patt_sym sig (sym_pred P)) as start.
      rewrite fold_left_map.
      assert (start = evar_quantify x' n start) by now rewrite Heqstart.
      clear Heqstart.
      generalize dependent start.
      induction v; intros; simpl; auto.
      rewrite IHv.
      - simpl. rewrite <- H, quantify_term_correspondence, double_evar_quantify; auto.
      - do 2 rewrite evar_quantify_fold.
        simpl. rewrite -> quantify_term_correspondence, -> double_evar_quantify. auto.
    * now rewrite -> IHφ1, -> IHφ2.
    * now rewrite IHφ.
  Qed.

  Theorem term_vars_free_vars_notin :
    forall t x, ~List.In x (term_vars t) -> x ∉ (free_evars (convert_term t)).
  Proof.
    induction t; intros x' H.
    * simpl. intros H0. apply H. simpl. apply sets.elem_of_singleton_1 in H0. auto.
    * intro. simpl in H0. inversion H0.
    * simpl in H. simpl. 
      remember (@patt_sym sig (sym_fun F)) as start.
      assert (x' ∉ free_evars start) by now rewrite Heqstart.
      clear Heqstart. generalize dependent start. 
      induction v; intros.
      - auto.
      - simpl. epose proof (IHv _ _ (start $ convert_term h)%ml _). clear IHv.
        apply H1.
      Unshelve.
        intros. apply IH. now constructor 2. auto.
        simpl in H. now apply notin_app_r in H.
        simpl in H. apply notin_app_l in H. apply IH in H.
        simpl. intro. apply elem_of_union in H1; inversion H1; contradiction.
        constructor.
  Qed.

  Theorem form_vars_free_vars_notin :
    forall φ x, ~List.In x (form_vars φ) -> x ∉ (free_evars (convert_form φ)).
  Proof.
    induction φ; intros x' H; auto.
    * intro. inversion H0.
    * simpl in H. simpl. 
      remember (@patt_sym sig (sym_pred P)) as start.
      assert (x' ∉ free_evars start) by now rewrite Heqstart.
      clear Heqstart. generalize dependent start. 
      induction v; intros.
      - auto.
      - simpl. epose proof (IHv _ (start $ convert_term h)%ml _). clear IHv.
        apply H1.
      Unshelve.
        simpl in H. now apply notin_app_r in H.
        simpl in H. apply notin_app_l in H. apply term_vars_free_vars_notin in H.
        simpl. intro. apply elem_of_union in H1; inversion H1; contradiction.
    * simpl in *. apply notin_app_r in H as H'. apply notin_app_l in H.
      apply IHφ1 in H. apply IHφ2 in H'.
      apply sets.not_elem_of_union. auto.
  Qed.

  Theorem bevar_subst_corr_term :
    forall b t n, wf_term t n -> wf_term b (S n) ->
                  convert_term (bsubst_term b t n) = 
                  bevar_subst (convert_term b) (convert_term t) n.
  Proof.
    induction b; intros t n H H0; auto.
    * simpl. now repeat (case_match; simpl).
    * simpl. remember (@patt_sym sig (sym_fun F)) as start.
      rewrite fold_left_map.
      assert (start = bevar_subst start (convert_term t) n) by now rewrite Heqstart.
      clear Heqstart. simpl in H0.
      generalize dependent start.
      induction v; intros; simpl; auto.
      rewrite IHv.
      - intros. apply IH. constructor 2; auto. auto. auto.
      - simpl in H0. now apply andb_true_iff in H0.
      - simpl. simpl in H0. apply andb_true_iff in H0 as [Wf1 Wf2]. erewrite <- H1, IH; auto.
        2: constructor.
        apply closed_ex_term_FOL_ML in Wf2 as Wf2'. apply closed_ex_term_FOL_ML in H as H'; auto.
        apply bevar_subst_closed_ex with (ψ := convert_term t) in Wf2'; auto.
        rewrite -> (bevar_subst_not_occur _ Wf2'); auto.
      - do 2 rewrite bevar_subst_fold.
        simpl. simpl in H0. apply andb_true_iff in H0 as [Wf1 Wf2].
        apply closed_ex_term_FOL_ML in Wf2 as Wf2'. apply closed_ex_term_FOL_ML in H as H'; auto.
        apply bevar_subst_closed_ex with (ψ := convert_term t) in Wf2'; auto.
        erewrite IH. rewrite -> (bevar_subst_not_occur _ Wf2'); auto.
        constructor. auto. auto.
  Qed.

  Theorem bevar_subst_corr_form :
    forall φ t n, wf_term t n -> wf_form φ (S n) ->
                  convert_form (bsubst_form φ t n) = 
                  bevar_subst (convert_form φ) (convert_term t) n.
  Proof.
    induction φ; intros t n H H0; auto.
    * simpl.
      remember (@patt_sym sig (sym_pred P)) as start.
      rewrite fold_left_map.
      assert (start = bevar_subst start (convert_term t) n) by now rewrite Heqstart.
      clear Heqstart. revert H.
      generalize dependent start. simpl in H0.
      induction v; intros; simpl; auto.
      rewrite IHv.
      - now apply andb_true_iff in H0.
      - intros. simpl in H0. apply andb_true_iff in H0 as [Wf1 Wf2].
        rewrite bevar_subst_corr_term; auto.
        apply closed_ex_term_FOL_ML in Wf2 as Wf2'. apply closed_ex_term_FOL_ML in H as H'; auto.
        apply bevar_subst_closed_ex with (ψ := convert_term t) in Wf2'; auto. simpl.
        rewrite -> (bevar_subst_not_occur (convert_term t) Wf2'), <- H1; auto.
      - auto.
      - do 2 rewrite bevar_subst_fold. simpl in H0. apply andb_true_iff in H0 as [Wf1 Wf2].
        simpl. erewrite bevar_subst_corr_term, <- H1.
        apply closed_ex_term_FOL_ML in Wf2 as Wf2'. apply closed_ex_term_FOL_ML in H as H'; auto.
        apply bevar_subst_closed_ex with (ψ := convert_term t) in Wf2'; auto. simpl.
        rewrite -> (bevar_subst_not_occur (convert_term t) Wf2'); auto.
        auto. auto.
    * simpl. apply andb_true_iff in H0. rewrite -> IHφ1, -> IHφ2; auto; apply H0. 
    * simpl. rewrite IHφ. auto. eapply wf_increase_term. apply H. lia. auto. auto.
  Qed.

  Theorem ax_in :
    forall Γ F, axiom F ∈ from_FOL_theory Γ.
  Proof.
    induction Γ; intros F.
    * simpl. unfold base_FOL_theory. econstructor.
      reflexivity.
    * simpl. apply sets.elem_of_union_r. apply IHΓ.
  Qed.

  Lemma add_forall_prefix_subst : forall n φ ψ m,
    bevar_subst (add_forall_prefix n φ) ψ m = add_forall_prefix n (bevar_subst φ ψ (m + n)).
  Proof.
    induction n; intros.
    * cbn. auto.
    * simpl. rewrite -> IHn, -> Nat.add_succ_comm. auto.
  Qed.

  Lemma subst_make_list : forall n m ψ start, m > n ->
    bevar_subst
       (List.fold_left
          (λ (Acc : Pattern) (x : nat),
             (Acc $ patt_bound_evar x)%ml) 
          (make_list1 n) start)
       ψ m =
    (List.fold_left
          (λ (Acc : Pattern) (x : nat),
             (Acc $ patt_bound_evar x)%ml) 
          (make_list1 n) (bevar_subst start ψ m)).
  Proof.
    induction n; intros; cbn; auto.
    rewrite IHn. lia. cbn. break_match_goal; auto. lia. lia.
  Qed.

  Lemma term_mu_free :
    forall t, mu_free (convert_term t).
  Proof.
    induction t; auto.
    simpl. remember (@patt_sym sig (sym_fun F)) as start.
    assert (is_true (mu_free start)) by (rewrite Heqstart; constructor). clear Heqstart.
    generalize dependent start.
    induction v; simpl.
    * intros. auto.
    * intros. eapply IHv.
      intros. apply IH. constructor 2; auto.
      simpl. rewrite H. auto. apply IH. constructor.
  Qed.

  Lemma form_mu_free:
    forall φ, mu_free (convert_form φ).
  Proof.
    induction φ; auto.
    * simpl. remember (@patt_sym sig (sym_pred P)) as start.
      assert (is_true (mu_free start)) by (rewrite Heqstart; constructor). clear Heqstart.
      generalize dependent start. induction v; simpl; auto.
      intros start H. eapply IHv.
      simpl. now rewrite -> H, -> term_mu_free.
    * simpl. now rewrite -> IHφ1, -> IHφ2.
  Qed.

  Proposition term_functionality :
    forall t Γ, wf_term t 0 ->
      from_FOL_theory Γ ⊢_ML patt_exists (patt_equal (convert_term t) (patt_bound_evar 0)) .
  Proof.
    induction t using term_rect; intros.
    * simpl.
      pose proof (@Ex_quan _ (from_FOL_theory Γ) (patt_equal (patt_free_evar x) (patt_bound_evar 0)) x ltac:(wf_auto2)). unfold instantiate in H0.
      simpl in H0. eapply MP.
      epose proof (@patt_equal_refl _ _ (patt_free_evar x) (from_FOL_theory Γ) _).
      gapply H1. apply pile_any.
      gapply H0. apply pile_any.
    * simpl in H. inversion H.
    * assert (from_FOL_theory Γ ⊢_ML axiom (AxFun F) ). {
        gapply hypothesis. apply pile_any. apply ax_wf. apply ax_in.
      } simpl in H1, H0.
      simpl. remember (@patt_sym sig (sym_fun F)) as start.
      assert (forall n ψ, bevar_subst start ψ n = start) as HIND. 
        { intros. rewrite Heqstart. auto. }
      assert (is_true (mu_free start)) as HMUF. { rewrite Heqstart. constructor. }
      assert (is_true (well_formed start)) as WFS. { rewrite Heqstart. auto. }
      clear Heqstart. generalize dependent start.
      revert H0. induction v; intros.
      - cbn. simpl in H1. exact H1.
      - cbn in *. eapply (IHv _ _ (start $ convert_term h)%ml); clear IHv.
        separate.
        specialize (H h ltac:(constructor) Γ E2).
        remember (add_forall_prefix n
            (ex ,
              patt_equal
                (List.fold_left
                   (λ (Acc : Pattern) (x : nat), (Acc $ patt_bound_evar x)%ml)
                   (make_list1 n) (start $ patt_bound_evar (S n))%ml)
                BoundVarSugar.b0)) as A.
        pose proof (@forall_functional_subst _ _ A (convert_term h) (from_FOL_theory Γ)).
        assert (mu_free A). {
          rewrite HeqA. clear H HIND H1 HeqA E1 E2 H0 h v Γ A F WFS.
          generalize dependent start. induction n; simpl.
          * intros. repeat constructor. all: rewrite HMUF; auto.
          * intros. simpl. rewrite IHn; auto. simpl. now rewrite HMUF.
        }
        assert (well_formed (all , A)) as WfA.
        {
          rewrite HeqA. clear H E1 E2 H2 HIND H1 H H0 h v Γ H2 HeqA A F HMUF.
          unfold well_formed, well_formed_closed.
          apply eq_sym, andb_true_eq in WFS. destruct WFS.
          apply andb_true_intro. split.
          - clear H0. apply well_formed_positive_all, well_formed_positive_prefix.
            simpl. generalize dependent start. induction n; simpl; intros.
            + rewrite <- H. auto.
            + rewrite IHn; auto. simpl. rewrite <- H. auto.
          - clear H.
            split_and!.
            + apply well_formed_closed_mu_all, well_formed_closed_prefix.
              simpl.
              split_and!; auto.
              all: apply well_formed_closed_list; simpl; symmetry in H0;
                unfold well_formed_closed in *; destruct_and!; split_and; auto.
            + apply well_formed_closed_ex_all, well_formed_closed_ex_prefix.
              simpl.
              split_and!; auto.
              all: apply well_formed_closed_ex_list; try lia; simpl; symmetry in H0;
                unfold well_formed_closed in *; destruct_and!; split_and;
                  try case_match;
                  auto; try lia.
              all: eapply well_formed_closed_ex_aux_ind; try eassumption; lia.
        }
        assert (from_FOL_theory Γ ⊢_ML (all , A and ex , patt_equal (convert_term h) BoundVarSugar.b0 ) ). {
          apply conj_intro_meta; auto.
          unfold well_formed. simpl. rewrite positive_term_FOL_ML.
          unfold well_formed_closed. simpl. apply wf_increase_term with (n' := 1) in E2. 2: lia.
          pose proof (E2' := E2).
          eapply closed_ex_term_FOL_ML in E2.
          eapply closed_mu_term_FOL_ML in E2'.
          split_and!; eauto.
        }
        apply MP in H0; auto.
        simpl in H0.
        rewrite -> HeqA, -> add_forall_prefix_subst in H0.
        simpl Nat.add in H0.
        replace (bevar_subst
              (ex ,
               @patt_equal sig definedness_syntax
                 (List.fold_left
                    (λ (Acc : Pattern) (x : nat),
                       (Acc $ patt_bound_evar x)%ml) 
                    (make_list1 n) (start $ patt_bound_evar (S n))%ml)
                 BoundVarSugar.b0) (convert_term h) n) with
             ((ex ,
               @patt_equal sig definedness_syntax
                 (bevar_subst (List.fold_left
                    (λ (Acc : Pattern) (x : nat),
                       (Acc $ patt_bound_evar x)%ml) 
                    (make_list1 n) (start $ patt_bound_evar (S n))%ml) (convert_term h) (S n))
                 BoundVarSugar.b0)) in H by auto.
        simpl in H0.
        rewrite subst_make_list in H0. lia.
        simpl in H0. rewrite HIND in H0. break_match_hyp.
        + lia.
        + exact H0.
        + lia.
        + apply have_definedness.
        (** asserted hypotheses *)
        + apply andb_true_iff in WfA as [_ WfA]. apply andb_true_iff in WfA as [_ WfA]. cbn in WfA.
          now destruct_and!.
        + apply andb_true_iff in WfA as [_ WfA]. apply andb_true_iff in WfA as [WfA _]. cbn in WfA.
          now destruct_and!.
        + intros. simpl. rewrite HIND. erewrite well_formed_bevar_subst.
          auto.
          2: { apply closed_ex_term_FOL_ML. inversion H0. separate. eassumption. }
          lia.
        + simpl. now rewrite -> HMUF, -> term_mu_free.
        + unfold well_formed, well_formed_closed in *.
          simpl. apply eq_sym, andb_true_eq in WFS. destruct WFS.
          symmetry in H2, H3.
          destruct_and!. split_and!; auto.
          ++ apply positive_term_FOL_ML.
          ++ eapply closed_mu_term_FOL_ML; eassumption.
          ++ apply closed_ex_term_FOL_ML; assumption.
  Unshelve.
    ** auto.
    ** intros. apply H; auto. constructor 2; auto.
    ** now separate.
  Qed.

  Theorem arrow_1 : forall (φ : form) (Γ : list form), 
    Γ ⊢_FOL φ
   -> 
    from_FOL_theory Γ ⊢_ML convert_form φ .
  Proof.
    intros φ Γ IH. induction IH; intros.
    * gapply hypothesis. apply pile_any.
      now apply wf_form_FOL_ML. now apply in_FOL_theory.
    * simpl. useBasicReasoning. apply P1; auto.
    * useBasicReasoning. apply P2; auto.
    * useBasicReasoning. apply P3; auto.
    * eapply MP. exact IHIH1. exact IHIH2.
    * simpl. unfold is_true in *.
      epose proof (term_functionality t Γ i0).
      pose proof (@exists_functional_subst _ _ (convert_form φ) (convert_term t) (from_FOL_theory Γ)).
      simpl in H0. rewrite bevar_subst_corr_form; auto.
      eapply and_impl_patt2. 4: exact H. 4: apply H0.
      all: unfold well_formed, well_formed_closed in *; simpl in *.
      all: try rewrite -> closed_ex_term_FOL_ML.
      all: try rewrite -> closed_mu_term_FOL_ML.
      all: try eassumption.
      all: split_and?; auto; simpl in *.
      10: apply have_definedness.
      all: try apply closed_ex_form_FOL_ML; try assumption.
      all: try apply form_mu_free.
      all: try apply wf_increase_term with (n := 0); auto.
      all: try apply well_formed_positive_bevar_subst; auto using form_mu_free.
      all: try apply positive_form_FOL_ML.
      all: try apply positive_term_FOL_ML.
      all: try apply bevar_subst_closed_mu.      
      all: try eapply closed_form_FOL_ML; try eassumption.
      all: try eapply closed_mu_term_FOL_ML; try eassumption.
      all: try apply bevar_subst_closed_ex; try apply closed_ex_form_FOL_ML; try assumption.
      apply closed_ex_term_FOL_ML. assumption.
    * simpl. rewrite quantify_form_correspondence. gapply Ex_gen; auto.
      1-2: apply pile_any.
      now apply form_vars_free_vars_notin.
      gapply IHIH. apply pile_any.
  Qed.


End FOL_ML_correspondence.

Section tests.

  Inductive PA_funcs : Set :=
    Zero : PA_funcs
  | Succ : PA_funcs
  | Plus : PA_funcs
  | Mult : PA_funcs.

  Instance pa_funs_eqdec : EqDecision PA_funcs.
  Proof.
    unfold EqDecision, Decision; intros. decide equality.
  Defined.

  Definition PA_funcs_ar (f : PA_funcs) :=
  match f with
   | Zero => 0
   | Succ => 1
   | Plus => 2
   | Mult => 2
   end.

  Inductive PA_preds : Set :=
    Eq : PA_preds.

  Instance pa_preds_eqdec : EqDecision PA_preds.
  Proof.
    solve_decision.
  Defined.

  Instance pa_funcs_eqdec : EqDecision PA_funcs.
  Proof.
    solve_decision.
  Defined.

  Definition PA_preds_ar (P : PA_preds) :=
  match P with
   | Eq => 2
  end.

  Instance PA_funcs_signature : funcs_signature :=
  {| funs := PA_funcs ; funs_eqdec := pa_funs_eqdec; ar_funs := PA_funcs_ar |}.

  Instance PA_preds_signature : preds_signature :=
  {| preds := PA_preds ; preds_eqdec := pa_preds_eqdec; ar_preds := PA_preds_ar |}.

  Program Instance PA_preds_finite : Finite PA_preds := {| enum := [Eq] |}.
  Next Obligation.
    repeat constructor. set_solver.
  Qed.
  Next Obligation.
    intros []. set_solver.
  Qed.
  Program Instance PA_funcs_finite : 
    Finite (@funs PA_funcs_signature) := {| enum := [Zero;Succ;Plus;Mult] |}.
  Next Obligation.
    repeat constructor; set_solver.
  Qed.
  Next Obligation.
    intros []; set_solver.
  Qed.

  Instance pa_preds_countable : Countable PA_preds.
  Proof. apply _. Qed.

  Instance pa_funcs_countable : Countable PA_funcs.
  Proof. apply _. Qed.

  Context {Σ_vars : FOL_variables}.
  Instance sig2 : Signature := 
  {|
    variables := @FOLVars Σ_vars;
    symbols := Symbols;
    sym_eqdec := Symbols_dec;
    sym_countable := Symbols_countable;
  |}.

  Instance definedness_syntax2 : Definedness_Syntax.Syntax :=
  {|
     Definedness_Syntax.inj := sym_import_definedness;
  |}.

  Goal axiom (AxFun Mult) = patt_forall (patt_forall (patt_exists (patt_equal 
             (patt_app (patt_app (patt_sym (sym_fun Mult)) (patt_bound_evar 2)) (patt_bound_evar 1))
             (patt_bound_evar 0)))).
  Proof.
    simpl. reflexivity.
  Qed.
  Goal axiom (AxPred Eq) = patt_forall (patt_forall (patt_or (patt_equal 
             (patt_app (patt_app (patt_sym (sym_pred Eq)) (patt_bound_evar 1)) (patt_bound_evar 0)) patt_top)
             (patt_equal 
             (patt_app (patt_app (patt_sym (sym_pred Eq)) (patt_bound_evar 1)) (patt_bound_evar 0)) patt_bott))
             ).
  Proof.
    simpl. reflexivity.
  Qed.
  Goal convert_term (func Plus (cons (func Zero nil) (cons (func Succ (cons (func Zero nil) nil)) nil))) =
     patt_app (patt_app (patt_sym (sym_fun Plus)) (patt_sym (sym_fun Zero))) (patt_app (patt_sym (sym_fun Succ)) (patt_sym (sym_fun Zero))).
   Proof.
     simpl. reflexivity.
   Qed.

End tests.
