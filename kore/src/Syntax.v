From Kore Require Export Signature.
From MatchingLogic Require Export extralibrary
                                  Lattice.


Set Default Proof Mode "Classic".

Section Syntax.

  Context {Σ : Signature}.

  Inductive Pattern :=
  | kore_bevar (dbi : nat) (* (s : sort) ? *)
  | kore_bsvar (dbi : nat) (* (s : sort) ? *)
  | kore_fevar (x : evar) (* (s : sort) ? *)
  | kore_fsvar (X : svar) (* (s : sort) ? *)

  | kore_app   (σ : symbol) (* (ss : list sort) ? *) (args : list Pattern)

  | kore_bot   (s : sort)
  | kore_top   (s : sort)
  | kore_not   (φ : Pattern)     (* (s : sort) ? *)
  | kore_and   (φ1 φ2 : Pattern) (* (s : sort) ? *)
  | kore_or    (φ1 φ2 : Pattern) (* (s : sort) ? *)
  | kore_imp   (φ1 φ2 : Pattern) (* (s : sort) ? *)
  | kore_iff   (φ1 φ2 : Pattern) (* (s : sort) ? *)

  | kore_exists (s_var : sort) (φ : Pattern) (* (s_ret : sort) ? *)
  | kore_forall (s_var : sort) (φ : Pattern) (* (s_ret : sort) ? *)

  | kore_mu    (s_var : sort) (φ : Pattern)
  | kore_nu    (s_var : sort) (φ : Pattern)

  (* if s1 is omitted from the following constructs, well_sorted would
     become not computable! *)
  | kore_ceil  (s1 s2 : sort) (φ : Pattern)
  | kore_floor (s1 s2 : sort) (φ : Pattern)
  | kore_equal (s1 s2 : sort) (φ1 φ2 : Pattern)
  | kore_in    (s1 s2 : sort) (φ1 φ2 : Pattern)

  | kore_next     (* (s : sort) ? *) (φ : Pattern)
  | kore_rewrites (* (s : sort) ? *) (φ1 φ2 : Pattern)
  | kore_dv       (s : sort) (s : string).


  Section pat_ind.

    Variables
      (P : Pattern -> Prop).
    Hypotheses
      (P_bevar : forall dbi, P (kore_bevar dbi))
      (P_fevar : forall x, P (kore_fevar x))
      (P_bsvar : forall dbi, P (kore_bsvar dbi))
      (P_fsvar : forall x, P (kore_fsvar x))

      (P_app : forall σ args, Forall P args -> P (kore_app σ args))

      (P_bot : forall s, P (kore_bot s))
      (P_top : forall s, P (kore_top s))
      (P_not : forall φ, P φ -> P (kore_not φ))
      (P_and : forall φ, P φ -> forall ψ, P ψ -> P (kore_and φ ψ))
      (P_or : forall φ, P φ -> forall ψ, P ψ -> P (kore_or φ ψ))
      (P_imp : forall φ, P φ -> forall ψ, P ψ -> P (kore_imp φ ψ))
      (P_iff : forall φ, P φ -> forall ψ, P ψ -> P (kore_iff φ ψ))

      (P_exists : forall s φ, P φ -> P (kore_exists s φ))
      (P_forall : forall s φ, P φ -> P (kore_forall s φ))
      (P_mu : forall s φ, P φ -> P (kore_mu s φ))
      (P_nu : forall s φ, P φ -> P (kore_nu s φ))

      (P_ceil : forall s1 s2 φ, P φ -> P (kore_ceil s1 s2 φ))
      (P_floor : forall s1 s2 φ, P φ -> P (kore_floor s1 s2 φ))
      (P_equal : forall s1 s2 φ, P φ -> forall ψ, P ψ -> P (kore_equal s1 s2 φ ψ))
      (P_in : forall s1 s2 φ, P φ -> forall ψ, P ψ -> P (kore_in s1 s2 φ ψ))

      (P_next : forall φ, P φ -> P (kore_next φ))
      (P_rewrites : forall φ, P φ -> forall ψ, P ψ -> P (kore_rewrites φ ψ))
      (P_dv : forall s str, P (kore_dv s str)).

    Definition Pat_ind (φ : Pattern) : P φ.
    Proof.
      revert φ.
      refine (fix Pat_ind φ :=
      match φ with
       | kore_bevar dbi => P_bevar dbi
       | kore_fevar x => P_fevar x
       | kore_bsvar dbi => P_bsvar dbi
       | kore_fsvar x => P_fsvar x

       | kore_app σ args => _

       | kore_bot s => P_bot s
       | kore_top s => P_top s
       | kore_not φ => P_not _ (Pat_ind φ)
       | kore_and φ1 φ2 => P_and _ (Pat_ind φ1) _ (Pat_ind φ2)
       | kore_or  φ1 φ2 => P_or _ (Pat_ind φ1) _ (Pat_ind φ2)
       | kore_imp φ1 φ2 => P_imp _ (Pat_ind φ1) _ (Pat_ind φ2)
       | kore_iff φ1 φ2 => P_iff _ (Pat_ind φ1) _ (Pat_ind φ2)

       | kore_exists σ φ => P_exists σ _ (Pat_ind φ)
       | kore_forall σ φ => P_forall σ _ (Pat_ind φ)

       | kore_mu σ φ => P_mu σ _ (Pat_ind φ)
       | kore_nu σ φ => P_nu σ _ (Pat_ind φ)

       | kore_ceil s1 s2 φ => P_ceil s1 s2 _ (Pat_ind φ)
       | kore_floor s1 s2 φ => P_floor s1 s2 _ (Pat_ind φ)
       | kore_equal s1 s2 φ1 φ2 => P_equal s1 s2 _ (Pat_ind φ1) _ (Pat_ind φ2)
       | kore_in    s1 s2 φ1 φ2 => P_in s1 s2 _ (Pat_ind φ1) _ (Pat_ind φ2)

       | kore_next φ => P_next _ (Pat_ind φ)
       | kore_rewrites φ ψ => P_rewrites _ (Pat_ind φ) _ (Pat_ind ψ)
       | kore_dv s str => P_dv s str
      end).
      apply P_app.
      induction args; constructor.
      by apply Pat_ind.
      assumption.
    Defined.
  End pat_ind.

End Syntax.

Module Notations.

  Declare Scope kore_scope.
  Delimit Scope kore_scope with kore.

  Notation "'⊥(' s ')'" := (kore_bot s) (format "'⊥(' s ')'") : kore_scope.
  Check ⊥( _ )%kore.
  Notation "'Top(' s ')'" := (kore_top s) (format "'Top(' s ')'") : kore_scope.
  Check Top( _ )%kore.
  Notation "'!' p" := (kore_not p) (at level 71, format "'!'  p") : kore_scope.
  Check (! ⊥(_))%kore.
  Notation "p1 'and' p2" := (kore_and p1 p2) (at level 72, format "p1  'and'  p2", left associativity) : kore_scope.
  Check (⊥ and(_) Top)%kore.
  Notation "p1 'or' p2" := (kore_or p1 p2) (at level 73, format "p1  'or'  p2", left associativity) : kore_scope.
  Check (⊥ or( _ ) Top)%kore.
  Notation "p1 '--->' p2" := (kore_imp p1 p2) (at level 75, format "p1  '--->'  p2", right associativity) : kore_scope.
  Check (⊥ ---> Top(_))%kore.
  Notation "p1 '<--->' p2" := (kore_iff p1 p2) (at level 74, format "p1  '<--->'  p2") : kore_scope.
  Check (⊥ <---> Top(_))%kore.

  Notation "s ⋅ pars" := (kore_app s pars) (at level 70, format "s '⋅' pars") : kore_scope.


  Notation "'ex' s1 ',' p 'as' s2" := (kore_exists s1 s2 p) (at level 80, s2 at level 65, format "'ex'  s1 ','  p  'as'  s2") : kore_scope.
  Check ex Nat , ⊥ as Nat.
  Notation "'all' s1 ',' p 'as' s2" := (kore_forall s1 s2 p) (at level 80, s2 at level 65, format "'all'  s1 ','  p  'as'  s2") : kore_scope.
  Goal forall {Σ : Signature} {s1 : Syntax} {s2 : Nat_Syntax.Syntax},
    ~ (all Nat , ⊥ as Nat ⋅ Nat) = (all Nat , ⊥ as (Nat ⋅ Nat)).
  Proof. intros. intro. inversion H. Qed.

  Notation "'⌈(' s1 , s2 ')' p ⌉" := (kore_ceil s1 s2 p) (format "'⌈(' s1 ',' s2 ')'  p ⌉") : kore_scope.
  Check ⌈(Nat, Nat) ⊥⌉.
  Notation "'⌊(' s1 , s2 ')' p ⌋" := (kore_floor s1 s2 p) (format "'⌊(' s1 ',' s2 ')'  p ⌋") : kore_scope.
  Check ⌊(Nat, Nat) ⊥⌋.
  Notation "p1 '=ml(' s1 ',' s2 ')' p2" := (kore_equals s1 s2 p1 p2) (at level 68, format "p1  '=ml(' s1 ',' s2 ')'  p2", left associativity) : kore_scope.
  Check ⊥ =ml(Nat, Nat) Top.
  Notation "p1 '⊆ml(' s1 ',' s2 ')' p2" := (kore_in s1 s2 p1 p2) (at level 68, format "p1  '⊆ml(' s1 ',' s2 ')'  p2", left associativity) : kore_scope.
  Check ⊥ ⊆ml(Nat, Nat) Top.




(*   Notation "''" := (kore_is_sort s).
  Notation := (kore_is_predicate s p).
  Notation := (kore_is_nonempty_sort s). *)

  (* Notation "'mu' s , p" := (kore_mu s p) (at level 80).
  Check mu Nat, ⊥.
  Notation "'nu' s , p" := (kore_nu s p) (at level 80).
  Check nu Nat, ⊥. *)

  Notation "'•(' s ')' p"    := (kore_next s p) (at level 30, format "'•(' s ')'  p") : kore_scope.
  Check •(Nat) ⊥.
  Notation "'○(' s ')' p"    := (kore_all_path_next s p) (at level 71, format "'○(' s ')'  p") : kore_scope.
  Check ○(Nat) ⊥.
  Notation "'⋄(' s ')' p"    := (kore_eventually s p) (at level 71, format "'⋄(' s ')'  p") : kore_scope.
  Check ⋄(Nat) ⊥.
  Notation "'⋄ʷ(' s ')' p"   := (kore_weak_eventually s p) (at level 71, format "'⋄ʷ(' s ')'  p") : kore_scope.
  Check ⋄ʷ(Nat) ⊥.
(*   Notation "s"       := (kore_well_founded s) (at level 71) : kore_scope. *)
(*   Notation ""       := (kore_well_founded_alt s) (at level 71) : kore_scope. *)
  Notation "'⊞(' s ')' p"    := (kore_always s p) (at level 71, format "'⊞(' s ')'  p") : kore_scope. (* □ is taken by application contexts *)
  Check ⊞(Nat) ⊥.
  Notation "p '=(' s ')=>' q"  := (kore_rewrites s p q) (at level 81, format "p  '=(' s ')=>'  q") : kore_scope.
  Check ⊥ =(Nat)=> Top.
  Notation "p '=(' s ')=>*' q" := (kore_rewrites_star s p q) (at level 81, format "p  '=(' s ')=>*'  q") : kore_scope.
  Check ⊥ =(Nat)=>* Top.
  Notation "p '=(' s ')=>⁺' q" := (kore_rewrites_plus s p q) (at level 81, format "p  '=(' s ')=>⁺'  q") : kore_scope.
  Check ⊥ =(Nat)=>⁺ Top.

(* These probably don't need notations:
  Notation "" := (kore_one_path_reaches_star s p1 p2).
  Notation := (kore_one_path_reaches_plus s p1 p2). *)
  Notation "'↺(' s ')' p" := (kore_circularity s p) (at level 71, format "'↺(' s ')'  p").
  Check ↺(Nat) ⊥.
  Notation "s ⇑" := (kore_non_terminating s) (at level 90).
  Check ⊥ ⋅ ⊥ ⇑.

End Notations.


Section Sortedness.

  Context {Σ : Signature}.

  Definition shift {T : Set} (f : nat -> T) (d : T)
    : nat -> T :=
    fun n => match n with
              | O => d
              | S n' => f n'
             end.

  Definition update {T : Set} (n : nat) (d : T) (f : nat -> T)
    : nat -> T :=
    fun m => if decide (n = m) then d else f m.

  Fixpoint app_ws (well_sorted : opml_sort -> OPMLPattern -> bool)
                  (φs : list OPMLPattern)
                  (ss : list opml_sort) {struct φs} :=
    match φs, ss with
    | [], [] => true
    | φ::φs, s::ss => well_sorted s φ &&
                      app_ws well_sorted φs ss
    | _, _ => false
    end.

  Fixpoint well_sorted
    (esorts : nat -> option opml_sort)
    (ssorts : nat -> option opml_sort)
    (s : opml_sort)
    (p : OPMLPattern) {struct p} : bool :=(* 
  Proof.
    revert p esorts ssorts s.
    refine (
    fix well_sorted p esorts ssorts s := *)
    match p with
     | kore_bot => true
     | kore_bevar dbi => decide (esorts dbi = Some s)
     | kore_bsvar dbi => decide (ssorts dbi = Some s)
     | kore_fevar x => decide (evar_sort x = s)
     | kore_fsvar X => decide (svar_sort X = s)
     | kore_imp φ1 φ2 => well_sorted esorts ssorts s φ1 &&
                       well_sorted esorts ssorts s φ2
     | kore_app σ args =>
        decide (s = opml_ret_sort σ) &&
        app_ws (well_sorted esorts ssorts) args (opml_arg_sorts σ)
     | kore_ex s0 φ => well_sorted (shift esorts (Some s0)) ssorts s φ
     | kore_mu s0 φ => well_sorted esorts (shift ssorts (Some s0)) s φ
     | kore_eq s1 s2 φ1 φ2
        => well_sorted esorts ssorts s1 φ1 &&
           well_sorted esorts ssorts s1 φ2 &&
           decide (s2 = s)
    end.

End Syntax.