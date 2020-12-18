(* In this module we define the definedness symbol and use it to build derived notions
   like totality and equality.
 *)
From Coq Require Import String Ensembles.
Require Import Coq.Logic.Classical_Prop.
From MatchingLogic Require Import Syntax Semantics.
From MatchingLogic.Utils Require Import Ensembles_Ext. 

Import MatchingLogic.Syntax.Notations.
Import MatchingLogic.Semantics.Notations.

Open Scope ml_scope.

(* We have only one symbol *)
Inductive Symbols := definedness.

Section definedness.
  Context {sig : Signature}.

  Class Syntax(*(sig : Signature)*) :=
    { (*sig: Signature;*)
    (* 'Symbols' are a 'subset' of all the symbols from the signature *)
    inj: Symbols -> symbols;
    (* TODO make it injective? *)
    (* for convenience *)
    }.  

  Context {self : Syntax}.

  Let Pattern : Type := @MatchingLogic.Syntax.Pattern sig.

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

  Let sym (s : Symbols) : Pattern :=
    @patt_sym sig (inj s).
  
  Let evarn (name : string) : Pattern :=
    @patt_free_evar sig (nevar name).


  Inductive AxiomName := AxDefinedness.

  Definition axiom(name : AxiomName) : Pattern :=
    match name with
    | AxDefinedness => patt_defined (evarn "x")
    end.

  Definition named_axioms : NamedAxioms := {| NAName := AxiomName; NAAxiom := axiom; |}.

  Definition theory := theory_of_NamedAxioms named_axioms.
  
  Lemma definedness_model_application :
    forall (M : @Model sig) (evar_val : @EVarVal sig M) (svar_val : @SVarVal (sig) M),
      M ⊨ᵀ theory ->
      forall (m: Domain M),
                 (app_ext (pattern_interpretation evar_val svar_val (sym definedness)) (Singleton (Domain M) m)) = Full.
  Proof.
    intros.
    symmetry.
    apply Extensionality_Ensembles.
    unfold app_ext.
    apply Same_set_Full_set.
    unfold Included. unfold In. intros. clear H0.
    pose proof (H' := satisfies_theory_impl_satisfies_named_axiom H AxDefinedness).
    simpl in H'.
    clear H. rename H' into H.
    unfold satisfies_model in H.
    remember (update_evar_val (nevar "x") m evar_val) as evar_val'.
    specialize (H evar_val' svar_val).
    apply eq_to_Same_set in H.
    unfold Same_set in H. destruct H as [_ H].
    unfold Included in H.
    specialize (H x).
    pose proof (H' := Full_intro (Domain M) x).
    specialize (H H'). clear H'.
    unfold patt_defined in H.
    rewrite -> pattern_interpretation_app_simpl in H.
    rewrite -> pattern_interpretation_sym_simpl in H.
    unfold sym.
    unfold evarn in H.
    rewrite -> pattern_interpretation_free_evar_simpl in H.
    rewrite -> Heqevar_val' in H.
    unfold update_evar_val in H. simpl in H.
    destruct (evar_eqdec (nevar "x") (nevar "x") ).
    2: { contradiction. }
    unfold app_ext in H. unfold In in H.
    destruct H as [m1 [m2 Hm1m2]].
    destruct Hm1m2. destruct H0.
    inversion H0. clear H0. simpl in H2. subst.
    exists m1. exists m2. split. 2: { split. 2: { apply H1. } constructor. }
    rewrite -> pattern_interpretation_sym_simpl. apply H.
  Qed.

  Lemma definedness_not_empty_1 : forall (M : @Model (sig)),
      M ⊨ᵀ theory ->
      forall (phi : Pattern) (evar_val : @EVarVal (sig) M) (svar_val : @SVarVal (sig) M),
        (@pattern_interpretation (sig) M evar_val svar_val phi) <> Empty ->
        (@pattern_interpretation (sig) M evar_val svar_val (patt_defined phi)) = Full.
  Proof.
    intros.
    pose (H' := Not_Empty_Contains_Elements (pattern_interpretation evar_val svar_val phi) H0).
    destruct H'.
    unfold patt_defined.
    rewrite -> pattern_interpretation_app_simpl.
    
    pose proof (H'' := definedness_model_application M evar_val svar_val H x).
    unfold sym in H''.
    apply Extensionality_Ensembles.
    apply Same_set_symmetric.
    apply Same_set_Full_set.
    apply eq_to_Same_set in H''.
    unfold Same_set in H''.
    destruct H'' as [_ H''].
    assert (Hincl: Included (Domain M) (Singleton (Domain M) x) (pattern_interpretation evar_val svar_val phi) ).
    { unfold Included. intros. unfold In in *. inversion H2. subst. assumption.  }

    Check app_ext_monotonic_r.
    pose proof (Hincl' := @app_ext_monotonic_r
                            sig
                            M
                            (pattern_interpretation evar_val svar_val (patt_sym (inj definedness)))
                            (Singleton (Domain M) x)
                            (pattern_interpretation evar_val svar_val phi)
                            Hincl
               ).
    apply Included_transitive with (S2 := app_ext (pattern_interpretation evar_val svar_val (patt_sym (inj definedness))) (Singleton (Domain M) x)). 2: assumption. assumption.

  Qed.

  Lemma definedness_empty_1 : forall (M : @Model (sig)),
      M ⊨ᵀ theory ->
      forall (phi : Pattern) (evar_val : @EVarVal (sig) M) (svar_val : @SVarVal (sig) M),
        @pattern_interpretation sig M evar_val svar_val phi = Empty ->
        @pattern_interpretation sig M evar_val svar_val (patt_defined phi) = Empty.
  Proof.
    intros. unfold patt_defined.
    rewrite -> pattern_interpretation_app_simpl.
    rewrite -> H0.
    apply app_ext_bot_r.
  Qed.

  Theorem modus_tollens: forall (P Q : Prop), (P -> Q) -> ~Q -> ~P.
  Proof. auto. Qed.

  Lemma definedness_empty_2 : forall (M : @Model (sig)),
      M ⊨ᵀ theory ->
      forall (phi : Pattern) (evar_val : @EVarVal (sig) M) (svar_val : @SVarVal (sig) M),
        @pattern_interpretation sig M evar_val svar_val (patt_defined phi) = Empty ->
        @pattern_interpretation sig M evar_val svar_val phi = Empty.
  Proof.
    intros.
    pose proof (H1 := @empty_impl_not_full sig M _ H0).
    pose proof (H2 := modus_tollens _ _ (definedness_not_empty_1 M H phi evar_val svar_val) H1).
    apply NNPP in H2. apply H2.
  Qed.

  Lemma definedness_not_empty_2 : forall (M : @Model (sig)),
      M ⊨ᵀ theory ->
      forall (phi : Pattern) (evar_val : @EVarVal (sig) M) (svar_val : @SVarVal (sig) M),
        @pattern_interpretation (sig) M evar_val svar_val (patt_defined phi) = Full ->
        @pattern_interpretation (sig) M evar_val svar_val phi <> Empty.
  Proof.
    intros.
    pose proof (H1 := full_impl_not_empty H0).
    exact (modus_tollens _ _ (definedness_empty_1 M H phi evar_val svar_val) H1).
  Qed.

  Lemma totality_not_full : forall (M : @Model (sig)),
      M ⊨ᵀ theory ->
      forall (phi : Pattern) (evar_val : @EVarVal (sig) M) (svar_val : @SVarVal (sig) M),
        @pattern_interpretation (sig) M evar_val svar_val phi <> Full ->
        @pattern_interpretation (sig) M evar_val svar_val (patt_total phi) = Empty.
  Proof.
    intros.
    assert (Hnonempty : pattern_interpretation evar_val svar_val (patt_not phi) <> Empty).
    { unfold not. unfold not in H0. intros. rewrite -> pattern_interpretation_not_simpl in H1.
      (* TODO extract these three (or two?) steps into a separate lemmma: swap_compl *)
      apply eq_to_Same_set in H1.
      apply Same_set_Compl in H1.
      apply Extensionality_Ensembles in H1.
      rewrite -> (Same_set_to_eq (Compl_Compl_Ensembles (Domain M) (pattern_interpretation evar_val svar_val phi))) in H1.
      unfold Empty in H1.
      rewrite -> (Same_set_to_eq (@Complement_Empty_is_Full (Domain M) )) in H1.
      apply H0. apply H1.
    }
    unfold patt_total. rewrite -> pattern_interpretation_not_simpl.
    apply Extensionality_Ensembles.
    apply Same_set_Compl.
    rewrite -> (Same_set_to_eq (Compl_Compl_Ensembles (Domain M) (pattern_interpretation evar_val svar_val
                                                                                         (patt_defined (patt_not phi))))).
    unfold Empty.
    rewrite -> (Same_set_to_eq (@Complement_Empty_is_Full (Domain M))).
    apply eq_to_Same_set.
    apply definedness_not_empty_1. apply H. apply Hnonempty.
  Qed.

  Lemma totality_full : forall (M : @Model (sig)),
      M ⊨ᵀ theory ->
      forall (phi : Pattern) (evar_val : @EVarVal (sig) M) (svar_val : @SVarVal (sig) M),
        @pattern_interpretation (sig) M evar_val svar_val phi = Full ->
        @pattern_interpretation (sig) M evar_val svar_val (patt_total phi) = Full.
  Proof.
    intros.
    unfold patt_total.
    rewrite -> pattern_interpretation_not_simpl.
    assert(H1: pattern_interpretation evar_val svar_val (patt_not phi) = Empty).
    { rewrite -> pattern_interpretation_not_simpl.
      rewrite -> H0.
      apply Extensionality_Ensembles.
      apply Complement_Full_is_Empty.
    }

    pose proof (H2 := definedness_empty_1 M H (patt_not phi) evar_val svar_val H1).
    rewrite -> H2.
    apply Extensionality_Ensembles.
    apply Complement_Empty_is_Full.
  Qed.

  Lemma totality_result_empty : forall (M : @Model (sig)),
      M ⊨ᵀ theory ->
      forall (phi : Pattern) (evar_val : @EVarVal (sig) M) (svar_val : @SVarVal (sig) M),
        @pattern_interpretation (sig) M evar_val svar_val (patt_total phi) = Empty ->
        @pattern_interpretation (sig) M evar_val svar_val phi <> Full.
  Proof.
    intros.
    pose proof (H1 := empty_impl_not_full H0).
    pose proof (H2 := modus_tollens _ _ (totality_full M H phi evar_val svar_val) H1).
    apply H2.
  Qed.

  Lemma totality_result_nonempty : forall (M : @Model (sig)),
      M ⊨ᵀ theory ->
      forall (phi : Pattern) (evar_val : @EVarVal (sig) M) (svar_val : @SVarVal (sig) M),
        @pattern_interpretation (sig) M evar_val svar_val (patt_total phi) <> Empty ->
        @pattern_interpretation (sig) M evar_val svar_val phi = Full.
  Proof.
    intros.
    pose proof (H2 := modus_tollens _ _ (totality_not_full M H phi evar_val svar_val) H0).
    apply NNPP in H2. apply H2.
  Qed.
  
  Lemma both_subseteq_imp_eq : forall (M : @Model (sig)),
      M ⊨ᵀ theory ->
      forall (phi1 phi2 : Pattern) (evar_val : @EVarVal (sig) M) (svar_val : @SVarVal (sig) M),
        @pattern_interpretation (sig) M evar_val svar_val (patt_subseteq phi1 phi2) = Full ->
        @pattern_interpretation (sig) M evar_val svar_val (patt_subseteq phi2 phi1) = Full ->
        @pattern_interpretation (sig) M evar_val svar_val (patt_equal phi1 phi2) = Full.
  Proof.
    unfold patt_subseteq. intros.
    apply full_impl_not_empty in H0.
    apply full_impl_not_empty in H1.
    apply (totality_result_nonempty _ H) in H0.
    apply (totality_result_nonempty _ H) in H1.
    unfold patt_equal.
    apply (totality_full _ H).
    unfold "<--->".
    rewrite -> pattern_interpretation_and_simpl.
    rewrite -> H0.
    rewrite -> H1.
    apply Extensionality_Ensembles.
    unfold Full.
    rewrite -> (Same_set_to_eq (Intersection_Full_l _)).
    apply Same_set_refl.
  Qed.

  Lemma equal_impl_both_subseteq : forall (M : @Model (sig)),        
      M ⊨ᵀ theory ->
      forall (phi1 phi2 : Pattern) (evar_val : @EVarVal (sig) M) (svar_val : @SVarVal (sig) M),
        @pattern_interpretation (sig) M evar_val svar_val (patt_equal phi1 phi2) = Full ->
        (
          @pattern_interpretation (sig) M evar_val svar_val (patt_subseteq phi1 phi2) = Full /\
          @pattern_interpretation (sig) M evar_val svar_val (patt_subseteq phi2 phi1) = Full).
  Proof.
    intros.
    unfold patt_equal in H0.
    apply full_impl_not_empty in H0.
    apply (totality_result_nonempty _ H) in H0.
    unfold "<--->" in H0.
    rewrite ->pattern_interpretation_and_simpl in H0.
    apply eq_to_Same_set in H0.
    apply Intersection_eq_Full in H0. destruct H0 as [H1 H2].
    apply Extensionality_Ensembles in H1. apply Extensionality_Ensembles in H2.
    unfold patt_subseteq.
    apply (totality_full _ H) in H1.
    apply (totality_full _ H) in H2.
    split; assumption.
  Qed.

  Lemma subseteq_iff_interpr_subseteq : forall (M : @Model (sig)),
      M ⊨ᵀ theory ->
      forall (phi1 phi2 : Pattern) (evar_val : @EVarVal (sig) M) (svar_val : @SVarVal (sig) M),
        @pattern_interpretation (sig) M evar_val svar_val (patt_subseteq phi1 phi2) = Full <->
        Included (Domain M)
                 (@pattern_interpretation (sig) M evar_val svar_val phi1)
                 (@pattern_interpretation (sig) M evar_val svar_val phi2).
  Proof.
    intros M H phi1 phi2 evar_val svar_val.
    split.
    - intros H0.
      unfold patt_subseteq in H0.
      apply full_impl_not_empty in H0.
      apply (totality_result_nonempty _ H) in H0.
      rewrite -> pattern_interpretation_imp_simpl in H0.
      apply eq_to_Same_set in H0.
      unfold Same_set in H0. destruct H0 as [_ H0].
      unfold Included in *. intros. specialize (H0 x).
      assert (H' : In (Domain M) (Full_set (Domain M)) x).
      { unfold In. constructor. }
      specialize (H0 H'). clear H'.
      unfold In in *. destruct H0; unfold In in H0.
      + unfold Complement in H0. contradiction.
      + apply H0.
    - intros H0.
      unfold patt_subseteq.
      apply (totality_full _ H).
      rewrite -> pattern_interpretation_imp_simpl.
      apply Extensionality_Ensembles.
      apply Same_set_symmetric.
      apply Same_set_Full_set.
      unfold Included in *.
      intros. specialize (H0 x). clear H1.
      destruct (classic (In (Domain M) (pattern_interpretation evar_val svar_val phi1) x)).
      + right. auto.
      + left. unfold In. unfold Complement. assumption.      
  Qed.
  
  Lemma equal_iff_interpr_same : forall (M : @Model (sig)),
      M ⊨ᵀ theory ->
      forall (phi1 phi2 : Pattern) (evar_val : @EVarVal (sig) M) (svar_val : @SVarVal (sig) M),
        @pattern_interpretation (sig) M evar_val svar_val (patt_equal phi1 phi2) = Full <->
        @pattern_interpretation (sig) M evar_val svar_val phi1
        = @pattern_interpretation (sig) M evar_val svar_val phi2.
  Proof.
    intros M H phi1 phi2 evar_val svar_val.
    split.
    - intros H0.
      apply (equal_impl_both_subseteq _ H) in H0.
      destruct H0 as [Hsub1 Hsub2].
      apply (subseteq_iff_interpr_subseteq _ H) in Hsub1.
      apply (subseteq_iff_interpr_subseteq _ H) in Hsub2.
      unfold Same_set.
      apply Extensionality_Ensembles.
      split; assumption.
    - intros H0.
      apply eq_to_Same_set in H0.
      destruct H0 as [Hincl1 Hincl2].
      apply (subseteq_iff_interpr_subseteq _ H) in Hincl1.
      apply (subseteq_iff_interpr_subseteq _ H) in Hincl2.
      auto using both_subseteq_imp_eq.      
  Qed.

  Lemma equal_refl : forall (M : @Model (sig)),
      M ⊨ᵀ theory ->
      forall (phi : Pattern) (evar_val : @EVarVal (sig) M) (svar_val : @SVarVal (sig) M),
        @pattern_interpretation (sig) M evar_val svar_val (patt_equal phi phi) = Full.
  Proof.
    intros.
    apply (equal_iff_interpr_same _ H).
    auto.
  Qed.

  Lemma equal_sym : forall (M : @Model (sig)),
      M ⊨ᵀ theory ->
      forall (phi1 phi2 : Pattern) (evar_val : @EVarVal (sig) M) (svar_val : @SVarVal (sig) M),
        @pattern_interpretation (sig) M evar_val svar_val (patt_equal phi1 phi2) = Full ->
        @pattern_interpretation (sig) M evar_val svar_val (patt_equal phi2 phi1) = Full.
  Proof.
    intros.
    apply (equal_iff_interpr_same _ H).
    apply (equal_iff_interpr_same _ H) in H0.
    symmetry. auto.
  Qed.

  Lemma equal_trans : forall (M : @Model (sig)),
      M ⊨ᵀ theory ->
      forall (phi1 phi2 phi3 : Pattern) (evar_val : @EVarVal (sig) M) (svar_val : @SVarVal (sig) M),
        @pattern_interpretation (sig) M evar_val svar_val (patt_equal phi1 phi2) = Full ->
        @pattern_interpretation (sig) M evar_val svar_val (patt_equal phi2 phi3) = Full ->
        @pattern_interpretation (sig) M evar_val svar_val (patt_equal phi1 phi3) = Full.
  Proof.
    intros.
    apply (equal_iff_interpr_same _ H).
    apply (equal_iff_interpr_same _ H) in H0.
    apply (equal_iff_interpr_same _ H) in H1.
    rewrite -> H0. auto.
  Qed.

  Lemma free_evar_in_patt : forall (M : @Model sig),
      M ⊨ᵀ theory ->
      forall (x : evar)(phi : Pattern) (evar_val : @EVarVal sig M) (svar_val : @SVarVal sig M),
        In (Domain M) (@pattern_interpretation sig M evar_val svar_val phi) (evar_val x) <->
        @pattern_interpretation sig M evar_val svar_val (patt_in (patt_free_evar x) phi) = Full.
  Proof.
    intros M H x phi evar_val svar_val.
    split.
    - intros H0.
      unfold patt_in.
      apply (definedness_not_empty_1 _ H).
      Check Contains_Elements_Not_Empty.
      intros Contra.
      apply eq_to_Same_set in Contra.
      apply Contains_Elements_Not_Empty in Contra. auto.
      exists (evar_val x).
      rewrite -> pattern_interpretation_and_simpl.
      split.
      + rewrite -> pattern_interpretation_free_evar_simpl. constructor.
      + assumption.
    - intros H0.
      unfold patt_in in H0.
      apply (definedness_not_empty_2 _ H) in H0.
      unfold not in H0.
      assert (H0': Same_set _ (pattern_interpretation evar_val svar_val (patt_free_evar x and phi)) Empty -> False).
      { intros Contra. apply H0. apply Extensionality_Ensembles. auto.  }
      apply Not_Empty_Contains_Elements in H0'.
      destruct H0' as [x0 H0'].
      rewrite -> pattern_interpretation_and_simpl in H0'.
      destruct H0'.
      rewrite -> pattern_interpretation_free_evar_simpl in H1.
      unfold In in H1. inversion H1. subst. assumption.
  Qed.

  Lemma T_predicate_defined : forall ϕ, T_predicate theory (patt_defined ϕ).
  Proof.
    intros. unfold T_predicate. intros. unfold M_predicate. intros.
    pose proof (Hlr := classic ( pattern_interpretation ρₑ ρₛ ϕ = Empty )).
    destruct Hlr.
    + apply definedness_empty_1 in H0. right. apply H0. apply H.
    + apply definedness_not_empty_1 in H0. left. apply H0. apply H.
  Qed.

  Lemma T_predicate_total : forall ϕ, T_predicate theory (patt_total ϕ).
  Proof.
    intros. unfold patt_total.
    apply T_predicate_not.
    apply T_predicate_defined.
  Qed.

  Lemma T_predicate_subseteq : forall ϕ₁ ϕ₂, T_predicate theory (patt_subseteq ϕ₁ ϕ₂).
  Proof.
    intros. unfold patt_subseteq. apply T_predicate_total.
  Qed.
  
  Lemma T_predicate_equals : forall ϕ₁ ϕ₂, T_predicate theory (patt_equal ϕ₁ ϕ₂).
  Proof.
    intros. unfold patt_equal. apply T_predicate_total.
  Qed.

  Lemma T_predicate_in : forall ϕ₁ ϕ₂, T_predicate theory (patt_in ϕ₁ ϕ₂).
  Proof.
    intros. unfold patt_equal. apply T_predicate_defined.
  Qed.

  (* defined, total, subseteq, equal, in *)
  Lemma evar_open_defined db x ϕ : evar_open db x (patt_defined ϕ) = patt_defined (evar_open db x ϕ).
  Proof. unfold patt_defined. cbn. auto. Qed.
  Lemma svar_open_defined db x ϕ : svar_open db x (patt_defined ϕ) = patt_defined (svar_open db x ϕ).
  Proof. unfold patt_defined. cbn. auto. Qed.
  
  Lemma evar_open_total db x ϕ : evar_open db x (patt_total ϕ) = patt_total (evar_open db x ϕ).
  Proof. unfold patt_total. autorewrite with ml_db. rewrite -> evar_open_defined. auto. Qed.
  Lemma svar_open_total db x ϕ : svar_open db x (patt_total ϕ) = patt_total (svar_open db x ϕ).
  Proof. unfold patt_total. autorewrite with ml_db. rewrite -> svar_open_defined. auto. Qed.
  
  Lemma evar_open_equal db x ϕ₁ ϕ₂ : evar_open db x (patt_equal ϕ₁ ϕ₂) = patt_equal (evar_open db x ϕ₁) (evar_open db x ϕ₂).
  Proof. unfold patt_equal. rewrite -> evar_open_total. autorewrite with ml_db. auto. Qed.
  Lemma svar_open_equal db x ϕ₁ ϕ₂ : svar_open db x (patt_equal ϕ₁ ϕ₂) = patt_equal (svar_open db x ϕ₁) (svar_open db x ϕ₂).
  Proof. unfold patt_equal. rewrite -> svar_open_total. autorewrite with ml_db. auto. Qed.

  Lemma evar_open_subseteq db x ϕ₁ ϕ₂ : evar_open db x (patt_subseteq ϕ₁ ϕ₂) = patt_subseteq (evar_open db x ϕ₁) (evar_open db x ϕ₂).
  Proof. unfold patt_subseteq. rewrite -> evar_open_total. autorewrite with ml_db. auto. Qed.
  Lemma svar_open_subseteq db x ϕ₁ ϕ₂ : svar_open db x (patt_subseteq ϕ₁ ϕ₂) = patt_subseteq (svar_open db x ϕ₁) (svar_open db x ϕ₂).
  Proof. unfold patt_subseteq. rewrite -> svar_open_total. autorewrite with ml_db. auto. Qed.

  Lemma evar_open_in db x ϕ₁ ϕ₂ : evar_open db x (patt_in ϕ₁ ϕ₂) = patt_in (evar_open db x ϕ₁) (evar_open db x ϕ₂).
  Proof. unfold patt_in. rewrite -> evar_open_defined. autorewrite with ml_db. auto. Qed.
  Lemma svar_open_in db x ϕ₁ ϕ₂ : svar_open db x (patt_in ϕ₁ ϕ₂) = patt_in (svar_open db x ϕ₁) (svar_open db x ϕ₂).
  Proof. unfold patt_in. rewrite -> svar_open_defined. autorewrite with ml_db. auto. Qed.
  
End definedness.

Hint Rewrite ->
@evar_open_defined
  @svar_open_defined
  @evar_open_total
  @svar_open_total
  @evar_open_equal
  @svar_open_equal
  @evar_open_subseteq
  @svar_open_subseteq
  @evar_open_in
  @svar_open_in
  : ml_db.
