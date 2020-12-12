(* In this module we define the definedness symbol and use it to build derived notions
   like totality and equality.
 *)
Require Import Coq.Logic.Classical_Prop.
Require Import MatchingLogic.locally_nameless.
Require Import MatchingLogic.Syntax.
Import MLNotations.

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

  Definition theory : Ensemble Pattern := fun p => exists a, p = axiom a.
  
(*
  Definition satisfies_axioms (M : Model) := forall (ax_name : AxiomName),
      satisfies_model M (axiom ax_name).
 *)

  Lemma theoryAxiom: forall (M : @Model sig), M ⊨ᵀ theory -> forall a, M ⊨ᴹ (axiom a).
  Proof.
    intros. unfold satisfies_theory in H.
    specialize (H (axiom a)). apply H.
    unfold In. unfold theory. exists a. reflexivity.
 Qed.
  
  Lemma definedness_model_application :
    forall (M : @Model sig) (evar_val : @EVarVal sig M) (svar_val : @SVarVal (sig) M),
      M ⊨ᵀ theory ->
      forall (m: Domain M),
        Same_set (Domain M)
                 (Full_set (Domain M))
                 (app_ext (pattern_interpretation evar_val svar_val (sym definedness)) (Singleton (Domain M) m)).
  Proof.
    intros.
    unfold app_ext.
    apply Same_set_Full_set.
    unfold Included. unfold In. intros. clear H0.
    pose proof (H' := theoryAxiom M H AxDefinedness). simpl in H'.
    clear H. rename H' into H.
    unfold satisfies_model in H.
    remember (update_evar_val (nevar "x") m evar_val) as evar_val'.
    specialize (H evar_val' svar_val).
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
    destruct (evar_eq (nevar "x") (nevar "x") ).
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
        ~ Same_set (Domain M)
          (@pattern_interpretation (sig) M evar_val svar_val phi)
          (Empty_set (Domain M)) ->
        Same_set (Domain M)
                 (@pattern_interpretation (sig) M evar_val svar_val (patt_defined phi))
                 (Full_set (Domain M)).
  Proof.
    intros.
    pose (H' := Not_Empty_Contains_Elements (pattern_interpretation evar_val svar_val phi) H0).
    destruct H'.
    unfold patt_defined.
    rewrite -> pattern_interpretation_app_simpl.
    
    pose proof (H'' := definedness_model_application M evar_val svar_val H x).
    unfold sym in H''.
    apply Same_set_symmetric.
    apply Same_set_Full_set.
    unfold Same_set in H''.
    destruct H'' as [H'' _].
    assert (Hincl: Included (Domain M) (Singleton (Domain M) x) (pattern_interpretation evar_val svar_val phi) ).
    { unfold Included. intros. unfold In in *. inversion H2. subst. assumption.  }
    
    pose proof (Hincl' := app_ext_monotonic_r
                            M
                            (pattern_interpretation evar_val svar_val (patt_sym (inj definedness)))
                            (Singleton (Domain M) x)
                            (pattern_interpretation evar_val svar_val phi)
                            Hincl
               ).
    apply Included_transitive with (S2 := app_ext (pattern_interpretation evar_val svar_val (patt_sym (inj definedness))) (Singleton (Domain M) x)). assumption. assumption.

  Qed.

  Lemma definedness_empty_1 : forall (M : @Model (sig)),
      M ⊨ᵀ theory ->
      forall (phi : Pattern) (evar_val : @EVarVal (sig) M) (svar_val : @SVarVal (sig) M),
        Same_set (Domain M) (@pattern_interpretation (sig) M evar_val svar_val phi) (Empty_set (Domain M)) ->
        Same_set (Domain M) (@pattern_interpretation (sig) M evar_val svar_val (patt_defined phi)) (Empty_set (Domain M)).
  Proof.
    intros. unfold patt_defined.
    rewrite -> pattern_interpretation_app_simpl.
    rewrite -> (Same_set_to_eq H0).
    apply app_ext_bot_r.
  Qed.

  Theorem modus_tollens: forall (P Q : Prop), (P -> Q) -> ~Q -> ~P.
  Proof. auto. Qed.

  Lemma definedness_empty_2 : forall (M : @Model (sig)),
      M ⊨ᵀ theory ->
      forall (phi : Pattern) (evar_val : @EVarVal (sig) M) (svar_val : @SVarVal (sig) M),
        Same_set (Domain M) (@pattern_interpretation (sig) M evar_val svar_val (patt_defined phi)) (Empty_set (Domain M)) ->
        Same_set (Domain M) (@pattern_interpretation (sig) M evar_val svar_val phi) (Empty_set (Domain M)).
  Proof.
    intros.
    pose proof (H1 := empty_impl_not_full _ H0).
    pose proof (H2 := modus_tollens _ _ (definedness_not_empty_1 M H phi evar_val svar_val) H1).
    apply NNPP in H2. apply H2.
  Qed.

  Lemma definedness_not_empty_2 : forall (M : @Model (sig)),
      M ⊨ᵀ theory ->
      forall (phi : Pattern) (evar_val : @EVarVal (sig) M) (svar_val : @SVarVal (sig) M),
        Same_set (Domain M)
                 (@pattern_interpretation (sig) M evar_val svar_val (patt_defined phi))
                 (Full_set (Domain M)) ->
        ~ Same_set (Domain M)
          (@pattern_interpretation (sig) M evar_val svar_val phi)
          (Empty_set (Domain M)).
  Proof.
    intros.
    pose proof (H1 := full_impl_not_empty _ H0).
    exact (modus_tollens _ _ (definedness_empty_1 M H phi evar_val svar_val) H1).
  Qed.

  Lemma totality_not_full : forall (M : @Model (sig)),
      M ⊨ᵀ theory ->
      forall (phi : Pattern) (evar_val : @EVarVal (sig) M) (svar_val : @SVarVal (sig) M),
        ~ Same_set (Domain M)
          (@pattern_interpretation (sig) M evar_val svar_val phi)
          (Full_set (Domain M)) ->
        Same_set (Domain M)
                 (@pattern_interpretation (sig) M evar_val svar_val (patt_total phi))
                 (Empty_set (Domain M)).
  Proof.
    intros.
    assert (Hnonempty : ~ Same_set (Domain M) (pattern_interpretation evar_val svar_val (patt_not phi)) (Empty_set (Domain M))).
    { unfold not. unfold not in H0. intros. rewrite -> pattern_interpretation_not_simpl in H1.
      (* TODO extract these three (or two?) steps into a separate lemmma: swap_compl *)
      apply Same_set_Compl in H1.
      rewrite -> (Same_set_to_eq (Compl_Compl_Ensembles (Domain M) (pattern_interpretation evar_val svar_val phi))) in H1.
      rewrite -> (Same_set_to_eq (@Complement_Empty_is_Full (Domain M) )) in H1.
      apply H0. apply H1.
    }
    unfold patt_total. rewrite -> pattern_interpretation_not_simpl.
    apply Same_set_Compl.
    rewrite -> (Same_set_to_eq (Compl_Compl_Ensembles (Domain M) (pattern_interpretation evar_val svar_val
                                                                                (patt_defined (patt_not phi))))).
    rewrite -> (Same_set_to_eq (@Complement_Empty_is_Full (Domain M))).
    apply definedness_not_empty_1. apply H. apply Hnonempty.
  Qed.

  Lemma totality_full : forall (M : @Model (sig)),
      M ⊨ᵀ theory ->
      forall (phi : Pattern) (evar_val : @EVarVal (sig) M) (svar_val : @SVarVal (sig) M),
        Same_set (Domain M)
                 (@pattern_interpretation (sig) M evar_val svar_val phi)
                 (Full_set (Domain M)) ->
        Same_set (Domain M)
                 (@pattern_interpretation (sig) M evar_val svar_val (patt_total phi))
                 (Full_set (Domain M)).
  Proof.
    intros.
    unfold patt_total.
    rewrite -> pattern_interpretation_not_simpl.
    assert(H1: Same_set (Domain M) (pattern_interpretation evar_val svar_val (patt_not phi)) (Empty_set (Domain M))).
    { rewrite -> pattern_interpretation_not_simpl.
      rewrite -> (Same_set_to_eq H0).
      apply Complement_Full_is_Empty.
    }

    pose proof (H2 := definedness_empty_1 M H (patt_not phi) evar_val svar_val H1).
    rewrite -> (Same_set_to_eq H2).
    apply Complement_Empty_is_Full.
  Qed.

  Lemma totality_result_empty : forall (M : @Model (sig)),
      M ⊨ᵀ theory ->
      forall (phi : Pattern) (evar_val : @EVarVal (sig) M) (svar_val : @SVarVal (sig) M),
        Same_set (Domain M)
                 (@pattern_interpretation (sig) M evar_val svar_val (patt_total phi))
                 (Empty_set (Domain M)) ->
        ~ Same_set (Domain M)
          (@pattern_interpretation (sig) M evar_val svar_val phi)
          (Full_set (Domain M)).
  Proof.
    intros.
    pose proof (H1 := empty_impl_not_full _ H0).
    pose proof (H2 := modus_tollens _ _ (totality_full M H phi evar_val svar_val) H1).
    apply H2.
  Qed.

  Lemma totality_result_nonempty : forall (M : @Model (sig)),
      M ⊨ᵀ theory ->
      forall (phi : Pattern) (evar_val : @EVarVal (sig) M) (svar_val : @SVarVal (sig) M),
        ~Same_set (Domain M)
         (@pattern_interpretation (sig) M evar_val svar_val (patt_total phi))
         (Empty_set (Domain M)) ->
        Same_set (Domain M)
                 (@pattern_interpretation (sig) M evar_val svar_val phi)
                 (Full_set (Domain M)).
  Proof.
    intros.
    pose proof (H2 := modus_tollens _ _ (totality_not_full M H phi evar_val svar_val) H0).
    apply NNPP in H2. apply H2.
  Qed.
  
  Lemma both_subseteq_imp_eq : forall (M : @Model (sig)),
      M ⊨ᵀ theory ->
      forall (phi1 phi2 : Pattern) (evar_val : @EVarVal (sig) M) (svar_val : @SVarVal (sig) M),
        Same_set (Domain M)
                 (@pattern_interpretation (sig) M evar_val svar_val (patt_subseteq phi1 phi2))
                 (Full_set (Domain M)) ->
        Same_set (Domain M)
                 (@pattern_interpretation (sig) M evar_val svar_val (patt_subseteq phi2 phi1))
                 (Full_set (Domain M)) ->
        Same_set (Domain M)
                 (@pattern_interpretation (sig) M evar_val svar_val (patt_equal phi1 phi2))
                 (Full_set (Domain M)).
  Proof.
    unfold patt_subseteq. intros.
    apply (full_impl_not_empty _) in H0.
    apply (full_impl_not_empty _) in H1.
    apply (totality_result_nonempty _ H) in H0.
    apply (totality_result_nonempty _ H) in H1.
    unfold patt_equal.
    apply (totality_full _ H).
    unfold "<--->".
    rewrite -> pattern_interpretation_and_simpl.
    rewrite -> (Same_set_to_eq H0).
    rewrite -> (Same_set_to_eq H1).
    rewrite -> (Same_set_to_eq (Intersection_Full_l _)).
    apply Same_set_refl.
  Qed.

  Lemma equal_impl_both_subseteq : forall (M : @Model (sig)),        
      M ⊨ᵀ theory ->
      forall (phi1 phi2 : Pattern) (evar_val : @EVarVal (sig) M) (svar_val : @SVarVal (sig) M),
        Same_set (Domain M)
                 (@pattern_interpretation (sig) M evar_val svar_val (patt_equal phi1 phi2))
                 (Full_set (Domain M)) ->
        (
          Same_set (Domain M)
                   (@pattern_interpretation (sig) M evar_val svar_val (patt_subseteq phi1 phi2))
                   (Full_set (Domain M)) /\
          Same_set (Domain M)
                   (@pattern_interpretation (sig) M evar_val svar_val (patt_subseteq phi2 phi1))
                   (Full_set (Domain M))).
  Proof.
    intros.
    unfold patt_equal in H0.
    apply full_impl_not_empty in H0.
    apply (totality_result_nonempty _ H) in H0.
    unfold "<--->" in H0.
    rewrite ->pattern_interpretation_and_simpl in H0.
    apply Intersection_eq_Full in H0. destruct H0 as [H1 H2].
    unfold patt_subseteq.
    apply (totality_full _ H) in H1.
    apply (totality_full _ H) in H2.
    split; assumption.
  Qed.

  Lemma subseteq_impl_interpr_subseteq : forall (M : @Model (sig)),
      M ⊨ᵀ theory ->
      forall (phi1 phi2 : Pattern) (evar_val : @EVarVal (sig) M) (svar_val : @SVarVal (sig) M),
        Same_set (Domain M)
                 (@pattern_interpretation (sig) M evar_val svar_val (patt_subseteq phi1 phi2))
                 (Full_set (Domain M)) ->
        Included (Domain M)
                 (@pattern_interpretation (sig) M evar_val svar_val phi1)
                 (@pattern_interpretation (sig) M evar_val svar_val phi2).
  Proof.
    intros.
    unfold patt_subseteq in H0.
    apply full_impl_not_empty in H0.
    apply (totality_result_nonempty _ H) in H0.
    rewrite -> pattern_interpretation_imp_simpl in H0.
    unfold Same_set in H0. destruct H0 as [_ H0].
    unfold Included in *. intros. specialize (H0 x).
    assert (H' : In (Domain M) (Full_set (Domain M)) x).
    { unfold In. constructor. }
    specialize (H0 H'). clear H'.
    unfold In in *. destruct H0; unfold In in H0.
    + unfold Complement in H0. contradiction.
    + apply H0.
  Qed.

  Lemma interpr_subseteq_impl_subseteq : forall (M : @Model (sig)),
      M ⊨ᵀ theory ->
      forall (phi1 phi2 : Pattern) (evar_val : @EVarVal (sig) M) (svar_val : @SVarVal (sig) M),
        Included (Domain M)
                 (@pattern_interpretation (sig) M evar_val svar_val phi1)
                 (@pattern_interpretation (sig) M evar_val svar_val phi2) ->
        Same_set (Domain M)
                 (@pattern_interpretation (sig) M evar_val svar_val (patt_subseteq phi1 phi2))
                 (Full_set (Domain M)).
  Proof.
    intros.
    unfold patt_subseteq.
    apply (totality_full _ H).
    rewrite -> pattern_interpretation_imp_simpl.
    apply Same_set_symmetric.
    apply Same_set_Full_set.
    unfold Included in *.
    intros. specialize (H0 x). clear H1.
    destruct (classic (In (Domain M) (pattern_interpretation evar_val svar_val phi1) x)).
    + right. auto.
    + left. unfold In. unfold Complement. assumption.
  Qed.
  
  Lemma equal_impl_interpr_same : forall (M : @Model (sig)),
      M ⊨ᵀ theory ->
      forall (phi1 phi2 : Pattern) (evar_val : @EVarVal (sig) M) (svar_val : @SVarVal (sig) M),
        Same_set (Domain M)
                 (@pattern_interpretation (sig) M evar_val svar_val (patt_equal phi1 phi2))
                 (Full_set (Domain M)) ->
        Same_set (Domain M)
                 (@pattern_interpretation (sig) M evar_val svar_val phi1)
                 (@pattern_interpretation (sig) M evar_val svar_val phi2).
  Proof.
    intros.
    apply (equal_impl_both_subseteq _ H) in H0.
    destruct H0 as [Hsub1 Hsub2].
    apply (subseteq_impl_interpr_subseteq _ H) in Hsub1.
    apply (subseteq_impl_interpr_subseteq _ H) in Hsub2.
    unfold Same_set.
    split; assumption.
  Qed.

  Lemma interpr_same_impl_equal : forall (M : @Model (sig)),
      M ⊨ᵀ theory ->
      forall (phi1 phi2 : Pattern) (evar_val : @EVarVal (sig) M) (svar_val : @SVarVal (sig) M),
        Same_set (Domain M)
                 (@pattern_interpretation (sig) M evar_val svar_val phi1)
                 (@pattern_interpretation (sig) M evar_val svar_val phi2) ->
        Same_set (Domain M)
                 (@pattern_interpretation (sig) M evar_val svar_val (patt_equal phi1 phi2))
                 (Full_set (Domain M)).
  Proof.
    intros. unfold Same_set in H0.
    destruct H0 as [Hincl1 Hincl2].
    apply (interpr_subseteq_impl_subseteq _ H) in Hincl1.
    apply (interpr_subseteq_impl_subseteq _ H) in Hincl2.
    auto using both_subseteq_imp_eq.
  Qed.

  Lemma equal_refl : forall (M : @Model (sig)),
      M ⊨ᵀ theory ->
      forall (phi : Pattern) (evar_val : @EVarVal (sig) M) (svar_val : @SVarVal (sig) M),
        Same_set (Domain M)
                 (@pattern_interpretation (sig) M evar_val svar_val (patt_equal phi phi))
                 (Full_set (Domain M)).
  Proof.
    intros.
    apply (interpr_same_impl_equal _ H).
    apply Same_set_refl.
  Qed.

  Lemma equal_sym : forall (M : @Model (sig)),
      M ⊨ᵀ theory ->
      forall (phi1 phi2 : Pattern) (evar_val : @EVarVal (sig) M) (svar_val : @SVarVal (sig) M),
        Same_set (Domain M)
                 (@pattern_interpretation (sig) M evar_val svar_val (patt_equal phi1 phi2))
                 (Full_set (Domain M)) ->
        Same_set (Domain M)
                 (@pattern_interpretation (sig) M evar_val svar_val (patt_equal phi2 phi1))
                 (Full_set (Domain M)).
  Proof.
    intros.
    apply (interpr_same_impl_equal _ H).
    apply (equal_impl_interpr_same _ H) in H0.
    apply Same_set_symmetric.
    assumption.
  Qed.

  Lemma equal_trans : forall (M : @Model (sig)),
      M ⊨ᵀ theory ->
      forall (phi1 phi2 phi3 : Pattern) (evar_val : @EVarVal (sig) M) (svar_val : @SVarVal (sig) M),
        Same_set (Domain M)
                 (@pattern_interpretation (sig) M evar_val svar_val (patt_equal phi1 phi2))
                 (Full_set (Domain M)) ->
        Same_set (Domain M)
                 (@pattern_interpretation (sig) M evar_val svar_val (patt_equal phi2 phi3))
                 (Full_set (Domain M)) ->
        Same_set (Domain M)
                 (@pattern_interpretation (sig) M evar_val svar_val (patt_equal phi1 phi3))
                 (Full_set (Domain M)).
  Proof.
    intros.
    apply (interpr_same_impl_equal _ H).
    apply (equal_impl_interpr_same _ H) in H0.
    apply (equal_impl_interpr_same _ H) in H1.
    eauto using Same_set_transitive.
  Qed.

  Lemma free_evar_in_patt_1 : forall (M : @Model sig),
      M ⊨ᵀ theory ->
      forall (x : evar)(phi : Pattern) (evar_val : @EVarVal sig M) (svar_val : @SVarVal sig M),
        In (Domain M) (@pattern_interpretation sig M evar_val svar_val phi) (evar_val x) ->
        Same_set (Domain M)
                 (@pattern_interpretation sig M evar_val svar_val (patt_in (patt_free_evar x) phi))
                 (Full_set (Domain M)).
  Proof.
    intros.
    unfold patt_in.
    apply (definedness_not_empty_1 _ H).
    apply Contains_Elements_Not_Empty.
    exists (evar_val x).
    rewrite -> pattern_interpretation_and_simpl.
    split.
    + rewrite -> pattern_interpretation_free_evar_simpl. constructor.
    + assumption.
  Qed.
  

  Lemma free_evar_in_patt_2 : forall (M : @Model sig),
      M ⊨ᵀ theory ->
      forall (x : evar)(phi : Pattern) (evar_val : @EVarVal sig M) (svar_val : @SVarVal sig M),
        Same_set (Domain M)
                 (@pattern_interpretation sig M evar_val svar_val (patt_in (patt_free_evar x) phi))
                 (Full_set (Domain M)) ->
        In (Domain M) (@pattern_interpretation sig M evar_val svar_val phi) (evar_val x).
  Proof.
    intros.
    unfold patt_in in H0.
    apply (definedness_not_empty_2 _ H) in H0.
    apply Not_Empty_Contains_Elements in H0.
    destruct H0.
    rewrite -> pattern_interpretation_and_simpl in H0.
    destruct H0.
    rewrite -> pattern_interpretation_free_evar_simpl in H0.
    unfold In in H0. inversion H0. subst. assumption.
  Qed.

  Lemma T_predicate_defined : forall ϕ, T_predicate theory (patt_defined ϕ).
  Proof.
    intros. unfold T_predicate. intros. unfold M_predicate. intros.
    pose proof (Hlr := classic (Same_set (Domain M) (pattern_interpretation ρₑ ρₛ ϕ) (Empty_set (Domain M)))).
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
  
End definedness.
