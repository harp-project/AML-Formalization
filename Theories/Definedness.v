(* In this module we define the definedness symbol and use it to build derived notions
   like totality and equality. The definitions are reusable from other modules,
   as is demonstrated in the module `test_Definedness` (TODO).
   TODO: include the axiom for definedness and prove some theorems about it.
 *)
Require Import locally_nameless.
Require Import ML.Signature.
Require Import Coq.Logic.Classical_Prop.
Import MLNotations.

Import ML.Signature.

(* We have only one symbol *)
Inductive Symbols := definedness.

Section definedness.
  Context {sig : Signature}.

  Class Syntax(*(sig : Signature)*) :=
    { (*sig: Signature;*)
    (* 'Symbols' are a 'subset' of all the symbols from the signature *)
    inj: Symbols -> symbols sig;
    (* TODO make it injective? *)
    (* for convenience *)
    }.  

  Context {self : Syntax}.

  Let Pattern : Type := @locally_nameless.Pattern sig.

  Definition patt_defined (phi : Pattern) : Pattern :=
    patt_sym (inj definedness) $ phi.
  
  Definition patt_total (phi: Pattern) : Pattern :=
    patt_not (patt_defined (patt_not phi)).

  Definition patt_subseteq (phi1 phi2 : Pattern) : Pattern :=
    patt_total (phi1 --> phi2).
  
  Definition patt_equal (phi1 phi2 : Pattern) : Pattern :=
    patt_total (phi1 <--> phi2).

  Let sym (s : Symbols) : Pattern :=
    @patt_sym sig (inj s).
  
  Let evar (name : string) : Pattern :=
    @patt_free_evar sig (nevar (variables sig) name).

  Definition definedness_axiom := patt_defined (evar "x").

  Lemma definedness_model_application :
    forall (M : @Model sig) (evar_val : @EVarVal sig M) (svar_val : @SVarVal (sig) M),
      satisfies_model M definedness_axiom ->
      forall (m: Domain M),
        Same_set (Domain M)
                 (Full_set (Domain M))
                 (pointwise_ext (ext_valuation evar_val svar_val (sym definedness)) (Singleton (Domain M) m)).
  Proof.
    intros.
    unfold pointwise_ext.
    apply Same_set_Full_set.
    unfold Included. unfold In. intros. clear H0.

    unfold satisfies_model in H. unfold definedness_axiom in H.
    remember (update_evar_val (nevar (variables (sig)) "x") m evar_val) as evar_val'.
    specialize (H evar_val' svar_val).
    unfold Same_set in H. destruct H as [_ H].
    unfold Included in H.
    specialize (H x).
    pose proof (H' := Full_intro (Domain M) x).
    specialize (H H'). clear H'.
    unfold patt_defined in H.
    rewrite -> ext_valuation_app_simpl in H.
    rewrite -> ext_valuation_sym_simpl in H.
    unfold sym.
    unfold evar in H.
    rewrite -> ext_valuation_free_evar_simpl in H.
    rewrite -> Heqevar_val' in H.
    unfold update_evar_val in H. simpl in H.
    unfold locally_nameless.eq_evar_name in H.
    destruct (evar_eq (variables (sig)) (nevar (variables (sig)) "x") (nevar (variables (sig)) "x") ).
    2: { contradiction. }
    unfold pointwise_ext in H. unfold In in H.
    destruct H as [m1 [m2 Hm1m2]].
    destruct Hm1m2. destruct H0.
    inversion H0. clear H0. subst.
    exists m1. exists m2. split. 2: { split. 2: { apply H1. } constructor. }
    rewrite -> ext_valuation_sym_simpl. apply H.
  Qed.
  


  Lemma definedness_not_empty_1 : forall (M : @Model (sig)),
      satisfies_model M definedness_axiom ->
      forall (phi : Pattern) (evar_val : @EVarVal (sig) M) (svar_val : @SVarVal (sig) M),
        ~ Same_set (Domain M)
          (@ext_valuation (sig) M evar_val svar_val phi)
          (Empty_set (Domain M)) ->
        Same_set (Domain M)
                 (@ext_valuation (sig) M evar_val svar_val (patt_defined phi))
                 (Full_set (Domain M)).
  Proof.
    intros.
    pose (H' := Not_Empty_Contains_Elements (ext_valuation evar_val svar_val phi) H0).
    destruct H'.
    unfold patt_defined.
    rewrite -> ext_valuation_app_simpl.
    
    pose proof (H'' := definedness_model_application M evar_val svar_val H x).
    unfold sym in H''.
    apply Same_set_symmetric.
    apply Same_set_Full_set.
    unfold Same_set in H''.
    destruct H'' as [H'' _].
    assert (Hincl: Included (Domain M) (Singleton (Domain M) x) (ext_valuation evar_val svar_val phi) ).
    { unfold Included. intros. unfold In in *. inversion H2. subst. assumption.  }
    
    pose proof (Hincl' := pointwise_ext_monotonic_r
                            M
                            (ext_valuation evar_val svar_val (patt_sym (inj definedness)))
                            (Singleton (Domain M) x)
                            (ext_valuation evar_val svar_val phi)
                            Hincl
               ).
    apply Included_transitive with (S2 := pointwise_ext (ext_valuation evar_val svar_val (patt_sym (inj definedness))) (Singleton (Domain M) x)). assumption. assumption.

  Qed.

  Lemma definedness_empty_1 : forall (M : @Model (sig)),
      satisfies_model M definedness_axiom -> (* we do not need this *)
      forall (phi : Pattern) (evar_val : @EVarVal (sig) M) (svar_val : @SVarVal (sig) M),
        Same_set (Domain M) (@ext_valuation (sig) M evar_val svar_val phi) (Empty_set (Domain M)) ->
        Same_set (Domain M) (@ext_valuation (sig) M evar_val svar_val (patt_defined phi)) (Empty_set (Domain M)).
  Proof.
    intros. unfold patt_defined.
    rewrite -> ext_valuation_app_simpl.
    rewrite -> (Same_set_to_eq H0).
    apply pointwise_ext_bot_r.
  Qed.

  Theorem modus_tollens: forall (P Q : Prop), (P -> Q) -> ~Q -> ~P.
  Proof. auto. Qed.

  Lemma definedness_empty_2 : forall (M : @Model (sig)),
      satisfies_model M definedness_axiom ->
      forall (phi : Pattern) (evar_val : @EVarVal (sig) M) (svar_val : @SVarVal (sig) M),
        Same_set (Domain M) (@ext_valuation (sig) M evar_val svar_val (patt_defined phi)) (Empty_set (Domain M)) ->
        Same_set (Domain M) (@ext_valuation (sig) M evar_val svar_val phi) (Empty_set (Domain M)).
  Proof.
    intros.
    pose proof (H1 := empty_impl_not_full _ H0).
    pose proof (H2 := modus_tollens _ _ (definedness_not_empty_1 M H phi evar_val svar_val) H1).
    apply NNPP in H2. apply H2.
  Qed.

  Lemma definedness_not_empty_2 : forall (M : @Model (sig)),
      satisfies_model M definedness_axiom ->
      forall (phi : Pattern) (evar_val : @EVarVal (sig) M) (svar_val : @SVarVal (sig) M),
        Same_set (Domain M)
                 (@ext_valuation (sig) M evar_val svar_val (patt_defined phi))
                 (Full_set (Domain M)) ->
        ~ Same_set (Domain M)
          (@ext_valuation (sig) M evar_val svar_val phi)
          (Empty_set (Domain M)).
  Proof.
    intros.
    pose proof (H1 := full_impl_not_empty _ H0).
    exact (modus_tollens _ _ (definedness_empty_1 M H phi evar_val svar_val) H1).
  Qed.

  Lemma totality_not_full : forall (M : @Model (sig)),
      satisfies_model M definedness_axiom ->
      forall (phi : Pattern) (evar_val : @EVarVal (sig) M) (svar_val : @SVarVal (sig) M),
        ~ Same_set (Domain M)
          (@ext_valuation (sig) M evar_val svar_val phi)
          (Full_set (Domain M)) ->
        Same_set (Domain M)
                 (@ext_valuation (sig) M evar_val svar_val (patt_total phi))
                 (Empty_set (Domain M)).
  Proof.
    intros.
    assert (Hnonempty : ~ Same_set (Domain M) (ext_valuation evar_val svar_val (patt_not phi)) (Empty_set (Domain M))).
    { unfold not. unfold not in H0. intros. rewrite -> ext_valuation_not_simpl in H1.
      (* TODO extract these three (or two?) steps into a separate lemmma: swap_compl *)
      apply Same_set_Compl in H1.
      rewrite -> (Same_set_to_eq (Compl_Compl_Ensembles (Domain M) (ext_valuation evar_val svar_val phi))) in H1.
      rewrite -> (Same_set_to_eq (@Complement_Empty_is_Full (Domain M) )) in H1.
      apply H0. apply H1.
    }
    unfold patt_total. rewrite -> ext_valuation_not_simpl.
    apply Same_set_Compl.
    rewrite -> (Same_set_to_eq (Compl_Compl_Ensembles (Domain M) (ext_valuation evar_val svar_val
                                                                                (patt_defined (patt_not phi))))).
    rewrite -> (Same_set_to_eq (@Complement_Empty_is_Full (Domain M))).
    apply definedness_not_empty_1. apply H. apply Hnonempty.
  Qed.

  Lemma totality_full : forall (M : @Model (sig)),
      satisfies_model M definedness_axiom ->
      forall (phi : Pattern) (evar_val : @EVarVal (sig) M) (svar_val : @SVarVal (sig) M),
        Same_set (Domain M)
                 (@ext_valuation (sig) M evar_val svar_val phi)
                 (Full_set (Domain M)) ->
        Same_set (Domain M)
                 (@ext_valuation (sig) M evar_val svar_val (patt_total phi))
                 (Full_set (Domain M)).
  Proof.
    intros.
    unfold patt_total.
    rewrite -> ext_valuation_not_simpl.
    assert(H1: Same_set (Domain M) (ext_valuation evar_val svar_val (patt_not phi)) (Empty_set (Domain M))).
    { rewrite -> ext_valuation_not_simpl.
      rewrite -> (Same_set_to_eq H0).
      apply Complement_Full_is_Empty.
    }

    pose proof (H2 := definedness_empty_1 M H (patt_not phi) evar_val svar_val H1).
    rewrite -> (Same_set_to_eq H2).
    apply Complement_Empty_is_Full.
  Qed.

  Lemma totality_result_empty : forall (M : @Model (sig)),
      satisfies_model M definedness_axiom ->
      forall (phi : Pattern) (evar_val : @EVarVal (sig) M) (svar_val : @SVarVal (sig) M),
        Same_set (Domain M)
                 (@ext_valuation (sig) M evar_val svar_val (patt_total phi))
                 (Empty_set (Domain M)) ->
        ~ Same_set (Domain M)
          (@ext_valuation (sig) M evar_val svar_val phi)
          (Full_set (Domain M)).
  Proof.
    intros.
    pose proof (H1 := empty_impl_not_full _ H0).
    pose proof (H2 := modus_tollens _ _ (totality_full M H phi evar_val svar_val) H1).
    apply H2.
  Qed.

  Lemma totality_result_nonempty : forall (M : @Model (sig)),
      satisfies_model M definedness_axiom ->
      forall (phi : Pattern) (evar_val : @EVarVal (sig) M) (svar_val : @SVarVal (sig) M),
        ~Same_set (Domain M)
         (@ext_valuation (sig) M evar_val svar_val (patt_total phi))
         (Empty_set (Domain M)) ->
        Same_set (Domain M)
                 (@ext_valuation (sig) M evar_val svar_val phi)
                 (Full_set (Domain M)).
  Proof.
    intros.
    pose proof (H2 := modus_tollens _ _ (totality_not_full M H phi evar_val svar_val) H0).
    apply NNPP in H2. apply H2.
  Qed.
  
  Lemma both_subseteq_imp_eq : forall (M : @Model (sig)),
      satisfies_model M definedness_axiom ->
      forall (phi1 phi2 : Pattern) (evar_val : @EVarVal (sig) M) (svar_val : @SVarVal (sig) M),
        Same_set (Domain M)
                 (@ext_valuation (sig) M evar_val svar_val (patt_subseteq phi1 phi2))
                 (Full_set (Domain M)) ->
        Same_set (Domain M)
                 (@ext_valuation (sig) M evar_val svar_val (patt_subseteq phi2 phi1))
                 (Full_set (Domain M)) ->
        Same_set (Domain M)
                 (@ext_valuation (sig) M evar_val svar_val (patt_equal phi1 phi2))
                 (Full_set (Domain M)).
  Proof.
    unfold patt_subseteq. intros.
    apply (full_impl_not_empty _) in H0.
    apply (full_impl_not_empty _) in H1.
    apply (totality_result_nonempty _ H) in H0.
    apply (totality_result_nonempty _ H) in H1.
    unfold patt_equal.
    apply (totality_full _ H).
    unfold "<-->".
    rewrite -> ext_valuation_and_simpl.
    rewrite -> (Same_set_to_eq H0).
    rewrite -> (Same_set_to_eq H1).
    rewrite -> (Same_set_to_eq (Intersection_Full_l _)).
    apply Same_set_refl.
  Qed.

  Lemma equal_impl_both_subseteq : forall (M : @Model (sig)),        
      satisfies_model M definedness_axiom ->
      forall (phi1 phi2 : Pattern) (evar_val : @EVarVal (sig) M) (svar_val : @SVarVal (sig) M),
        Same_set (Domain M)
                 (@ext_valuation (sig) M evar_val svar_val (patt_equal phi1 phi2))
                 (Full_set (Domain M)) ->
        (
          Same_set (Domain M)
                   (@ext_valuation (sig) M evar_val svar_val (patt_subseteq phi1 phi2))
                   (Full_set (Domain M)) /\
          Same_set (Domain M)
                   (@ext_valuation (sig) M evar_val svar_val (patt_subseteq phi2 phi1))
                   (Full_set (Domain M))).
  Proof.
    intros.
    unfold patt_equal in H0.
    apply full_impl_not_empty in H0.
    apply (totality_result_nonempty _ H) in H0.
    unfold "<-->" in H0.
    rewrite ->ext_valuation_and_simpl in H0.
    apply Intersection_eq_Full in H0. destruct H0 as [H1 H2].
    unfold patt_subseteq.
    apply (totality_full _ H) in H1.
    apply (totality_full _ H) in H2.
    split; assumption.
  Qed.

  Lemma subseteq_impl_interpr_subseteq : forall (M : @Model (sig)),
      satisfies_model M definedness_axiom ->
      forall (phi1 phi2 : Pattern) (evar_val : @EVarVal (sig) M) (svar_val : @SVarVal (sig) M),
        Same_set (Domain M)
                 (@ext_valuation (sig) M evar_val svar_val (patt_subseteq phi1 phi2))
                 (Full_set (Domain M)) ->
        Included (Domain M)
                 (@ext_valuation (sig) M evar_val svar_val phi1)
                 (@ext_valuation (sig) M evar_val svar_val phi2).
  Proof.
    intros.
    unfold patt_subseteq in H0.
    apply full_impl_not_empty in H0.
    apply (totality_result_nonempty _ H) in H0.
    rewrite -> ext_valuation_imp_simpl in H0.
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
      satisfies_model M definedness_axiom ->
      forall (phi1 phi2 : Pattern) (evar_val : @EVarVal (sig) M) (svar_val : @SVarVal (sig) M),
        Included (Domain M)
                 (@ext_valuation (sig) M evar_val svar_val phi1)
                 (@ext_valuation (sig) M evar_val svar_val phi2) ->
        Same_set (Domain M)
                 (@ext_valuation (sig) M evar_val svar_val (patt_subseteq phi1 phi2))
                 (Full_set (Domain M)).
  Proof.
    intros.
    unfold patt_subseteq.
    apply (totality_full _ H).
    rewrite -> ext_valuation_imp_simpl.
    apply Same_set_symmetric.
    apply Same_set_Full_set.
    unfold Included in *.
    intros. specialize (H0 x). clear H1.
    destruct (classic (In (Domain M) (ext_valuation evar_val svar_val phi1) x)).
    + right. auto.
    + left. unfold In. unfold Complement. assumption.
  Qed.
  
  Lemma equal_impl_interpr_same : forall (M : @Model (sig)),
      satisfies_model M definedness_axiom ->
      forall (phi1 phi2 : Pattern) (evar_val : @EVarVal (sig) M) (svar_val : @SVarVal (sig) M),
        Same_set (Domain M)
                 (@ext_valuation (sig) M evar_val svar_val (patt_equal phi1 phi2))
                 (Full_set (Domain M)) ->
        Same_set (Domain M)
                 (@ext_valuation (sig) M evar_val svar_val phi1)
                 (@ext_valuation (sig) M evar_val svar_val phi2).
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
      satisfies_model M definedness_axiom ->
      forall (phi1 phi2 : Pattern) (evar_val : @EVarVal (sig) M) (svar_val : @SVarVal (sig) M),
        Same_set (Domain M)
                 (@ext_valuation (sig) M evar_val svar_val phi1)
                 (@ext_valuation (sig) M evar_val svar_val phi2) ->
        Same_set (Domain M)
                 (@ext_valuation (sig) M evar_val svar_val (patt_equal phi1 phi2))
                 (Full_set (Domain M)).
  Proof.
    intros. unfold Same_set in H0.
    destruct H0 as [Hincl1 Hincl2].
    apply (interpr_subseteq_impl_subseteq _ H) in Hincl1.
    apply (interpr_subseteq_impl_subseteq _ H) in Hincl2.
    auto using both_subseteq_imp_eq.
  Qed.

  Lemma equal_refl : forall (M : @Model (sig)),
      satisfies_model M definedness_axiom ->
      forall (phi : Pattern) (evar_val : @EVarVal (sig) M) (svar_val : @SVarVal (sig) M),
        Same_set (Domain M)
                 (@ext_valuation (sig) M evar_val svar_val (patt_equal phi phi))
                 (Full_set (Domain M)).
  Proof.
    intros.
    apply (interpr_same_impl_equal _ H).
    apply Same_set_refl.
  Qed.

  Lemma equal_sym : forall (M : @Model (sig)),
      satisfies_model M definedness_axiom ->
      forall (phi1 phi2 : Pattern) (evar_val : @EVarVal (sig) M) (svar_val : @SVarVal (sig) M),
        Same_set (Domain M)
                 (@ext_valuation (sig) M evar_val svar_val (patt_equal phi1 phi2))
                 (Full_set (Domain M)) ->
        Same_set (Domain M)
                 (@ext_valuation (sig) M evar_val svar_val (patt_equal phi2 phi1))
                 (Full_set (Domain M)).
  Proof.
    intros.
    apply (interpr_same_impl_equal _ H).
    apply (equal_impl_interpr_same _ H) in H0.
    apply Same_set_symmetric.
    assumption.
  Qed.

  Lemma equal_trans : forall (M : @Model (sig)),
      satisfies_model M definedness_axiom ->
      forall (phi1 phi2 phi3 : Pattern) (evar_val : @EVarVal (sig) M) (svar_val : @SVarVal (sig) M),
        Same_set (Domain M)
                 (@ext_valuation (sig) M evar_val svar_val (patt_equal phi1 phi2))
                 (Full_set (Domain M)) ->
        Same_set (Domain M)
                 (@ext_valuation (sig) M evar_val svar_val (patt_equal phi2 phi3))
                 (Full_set (Domain M)) ->
        Same_set (Domain M)
                 (@ext_valuation (sig) M evar_val svar_val (patt_equal phi1 phi3))
                 (Full_set (Domain M)).
  Proof.
    intros.
    apply (interpr_same_impl_equal _ H).
    apply (equal_impl_interpr_same _ H) in H0.
    apply (equal_impl_interpr_same _ H) in H1.
    eauto using Same_set_transitive.
  Qed.  
  
End definedness.
