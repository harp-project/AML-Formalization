From MatchingLogic Require Export Surj
                                  monotonic.

Import MatchingLogic.Substitution.Notations.

Section isomorphism.
  Open Scope ml_scope.



  (* Polymorphic Cumulative *)
  Record ModelIsomorphism {Σ : Signature} {M₁ M₂ : Model} : Type := mkModelIsomorphism
      {
          mi_f : (Domain M₁) -> (Domain M₂) ;
          mi_inj :> Inj (=) (=) mi_f ;
          mi_surj :> Surj' (=) mi_f ;
          mi_sym : ∀ (s : symbols),
              mi_f <$> (sym_interp M₁ s) ≡ sym_interp M₂ s ;
          mi_app : ∀ (x y : Domain M₁),
              mi_f <$> (@app_interp Σ M₁ x y) ≡ @app_interp Σ M₂ (mi_f x) (mi_f y) ;
      }.

  Definition isom {Σ : Signature} : relation Model :=
      λ M₁ M₂, ∃ (r : @ModelIsomorphism _ M₁ M₂), True.

  Definition ModelIsomorphism_refl {Σ : Signature} (M : Model) : @ModelIsomorphism _ M M.
  Proof.
      exists Datatypes.id.
      {
          apply _.
      }
      {
          apply _.
      }
      {
          intros s.
          unfold fmap.
          with_strategy transparent [propset_fmap] unfold propset_fmap.
          unfold Datatypes.id.
          set_solver.
      }
      {
          intros x y.
          unfold fmap.
          with_strategy transparent [propset_fmap] unfold propset_fmap.
          unfold Datatypes.id.
          set_solver.
      }
  Defined.

  Definition ModelIsomorphism_sym {Σ : Signature} (M₁ M₂ : Model) (i : @ModelIsomorphism _ M₁ M₂)
  : @ModelIsomorphism _ M₂ M₁.
  Proof.
      destruct i. destruct mi_surj0.
      exists surj'_inv.
      {
          intros x y H. unfold Inj in mi_inj0.
          rewrite -[x]surj'_pf. rewrite -[y]surj'_pf.
          f_equal. apply mi_inj0. f_equal. assumption.
      }
      {
          unfold Inj in mi_inj0.
          exists mi_f0. intros a.
          apply mi_inj0.
          rewrite surj'_pf. reflexivity.
      }
      {
          intros x y.
          unfold fmap in *.
          with_strategy transparent [propset_fmap] unfold propset_fmap in *.
          rewrite elem_of_PropSet.
          specialize (mi_sym0 x).
          rewrite set_equiv_subseteq in mi_sym0.
          destruct mi_sym0 as [mi_sym1 mi_sym2].
          rewrite elem_of_subseteq in mi_sym1.
          rewrite elem_of_subseteq in mi_sym2.
          setoid_rewrite elem_of_PropSet in mi_sym1.
          setoid_rewrite elem_of_PropSet in mi_sym2.
          split.
          {
              intros [b [Hb1 Hb2] ].
              subst.
              specialize (mi_sym2 b Hb2).
              destruct mi_sym2 as [a [Ha1 Ha2] ].
              subst.
              cut (surj'_inv (mi_f0 a) = a).
              {
                  intros Htmp. rewrite Htmp. exact Ha2.
              }
              apply mi_inj0.
              rewrite surj'_pf.
              reflexivity.
          }
          {
              intros Hy.
              specialize (mi_sym1 (mi_f0 y)).
              ospecialize* mi_sym1.
              {
                  exists y.
                  split;[reflexivity|].
                  exact Hy.
              }
              exists (mi_f0 y).
              split.
              {
                  apply mi_inj0.
                  rewrite surj'_pf.
                  reflexivity.
              }
              {
                  exact mi_sym1.
              }
          }
      }
      {
          intros x y.
          unfold fmap in *.
          with_strategy transparent [propset_fmap] unfold propset_fmap in *.
          specialize (mi_app0 (surj'_inv x) (surj'_inv y)).
          do 2 rewrite surj'_pf in mi_app0.
          rewrite set_equiv_subseteq in mi_app0.
          rewrite elem_of_subseteq in mi_app0.
          rewrite elem_of_subseteq in mi_app0.
          setoid_rewrite elem_of_PropSet in mi_app0.
          destruct mi_app0 as [mi_app1 mi_app2].
          rewrite set_equiv_subseteq.
          do 2 rewrite elem_of_subseteq.
          setoid_rewrite elem_of_PropSet.
          split.
          {
              intros a [b [Hb1 Hb2] ].
              subst.
              specialize (mi_app2 b Hb2).
              destruct mi_app2 as [a [Ha1 Ha2] ].
              subst.
              cut (surj'_inv (mi_f0 a) = a).
              {
                  intros Htmp. rewrite Htmp. exact Ha2.
              }
              apply mi_inj0.
              rewrite surj'_pf.
              reflexivity.
          }
          {
              intros a Ha.
              exists (mi_f0 a).
              split.
              {
                  apply mi_inj0.
                  rewrite surj'_pf.
                  reflexivity.
              }
              {
                  apply mi_app1.
                  exists a.
                  split;[reflexivity|].
                  exact Ha.
              }
          }
      }
  Defined.

  Program Definition ModelIsomorphism_trans {Σ : Signature} (M₁ M₂ M₃ : Model)
      (i : @ModelIsomorphism _ M₁ M₂)
      (j : @ModelIsomorphism _ M₂ M₃)
      : @ModelIsomorphism _ M₁ M₃
      :=
      {|
          mi_f := (mi_f j) ∘ (mi_f i)
      |}.
  Next Obligation.
      intros.
      destruct i,j. simpl. (* simpl in H. *)
      unfold Inj in *. intros.
      apply mi_inj1 in H.
      apply mi_inj0 in H.
      exact H.
  Defined.
  Next Obligation.
      intros. pose proof (mi_surj i). pose proof (mi_surj j).
      apply _.
  Defined.
  Next Obligation.
      intros.
      pose proof (Hi := mi_sym i s).
      pose proof (Hj := mi_sym j s).
      rewrite -Hj.
      rewrite -Hi.
      apply set_fmap_compose.
  Defined.
  Next Obligation.
      intros. destruct i, j. simpl in *.
      clear -mi_app1 mi_app0.
      rewrite -mi_app1.
      rewrite -mi_app0.
      apply set_fmap_compose.
  Defined.

  #[global]
  Instance ModelIsomorphism_equiv {Σ : Signature} : Equivalence isom.
  Proof.
      split.
      {
          (* reflexive *)
          unfold Reflexive.
          intros M.
          exists (ModelIsomorphism_refl M).
          exact I.
      }
      {
          (* Symmetric *)
          unfold Symmetric.
          intros M1 M2 [j _].
          exists (ModelIsomorphism_sym _ _ j).
          exact I.
      }
      {
          (* Transitive *)
          unfold Transitive.
          intros M1 M2 M3 [i _] [j _].
          exists (ModelIsomorphism_trans _ _ _ i j).
          exact I.
      }
  Qed.

  (*
  #[global]
  Instance ModelIsomorphism_sym_cancel
      {Σ : Signature}
      (M₁ M₂ : Model)
      (i : @ModelIsomorphism _M₁ M₂)
      :
      Cancel (=) (mi_f i) (mi_f (ModelIsomorphism_sym i)).
  Proof.
      unfold Cancel.
      intros x.
      unfold ModelIsomorphism_sym.
      simpl.
  Qed.
  *)

  Lemma fmap_app_ext {Σ : Signature} (M : Model) (X Y : propset (Domain M))
      (B : Type) (f : (Domain M) -> B)
      :
      f <$> app_ext X Y ≡ {[ e | ∃ le re : M, le ∈ X ∧ re ∈ Y ∧ e ∈ (f <$> (app_interp _ le re)) ]}.
  Proof.
      unfold fmap at 1.
      with_strategy transparent [propset_fmap] unfold propset_fmap at 1.
      set_solver.
  Qed.


  Lemma update_evar_val_compose
      {Σ : Signature} (M₁ M₂ : Model) (ρ : @Valuation Σ M₁) (x : evar) (m : Domain M₁)
      (f : Domain M₁ -> Domain M₂)
      :
      (update_evar_val x (f m)
               {|
                 evar_valuation := f ∘ evar_valuation ρ;
                 svar_valuation := λ X : svar, f <$> svar_valuation ρ X
               |})
      =
      {|
      evar_valuation := f ∘ evar_valuation (update_evar_val x m ρ);
      svar_valuation := λ X : svar, f <$> svar_valuation (update_evar_val x m ρ) X ;
      |}.
  Proof.
      destruct ρ as [ρₑ ρₛ]. simpl.
      unfold update_evar_val. simpl.
      f_equal.
      apply functional_extensionality.
      intros y.
      simpl.
      case_match; auto.
  Qed.

  Lemma update_svar_val_compose
      {Σ : Signature} (M₁ M₂ : Model) (ρ : @Valuation Σ M₁) (X : svar) (ms : propset (Domain M₁))
      (f : Domain M₁ -> Domain M₂)
      :
      (update_svar_val X (f <$> ms)
      {| evar_valuation := f ∘ evar_valuation ρ ;
         svar_valuation := λ X : svar, (f <$> (svar_valuation ρ X)) ;
      |})
      =
      {|
        evar_valuation := f ∘ evar_valuation (update_svar_val X ms ρ) ;
        svar_valuation := λ Y : svar, f <$> (svar_valuation (update_svar_val X ms ρ) Y) ;
      |}.
  Proof.
      destruct ρ as [ρₑ ρₛ]. simpl.
      unfold update_svar_val. simpl.
      f_equal.
      apply functional_extensionality.
      intros y.
      simpl.
      repeat case_match; auto.
  Qed.

  Theorem isomorphism_preserves_semantics
      {Σ : Signature}
      (M₁ M₂ : Model)
      (i : @ModelIsomorphism _ M₁ M₂)
      :
      forall (ϕ : Pattern) (ρ : @Valuation _ M₁),
          ((mi_f i) <$> (@eval Σ M₁ ρ ϕ))
          ≡@{propset (Domain M₂)} (@eval Σ M₂ (mkValuation ((mi_f i) ∘ (evar_valuation ρ)) (λ X, (mi_f i) <$> (svar_valuation ρ X))) ϕ).
  Proof.
      intros ϕ.
      size_induction ϕ; intros ρ.
      {
          (* patt_free_evar x *)
          do 2 rewrite eval_free_evar_simpl.
          simpl.
          unfold fmap.
          with_strategy transparent [propset_fmap] unfold propset_fmap.
          clear. set_solver.
      }
      {
          (* patt_free_svar X *)
          do 2 rewrite eval_free_svar_simpl.
          simpl.
          unfold fmap.
          with_strategy transparent [propset_fmap] unfold propset_fmap.
          clear. set_solver.
      }
      {
          (* patt_bound_evar n *)
          do 2 rewrite eval_bound_evar_simpl.
          simpl.
          unfold fmap.
          with_strategy transparent [propset_fmap] unfold propset_fmap.
          clear. set_solver.
      }
      {
          (* patt_bound_svar n *)
          do 2 rewrite eval_bound_svar_simpl.
          simpl.
          unfold fmap.
          with_strategy transparent [propset_fmap] unfold propset_fmap.
          clear. set_solver.
      }
      {
          (* patt_sym s *)
          do 2 rewrite eval_sym_simpl.
          apply mi_sym.
      }
      {
          (* patt_app ϕ1 ϕ2 *)
          do 2 rewrite eval_app_simpl.
          rewrite fmap_app_ext.

          simpl in Hsz.
          rewrite set_equiv_subseteq.
          do 2 rewrite elem_of_subseteq.
          split.
          {
              intros x Hx.
              rewrite elem_of_PropSet in Hx.
              destruct Hx as [le [re [Hle [Hre Hx] ] ] ].
              rewrite mi_app in Hx.
              rewrite -IHsz.
              { unfold size in *; lia. }
              rewrite -IHsz.
              { unfold size in *; lia. }
              unfold app_ext.
              rewrite elem_of_PropSet.
              exists (mi_f i le).
              exists (mi_f i re).
              repeat split.
              3: { exact Hx. }
              { apply elem_of_fmap_2. assumption. }
              { apply elem_of_fmap_2. assumption. }
          }
          {
              intros x Hx.
              rewrite elem_of_PropSet in Hx.
              rewrite elem_of_PropSet.
              destruct Hx as [le [re [Hle [Hre Hx] ] ] ].
              rewrite -IHsz in Hle.
              { unfold size in *; lia. }
              rewrite -IHsz in Hre.
              { unfold size in *; lia. }
              apply elem_of_fmap_1 in Hle.
              apply elem_of_fmap_1 in Hre.
              destruct Hle as [x1 [Hx1 Hle] ].
              destruct Hre as [x2 [Hx2 Hre] ].
              subst.
              rewrite -(mi_app i) in Hx.
              exists x1. exists x2.
              repeat split; assumption.
          }
      }
      {
          (* patt_bott *)
          do 2 rewrite eval_bott_simpl.
          unfold fmap.
          with_strategy transparent [propset_fmap] unfold propset_fmap.
          clear.
          set_solver.
      }
      {
          (* patt_imp ϕ1 ϕ2 *)
          do 2 rewrite eval_imp_simpl.
          simpl in Hsz.
          rewrite -IHsz.
          { unfold size in *; lia. }
          rewrite -IHsz.
          { unfold size in *; lia. }
          remember (eval ρ ϕ1) as X1.
          remember (eval ρ ϕ2) as X2.
          unfold fmap.
          with_strategy transparent [propset_fmap] unfold propset_fmap.
          rewrite set_equiv_subseteq.
          split.
          {
              rewrite elem_of_subseteq.
              intros x Hx.
              rewrite elem_of_PropSet in Hx.
              destruct Hx as [a [Ha Hx] ].
              subst.
              destruct Hx as [Hx1|Hx2].
              {
                  left.
                  rewrite elem_of_PropSet.
                  split.
                  { clear. set_solver. }
                  intros HContra.
                  rewrite elem_of_PropSet in Hx1.
                  apply Hx1. clear Hx1.
                  rewrite elem_of_PropSet in HContra.
                  destruct HContra as [a0 [Ha0 HContra] ].
                  apply (mi_inj) in Ha0. subst.
                  exact HContra.
              }
              {
                  right.
                  rewrite elem_of_PropSet.
                  exists a.
                  split;[reflexivity|assumption].
              }
          }
          {
              pose (j := ModelIsomorphism_sym _ _ i).
              rewrite elem_of_subseteq.
              intros x Hx.
              rewrite elem_of_PropSet.
              destruct Hx as [Hx|Hx].
              {
                  rewrite elem_of_PropSet in Hx.
                  destruct Hx as [_ Hx].
                  pose (mi_surj i) as i'.
                  pose (@surj'_inv _ _ (=) _ i') as d.
                  exists (d x).
                  rewrite surj'_pf.
                  split;[reflexivity|].
                  left.
                  rewrite elem_of_PropSet.
                  split;[(clear;set_solver)|].
                  rewrite elem_of_PropSet in Hx.
                  intros HContra.
                  apply Hx. clear Hx.
                  exists (d x).
                  rewrite surj'_pf.
                  split;[reflexivity|assumption].
              }
              {
                  rewrite elem_of_PropSet in Hx.
                  destruct Hx as [a [Ha Hx] ].
                  subst.
                  exists a.
                  split;[reflexivity|].
                  right.
                  exact Hx.
              }
          }
      }
      {
          do 2 rewrite eval_ex_simpl.
          simpl.
          rewrite set_equiv_subseteq.
          split.
          {
              rewrite elem_of_subseteq.
              intros x Hx.
              with_strategy transparent [propset_fmap] unfold propset_fmap in Hx.
              rewrite elem_of_PropSet in Hx.
              destruct Hx as [a [Ha Hx] ].
              subst.
              rewrite elem_of_PropSet in Hx.
              destruct Hx as [c Hc].

              under [fun e => _]functional_extensionality => e.
              {
                  rewrite -{1}[e](@surj'_pf _ _ (=) _ (i)).
                  rewrite update_evar_val_compose.
                  over.
              }

              setoid_rewrite <- IHsz.
              2: { rewrite -evar_open_size. simpl in Hsz. unfold size in *; lia. }
              unfold propset_fa_union.
              rewrite elem_of_PropSet.
              exists (mi_f i c).
              apply elem_of_fmap_2.
              replace (surj'_inv (mi_f i c)) with c.
              2: {
                  apply (@mi_inj Σ M₁ M₂ i).
                  rewrite surj'_pf.
                  reflexivity.
              }
              exact Hc.
          }
          {
              rewrite elem_of_subseteq.
              intros x Hx.
              with_strategy transparent [propset_fmap] unfold propset_fmap.
              rewrite elem_of_PropSet.
              unfold propset_fa_union in Hx.
              rewrite elem_of_PropSet in Hx.
              destruct Hx as [c Hc].
              exists (@surj'_inv _ _ _ _ (mi_surj i) x).
              split.
              {
                  rewrite surj'_pf. reflexivity.
              }
              rewrite elem_of_PropSet.
              exists (@surj'_inv _ _ _ _ (mi_surj i) c).
              replace c with ((mi_f i) (@surj'_inv _ _ _ _ (mi_surj i) c)) in Hc by apply surj'_pf.
              rewrite update_evar_val_compose in Hc.
              rewrite -IHsz in Hc.
              { rewrite -evar_open_size. simpl in Hsz. unfold size in *; lia. }
              apply elem_of_fmap in Hc.
              destruct Hc as [y [Hy Hc] ]. subst.
              replace (surj'_inv (mi_f i y)) with y.
              2: {
                  apply (@mi_inj Σ M₁ M₂ i).
                  rewrite surj'_pf.
                  reflexivity.
              }
              exact Hc.
          }
      }
      {
          (* patt_mu ϕ *)
          simpl in Hsz.
          do 2 rewrite eval_mu_simpl. simpl.
          unfold Lattice.LeastFixpointOf,Lattice.meet,Lattice.PrefixpointsOf.
          simpl.
          unfold Lattice.propset_Meet.
          rewrite set_equiv_subseteq.
          do 2 rewrite elem_of_subseteq.
          with_strategy transparent [propset_fmap] unfold propset_fmap.
          do 3 setoid_rewrite elem_of_PropSet.
          split.
          {
              intros x [a [Ha Hx] ]. subst.
              intros e He.
              replace e with ((mi_f i) <$> ((@surj'_inv _ _ _ _ (mi_surj i)) <$> e)) in He at 1.
              2: {
                  clear.
                  unfold_leibniz.
                  rewrite -(set_fmap_compose (surj'_inv) (mi_f i)).
                  unfold fmap.
                  with_strategy transparent [propset_fmap] unfold propset_fmap.
                  rewrite set_equiv_subseteq.
                  do 2 rewrite elem_of_subseteq.
                  split; intros x Hx.
                  {
                      rewrite elem_of_PropSet in Hx.
                      destruct Hx as [a [Ha Hx] ]. subst.
                      unfold compose. rewrite surj'_pf.
                      exact Hx.
                  }
                  {
                      unfold compose.
                      rewrite elem_of_PropSet.
                      exists x.
                      rewrite surj'_pf.
                      split;[reflexivity|assumption].
                  }
              }

              rewrite update_svar_val_compose in He.
              rewrite -IHsz in He.
              { rewrite -svar_open_size.  unfold size in *; lia. }
              specialize (Hx ((@surj'_inv _ _ _ _ (mi_surj i)) <$> e)).
              ospecialize* Hx.
              {
                  clear -He.
                  rewrite elem_of_subseteq in He.
                  rewrite elem_of_subseteq.
                  intros x.
                  specialize (He (mi_f i x)).
                  remember (eval
                  (update_svar_val (fresh_svar ϕ) (surj'_inv <$> e) ρ)
                  (ϕ^{svar: 0 ↦ fresh_svar ϕ})) as PI.
                  intros Hx.
                  apply (elem_of_fmap_2 (mi_f i)) in Hx.
                  specialize (He Hx). clear Hx.
                  apply elem_of_fmap.
                  exists (mi_f i x).
                  split.
                  {
                      apply (@mi_inj _ _ _ i).
                      rewrite surj'_pf.
                      reflexivity.
                  }
                  {
                      exact He.
                  }
              }
              apply elem_of_fmap in Hx.
              destruct Hx as [y [Hy Hx] ]. subst.
              rewrite surj'_pf.
              exact Hx.
          }
          {
              intros x Hx.
              exists (@surj'_inv _ _ _ _ (mi_surj i) x).
              split.
              {
                  rewrite surj'_pf. reflexivity.
              }
              {
                  intros e He.
                  specialize (Hx ((mi_f i) <$> e)).
                  rewrite update_svar_val_compose in Hx.
                  rewrite -IHsz in Hx.
                  { rewrite -svar_open_size. unfold size in *; lia. }
                  clear IHsz.

                  replace e with (((@surj'_inv _ _ _ _ (mi_surj i)) <$> ((mi_f i) <$> e))).
                  2: {
                      clear.
                      unfold_leibniz.
                      rewrite -(set_fmap_compose (mi_f i) (surj'_inv)).
                      unfold fmap.
                      with_strategy transparent [propset_fmap] unfold propset_fmap.
                      rewrite set_equiv_subseteq.
                      do 2 rewrite elem_of_subseteq.
                      split; intros x Hx.
                      {
                          rewrite elem_of_PropSet in Hx.
                          destruct Hx as [a [Ha Hx] ]. subst.
                          unfold compose.
                          replace (surj'_inv (mi_f i a)) with a.
                          2: {
                              apply (@mi_inj _ _ _ i).
                              rewrite surj'_pf.
                              reflexivity.
                          }
                          exact Hx.
                      }
                      {
                          unfold compose.
                          rewrite elem_of_PropSet.
                          exists x.
                          replace (surj'_inv (mi_f i x)) with x.
                          2: {
                              apply (@mi_inj _ _ _ i).
                              rewrite surj'_pf.
                              reflexivity.
                          }
                          split;[reflexivity|assumption].
                      } 
                  }
                  apply elem_of_fmap.
                  exists x.
                  split;[reflexivity|].
                  apply Hx. clear Hx.
                  rewrite elem_of_subseteq.
                  intros x0.
                  rewrite elem_of_subseteq in He.
                  intros H.
                  specialize (He ((@surj'_inv _ _ _ _ (mi_surj i)) x0)).
                  apply (elem_of_fmap_2 (mi_f i)) in He.
                  {
                      rewrite surj'_pf in He. exact He.
                  }
                  apply (elem_of_fmap_2 ((@surj'_inv _ _ _ _ (mi_surj i)))) in H.
                  rewrite -(set_fmap_compose (mi_f i) (surj'_inv)) in H.
                  unfold compose in H. simpl in H.
                  move: H.
                  under [fun x => _]functional_extensionality => x1.
                  {
                      replace (surj'_inv (mi_f i x1)) with x1.
                      2: {
                          apply (@mi_inj _ _ _ i).
                          rewrite surj'_pf.
                          reflexivity.
                      }
                      over.
                  }
                  move=> H.
                  unfold fmap in H.
                  with_strategy transparent [propset_fmap] unfold propset_fmap in H.
                  rewrite elem_of_PropSet in H.
                  destruct H as [a [Ha H] ]. subst.
                  exact H.
              }
          }
      }
  Qed.
End isomorphism.
