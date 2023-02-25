From Coq Require Import ssreflect ssrfun ssrbool.

From Coq Require Import Strings.String.
From Coq Require Import Logic.PropExtensionality Logic.Eqdep_dec.
From Equations Require Import Equations.

From stdpp Require Export base gmap fin_sets sets list countable.
From MatchingLogic Require Import Syntax Semantics StringSignature ProofSystem ProofMode Utils.stdpp_ext.
From MatchingLogicProver Require Import Named NamedProofSystem NMatchers.

From stdpp Require Import base finite gmap mapset listset_nodup numbers propset list pretty strings.

Import ProofSystem.Notations.

(* TODO: move this near to the definition of Pattern *)
Derive NoConfusion for Pattern.
Derive Subterm for Pattern.


Global Instance string_app_empty_rightid :
  RightId (=) "" String.append
.
Proof.
  intros s.
  induction s; simpl.
  { reflexivity. }
  cbv.
  fold String.append. (* This is weird. *)
  rewrite IHs.
  reflexivity.
Qed.

Global Instance string_app_empty_leftid :
  LeftId (=) "" String.append
.
Proof.
  intros s. reflexivity.
Qed.

Lemma string_of_list_ascii_app l1 l2:
  string_of_list_ascii (l1 ++ l2)
  = (string_of_list_ascii l1) +:+ (string_of_list_ascii l2)
.
Proof.
  induction l1; cbn.
  {
    unfold String.append. reflexivity.
  }
  {
    rewrite IHl1. clear IHl1.
    reflexivity.
  }
Qed.


Global Instance string_of_list_ascii_of_string_cancel:
  Cancel (=) string_of_list_ascii list_ascii_of_string
.
Proof.
  intros x.
  apply string_of_list_ascii_of_string.
Qed.

Global Instance list_ascii_of_string_of_list_ascii_cancel:
  Cancel (=) list_ascii_of_string string_of_list_ascii 
.
Proof.
  intros x.
  apply list_ascii_of_string_of_list_ascii.
Qed.

Global Instance string_of_list_ascii_inj:
  Inj (=) (=) string_of_list_ascii
.
Proof.
  apply cancel_inj.
Qed.

Global Instance list_ascii_of_string_inj:
  Inj (=) (=) list_ascii_of_string
.
Proof.
  apply cancel_inj.
Qed.

Global Instance string_app_assoc:
  Assoc (=) String.append
.
Proof.
  intros x y z.
  rewrite -(string_of_list_ascii_of_string x).
  rewrite -(string_of_list_ascii_of_string y).
  rewrite -(string_of_list_ascii_of_string z).
  rewrite -!string_of_list_ascii_app.
  rewrite app_assoc.
  reflexivity.
Qed.

Global Instance string_app_inj_2 s2 :
  Inj (=) (=) (fun s1 => String.append s1 s2).
Proof.
  intros s1 s1' H.
  move: s1 s1' H.
  induction s2; intros s1 s1' H; cbn in *.
  {
    do 2 rewrite right_id in H.
    exact H.
  }
  {
    replace (String a s2)
      with ((String a EmptyString) +:+ s2) in H
      by reflexivity.
    replace (String a s1)
      with ((String a EmptyString) +:+ s1) in H
      by reflexivity.
    rewrite 2!string_app_assoc in H.
    specialize (IHs2 _ _ H).
    clear H s2.
    rename IHs2 into H.
    rewrite -(string_of_list_ascii_of_string s1).
    rewrite -(string_of_list_ascii_of_string s1').
    rewrite -(string_of_list_ascii_of_string s1) in H.
    rewrite -(string_of_list_ascii_of_string s1') in H.
    rewrite -(string_of_list_ascii_of_string (String a "")) in H.
    rewrite [list_ascii_of_string (String a "")]/= in H.
    rewrite -!string_of_list_ascii_app in H.
    apply string_of_list_ascii_inj in H.
    simplify_list_eq.
    congruence.
    }
Qed.


Lemma list_ascii_of_string_app s1 s2:
  list_ascii_of_string (s1 +:+ s2)
  = (list_ascii_of_string s1) ++ (list_ascii_of_string s2)
.
Proof.
  induction s1; cbn.
  {
    reflexivity.
  }
  {
    cbv. fold list_ascii_of_string. fold String.append.
    apply f_equal. rewrite IHs1. reflexivity.
  }
Qed.


Section abstract.
  Context
    {Σ : Signature}
    (l2n : Pattern -> NamedPattern)
    (l2n_fe : forall x, l2n (patt_free_evar x) = npatt_evar x)
    (l2n_fs : forall X, l2n (patt_free_svar X) = npatt_svar X)
    (l2n_bs : forall n, l2n (patt_bound_svar n) = npatt_bott)
    (l2n_be : forall n, l2n (patt_bound_evar n) = npatt_bott)
    (l2n_b : l2n patt_bott = npatt_bott)
    (l2n_sym : forall s, l2n (patt_sym s) = npatt_sym s)
    (l2n_imp : forall ϕ1 ϕ2, l2n (patt_imp ϕ1 ϕ2) = npatt_imp (l2n ϕ1) (l2n ϕ2))
    (l2n_app : forall ϕ1 ϕ2, l2n (patt_app ϕ1 ϕ2) = npatt_app (l2n ϕ1) (l2n ϕ2))
    (ename : Pattern -> evar)
    (ebody : Pattern -> NamedPattern)
    (sname : Pattern -> svar)
    (sbody : Pattern -> NamedPattern)
    (l2n_ex : forall ϕ', l2n (patt_exists ϕ') = npatt_exists (ename ϕ') (ebody ϕ'))
    (l2n_mu : forall ϕ', l2n (patt_mu ϕ') = npatt_mu (sname ϕ') (sbody ϕ'))
  .

  Context
    (f : Pattern -> evar -> evar)
    (fs : Pattern -> svar -> svar)
    (ebody_bott : ebody patt_bott = npatt_bott )
    (ebody_efree: forall x, ebody (patt_free_evar x) = npatt_evar x)
    (ebody_sfree: forall X, ebody (patt_free_svar X) = npatt_svar X)
    (ebody_sym: forall s, ebody (patt_sym s) = npatt_sym s)
    (ebody_app : forall ϕ1 ϕ2, well_formed_closed_ex_aux ϕ1 0 -> well_formed_closed_ex_aux ϕ2 0 -> ebody (patt_app ϕ1 ϕ2) = npatt_app (ebody ϕ1) (ebody ϕ2))
    (ebody_imp : forall ϕ1 ϕ2, well_formed_closed_ex_aux ϕ1 0 -> well_formed_closed_ex_aux ϕ2 0 -> ebody (patt_imp ϕ1 ϕ2) = npatt_imp (ebody ϕ1) (ebody ϕ2))
    (ebody_bs : forall n, ebody (patt_bound_svar n) = npatt_bott)
    (ebody_mu : forall ϕ, well_formed_closed_mu_aux ϕ 1 -> ebody (patt_mu ϕ) = npatt_mu (sname ϕ) (ebody ϕ))

    (sbody_bott : sbody patt_bott = npatt_bott )
    (sbody_efree: forall x, sbody (patt_free_evar x) = npatt_evar x)
    (sbody_sfree: forall X, sbody (patt_free_svar X) = npatt_svar X)
    (sbody_sym: forall s, sbody (patt_sym s) = npatt_sym s)
    (sbody_app : forall ϕ1 ϕ2, well_formed_closed_mu_aux ϕ1 0 -> well_formed_closed_mu_aux ϕ2 0 -> sbody (patt_app ϕ1 ϕ2) = npatt_app (sbody ϕ1) (sbody ϕ2))
    (sbody_imp : forall ϕ1 ϕ2, well_formed_closed_mu_aux ϕ1 0 -> well_formed_closed_mu_aux ϕ2 0 -> sbody (patt_imp ϕ1 ϕ2) = npatt_imp (sbody ϕ1) (sbody ϕ2))
    (sbody_be : forall n, sbody (patt_bound_evar n) = npatt_bott)
    (sbody_ex : forall ϕ, well_formed_closed_ex_aux ϕ 1 -> sbody (patt_exists ϕ) = npatt_exists (ename ϕ) (sbody ϕ))

    (ebody_ex : forall ϕ, well_formed_closed_ex_aux ϕ 1 -> ebody (patt_exists ϕ) = npatt_exists (ename ϕ) (ebody ϕ))
    (sbody_mu : forall ϕ, well_formed_closed_mu_aux ϕ 1 -> sbody (patt_mu ϕ) = npatt_mu (sname ϕ) (sbody ϕ))
    (ename_erenames: forall x, ename (patt_free_evar x) <> x)
    (sname_srenames: forall X, sname (patt_free_svar X) <> X)
    (ename_fresh_in_ebody: forall ϕ, ename ϕ ∉ named_free_evars (ebody ϕ))
    (sname_fresh_in_sbody: forall ϕ, sname ϕ ∉ named_free_svars (sbody ϕ))
    (f_ex : forall ϕ y, (f (patt_exists ϕ) y) = (f ϕ y))
    (f_mu : forall ϕ y, (f (patt_mu ϕ) y) = (f ϕ y))
    (ename_ex : forall ϕ, ename (patt_exists ϕ) = ename ϕ)
    (ename_mu : forall ϕ, ename (patt_mu ϕ) = ename ϕ)
    (sname_ex : forall ϕ, sname (patt_exists ϕ) = sname ϕ)
    (sname_mu : forall ϕ, sname (patt_mu ϕ) = sname ϕ)
    (*sbody_phi : forall ϕ, sbody ϕ = l2n ϕ*)
    (*sbody_mu : forall ϕ, sbody (patt_mu ϕ) = npatt_mu (sname ϕ) (sbody ϕ)*)
    (fs_ex : forall ϕ Y, (fs (patt_exists ϕ) Y) = (fs ϕ Y))
    (fs_mu : forall ϕ Y, (fs (patt_mu ϕ) Y) = (fs ϕ Y))
  .

  Context
    (sz : nat)
  .
  Lemma what_we_want_evar (ϕ : Pattern) (y : evar)
    (l2n_mu_ind : forall ϕ', (* this is a lemma / mutually inductive hypothesis*)
    well_formed (patt_mu ϕ') ->
    size' ϕ' < sz ->
    l2n (patt_mu ϕ') = npatt_mu (sname ϕ') (ebody ϕ'))
    :
    size' ϕ <= sz ->
    well_formed ϕ ->
    l2n (evar_open y 0 ϕ) = rename_free_evar (ebody ϕ) (f ϕ y) (ename ϕ)
  .
  Proof.
    intros Hsz.
    move: y.
    move: ϕ Hsz.
    induction sz; intros ϕ Hsz.
    { destruct ϕ; cbn in Hsz; lia. }
    destruct ϕ; intros y wfϕ; cbn in *.
    {
      (* patt_free_evar x*)
      rewrite l2n_fe.
      rewrite rename_free_evar_id.
      { rewrite ebody_efree. simpl. rewrite elem_of_singleton. apply ename_erenames. }
      { rewrite ebody_efree. reflexivity. }
    }
    {
      (* patt_free_svar x*)
      rewrite l2n_fs.
      rewrite rename_free_evar_id.
      { rewrite ebody_sfree. simpl. rewrite elem_of_empty. auto. }
      { rewrite ebody_sfree. reflexivity. }
    }
    {
      (* patt_bound_evar n *)
      repeat case_match; subst; try lia; try congruence.
    }
    {
      (* patt_bound_svar n *)
      rewrite ebody_bs. cbn. rewrite l2n_bs. reflexivity.
    }
    {
      (* patt_sym s *)
      rewrite l2n_sym.
      rewrite rename_free_evar_id.
      { rewrite ebody_sym. cbn. rewrite elem_of_empty. auto. }
      { rewrite ebody_sym. reflexivity. }
    }
    {
      (* patt_app ϕ1 ϕ2 *)
      rewrite l2n_app.
      rewrite IHn.
      2: { lia. }
      2: { wf_auto2. }
      {
        intros.
        apply l2n_mu_ind.
        { assumption. }
        { lia. }
      }
      rewrite IHn.
      2: { lia. }
      2: { wf_auto2. }
      {
        intros.
        apply l2n_mu_ind.
        { assumption. }
        { lia. }
      }
      rewrite rename_free_evar_id.
      { apply ename_fresh_in_ebody. }
      rewrite rename_free_evar_id.
      { apply ename_fresh_in_ebody. }
      rewrite rename_free_evar_id.
      { apply ename_fresh_in_ebody. }
      rewrite ebody_app.
      { wf_auto2. }
      { wf_auto2. }
      reflexivity.
    }
    {
      (* patt_bott *)
      rewrite l2n_b.
      rewrite rename_free_evar_id.
      { rewrite ebody_bott. cbn. rewrite elem_of_empty. auto. }
      { rewrite ebody_bott. reflexivity. }
    }
    {
      (* patt_imp ϕ1 ϕ2 *)
      rewrite l2n_imp.
      rewrite IHn.
      2: { lia. }
      2: { wf_auto2. }
      {
        intros.
        apply l2n_mu_ind.
        { assumption. }
        { lia. }
      }
      rewrite IHn.
      2: { lia. }
      2: { wf_auto2. }
      {
        intros.
        apply l2n_mu_ind.
        { assumption. }
        { lia. }
      }
      rewrite rename_free_evar_id.
      { apply ename_fresh_in_ebody. }
      rewrite rename_free_evar_id.
      { apply ename_fresh_in_ebody. }
      rewrite rename_free_evar_id.
      { apply ename_fresh_in_ebody. }
      rewrite ebody_imp.
      { wf_auto2. }
      { wf_auto2. }
      reflexivity.
    }
    {
      rewrite l2n_ex.
      fold (evar_open y 1 ϕ).
      (*
      (* We need `rename_free_evar` to return `npatt_exists`,
         but the only way to ensure that is to feed it a `patt_exists`.
         More precisely, we need it to return `npatt_exists (ename (evar_open y 1 ϕ)) ?something).
         Our best chance is if `ebody` returns this `(ename (evar_open y 1 ϕ))` thing.
       *)
      assert (H1: exists ϕb, ebody (patt_exists ϕ) = npatt_exists (ename (evar_open y 1 ϕ)) ϕb).
      { admit. }
      destruct H1 as [ϕb H1].
      rewrite H1.
      cbn.
      destruct (decide (ename (patt_exists ϕ) = ename (evar_open y 1 ϕ))) as [Hy|Hn].
      {
        apply f_equal.
        admit.
      }
      {
        apply f_equal. revert Hn.
      }

      (* The only way to use IHϕ is backwards now,
         but we need some additional assumptions for that.
      *)
      rewrite -IHϕ.
      *)
      erewrite evar_open_wfc_aux with (db1 := 1).
      3: wf_auto2.
      2: lia.
      pose proof (Hee := ebody_ex ϕ ltac:(wf_auto2)).
      rewrite Hee.
      cbn.
      rewrite ename_ex. rewrite decide_eq_same.
      reflexivity.
    }
    {
      fold (evar_open y 0 ϕ).
      rewrite evar_open_closed.
      { wf_auto2. }
      rewrite l2n_mu_ind.
      { wf_auto2. }
      { lia. }
      
      rewrite ebody_mu.
      { wf_auto2. }
      cbn.
      f_equal.
      rewrite ename_mu.

      rewrite rename_free_evar_id.
      {
        intros HContra.
        apply ename_fresh_in_ebody in HContra.
        exact HContra.
      }
      reflexivity.
    }
  Qed.


  Lemma what_we_want_svar (ϕ : Pattern) (Y : svar)
    (l2n_ex_ind : forall ϕ', (* this is a lemma / mutually inductive hypothesis*)
    well_formed (patt_exists ϕ') ->
    size' ϕ' < sz ->
    l2n (patt_exists ϕ') = npatt_exists (ename ϕ') (sbody ϕ'))
    :
    size' ϕ <= sz ->
    well_formed ϕ ->
    l2n (svar_open Y 0 ϕ) = rename_free_svar (sbody ϕ) (fs ϕ Y) (sname ϕ)
  .
  Proof.
    intros Hsz.
    move: Y.
    move: ϕ Hsz.
    induction sz; intros ϕ Hsz.
    { destruct ϕ; cbn in Hsz; lia. }
    destruct ϕ; intros Y wfϕ; cbn in *.
    
    {
      (* patt_free_evar x*)
      rewrite l2n_fe.
      rewrite rename_free_svar_id.
      { rewrite sbody_efree. simpl. rewrite elem_of_empty. auto. }
      { rewrite sbody_efree. reflexivity. }
    }
    {
      (* patt_free_svar X*)
      rewrite l2n_fs.
      rewrite rename_free_svar_id.
      { rewrite sbody_sfree. simpl. rewrite elem_of_singleton. apply sname_srenames. }
      { rewrite sbody_sfree. reflexivity. }
    }
    {
      (* patt_bound_evar n *)
      rewrite sbody_be. cbn. rewrite l2n_be. reflexivity.
    }
    {
      (* patt_bound_svar n *)
      unfold well_formed_closed in wfϕ. cbn in wfϕ.
      repeat case_match; subst; try lia; cbn in wfϕ; try congruence.
    }
    {
      (* patt_sym s *)
      rewrite l2n_sym.
      rewrite rename_free_svar_id.
      { rewrite sbody_sym. cbn. rewrite elem_of_empty. auto. }
      { rewrite sbody_sym. reflexivity. }
    }
    {
      (* patt_app ϕ1 ϕ2 *)
      rewrite l2n_app.
      rewrite IHn.
      2: { lia. }
      2: { wf_auto2. }
      {
        intros.
        apply l2n_ex_ind.
        { assumption. }
        { lia. }
      }
      rewrite IHn.
      2: { lia. }
      2: { wf_auto2. }
      {
        intros.
        apply l2n_ex_ind.
        { assumption. }
        { lia. }
      }
      rewrite rename_free_svar_id.
      { apply sname_fresh_in_sbody. }
      rewrite rename_free_svar_id.
      { apply sname_fresh_in_sbody. }
      rewrite rename_free_svar_id.
      { apply sname_fresh_in_sbody. }
      rewrite sbody_app.
      { wf_auto2. }
      { wf_auto2. }
      reflexivity.
    }
    {
      (* patt_bott *)
      rewrite l2n_b.
      rewrite rename_free_svar_id.
      { rewrite sbody_bott. cbn. rewrite elem_of_empty. auto. }
      { rewrite sbody_bott. reflexivity. }
    }
    {
      (* patt_imp ϕ1 ϕ2 *)
      rewrite l2n_imp.
      rewrite IHn.
      2: { lia. }
      2: { wf_auto2. }
      {
        intros.
        apply l2n_ex_ind.
        { assumption. }
        { lia. }
      }
      rewrite IHn.
      2: { lia. }
      2: { wf_auto2. }
      {
        intros.
        apply l2n_ex_ind.
        { assumption. }
        { lia. }
      }
      rewrite rename_free_svar_id.
      { apply sname_fresh_in_sbody. }
      rewrite rename_free_svar_id.
      { apply sname_fresh_in_sbody. }
      rewrite rename_free_svar_id.
      { apply sname_fresh_in_sbody. }
      rewrite sbody_imp.
      { wf_auto2. }
      { wf_auto2. }
      reflexivity.
    }
    {
      fold (svar_open Y 0 ϕ).
      rewrite svar_open_closed.
      { wf_auto2. }
      rewrite l2n_ex_ind.
      { wf_auto2. }
      { lia. }
      
      rewrite sbody_ex.
      { wf_auto2. }
      cbn.
      f_equal.
      rewrite sname_ex.

      rewrite rename_free_svar_id.
      {
        intros HContra.
        apply sname_fresh_in_sbody in HContra.
        exact HContra.
      }
      reflexivity.
    }
    {
      rewrite l2n_mu.
      fold (svar_open Y 1 ϕ).
      erewrite svar_open_wfc_aux with (db1 := 1).
      3: wf_auto2.
      2: lia.
      pose proof (Hsm := sbody_mu ϕ ltac:(wf_auto2)).
      rewrite Hsm.
      cbn.
      rewrite sname_mu. rewrite decide_eq_same.
      reflexivity.
    }
  Qed.

End abstract.

Section concrete.
  Context
    {Σ : Signature}
    (string2evar : string -> evar)
    (evar2string : evar -> string)
    (string2svar : string -> svar)
    (svar2string : svar -> string)
    (sym2string : symbols -> string)
    (cancele1: Cancel (=) string2evar evar2string)
    (cancele2: Cancel (=) evar2string string2evar)
    (cancels1: Cancel (=) string2svar svar2string)
    (cancels2: Cancel (=) svar2string string2svar)
  .

  Definition empty_evar : evar := string2evar "F".
  Definition empty_svar : svar := string2svar "F".

  Fixpoint ename (ϕ : Pattern) : evar :=
    match ϕ with
    | patt_free_evar x => string2evar ("E" +:+ evar2string x)
    | patt_free_svar X => string2evar ("E" +:+ svar2string X)
    | patt_sym s => string2evar ("E" +:+ sym2string s)
    | patt_bott => empty_evar
    | patt_bound_evar _ => empty_evar
    | patt_bound_svar _ => empty_evar
    | patt_app ϕ₁ ϕ₂ => string2evar (evar2string (ename ϕ₁) +:+ evar2string (ename ϕ₂))
    | patt_imp ϕ₁ ϕ₂ => string2evar (evar2string (ename ϕ₁) +:+ evar2string (ename ϕ₂))
    | patt_exists ϕ' => ename ϕ'
    | patt_mu ϕ' => ename ϕ'
    end.

  Fixpoint sname (ϕ : Pattern) : svar :=
    match ϕ with
    | patt_free_svar X => string2svar ("S" +:+ svar2string X)
    | patt_free_evar x => string2svar ("S" +:+ evar2string x)
    | patt_sym s => string2svar ("S" +:+ sym2string s)
    | patt_bott => empty_svar
    | patt_bound_evar _ => empty_svar
    | patt_bound_svar _ => empty_svar
    | patt_app ϕ₁ ϕ₂ => string2svar (svar2string (sname ϕ₁) +:+ svar2string (sname ϕ₂))
    | patt_imp ϕ₁ ϕ₂ => string2svar (svar2string (sname ϕ₁) +:+ svar2string (sname ϕ₂))
    | patt_exists ϕ' => sname ϕ'
    | patt_mu ϕ' => sname ϕ'
    end.

  Lemma ename_not_in_free' ϕ ev:
    ev ∈ free_evars ϕ ->
    List.length (list_ascii_of_string (evar2string (ename ϕ))) > List.length (list_ascii_of_string (evar2string ev))
  .
  Proof.
    induction ϕ; cbn; intros Hin.
    {
      rewrite elem_of_singleton in Hin. subst ev.
      rewrite cancele2.
      rewrite list_ascii_of_string_app. cbn.
      lia.
    }
    { exfalso. set_solver. }
    { exfalso. set_solver. }
    { exfalso. set_solver. }
    { exfalso. set_solver. }
    {
      rewrite cancele2.
      rewrite list_ascii_of_string_app.
      rewrite app_length.
      rewrite elem_of_union in Hin.
      destruct Hin as [Hin|Hin].
      {
        specialize (IHϕ1 Hin).
        lia.
      }
      {
        specialize (IHϕ2 Hin).
        lia.
      }
    }
    { exfalso. set_solver. }
    {
      rewrite cancele2.
      rewrite list_ascii_of_string_app.
      rewrite app_length.
      rewrite elem_of_union in Hin.
      destruct Hin as [Hin|Hin].
      {
        specialize (IHϕ1 Hin).
        lia.
      }
      {
        specialize (IHϕ2 Hin).
        lia.
      }
    }
    { auto with nocore. }
    { auto with nocore. }
  Qed.

  Lemma sname_not_in_free' ϕ sv:
    sv ∈ free_svars ϕ ->
    List.length (list_ascii_of_string (svar2string (sname ϕ))) > List.length (list_ascii_of_string (svar2string sv))
  .
  Proof.
    induction ϕ; cbn; intros Hin.
    { exfalso. set_solver. }
    {
      rewrite elem_of_singleton in Hin. subst sv.
      rewrite cancels2.
      rewrite list_ascii_of_string_app. cbn.
      lia.
    }
    { exfalso. set_solver. }
    { exfalso. set_solver. }
    { exfalso. set_solver. }
    {
      rewrite cancels2.
      rewrite list_ascii_of_string_app.
      rewrite app_length.
      rewrite elem_of_union in Hin.
      destruct Hin as [Hin|Hin].
      {
        specialize (IHϕ1 Hin).
        lia.
      }
      {
        specialize (IHϕ2 Hin).
        lia.
      }
    }
    { exfalso. set_solver. }
    {
      rewrite cancels2.
      rewrite list_ascii_of_string_app.
      rewrite app_length.
      rewrite elem_of_union in Hin.
      destruct Hin as [Hin|Hin].
      {
        specialize (IHϕ1 Hin).
        lia.
      }
      {
        specialize (IHϕ2 Hin).
        lia.
      }
    }
    { auto with nocore. }
    { auto with nocore. }
  Qed.

  Lemma sname_not_in_free ϕ:
    sname ϕ ∉ free_svars ϕ.
  Proof.
    intros HContra.
    apply sname_not_in_free' in HContra.
    lia.
  Qed.

  Lemma ename_not_in_free ϕ:
    ename ϕ ∉ free_evars ϕ.
  Proof.
    intros HContra.
    apply ename_not_in_free' in HContra.
    lia.
  Qed.

  Equations? ln2named (ϕ : Pattern) : NamedPattern by wf (size' ϕ) lt :=
    ln2named (patt_bound_evar _) => npatt_bott ;
    ln2named (patt_bound_svar _) => npatt_bott ;
    ln2named (patt_free_evar x) => npatt_evar x ;
    ln2named (patt_free_svar X) => npatt_svar X ;
    ln2named patt_bott := npatt_bott ;
    ln2named (patt_sym s) := npatt_sym s ;
    ln2named (patt_imp ϕ₁ ϕ₂)
      := npatt_imp (ln2named ϕ₁) (ln2named ϕ₂) ;
    ln2named (patt_app ϕ₁ ϕ₂)
      := npatt_app (ln2named ϕ₁) (ln2named ϕ₂) ;
    ln2named (patt_exists ϕ')
      := let x := string2evar ("A" +:+ evar2string (ename ϕ')) in
         npatt_exists (ename ϕ') (ln2named (evar_open x 0 ϕ')) ;
    ln2named (patt_mu ϕ')
      := let X := string2svar ("B" +:+ svar2string (sname ϕ')) in
        npatt_mu (sname ϕ') (ln2named (svar_open X 0 ϕ')) .
  Proof.
      all: simpl; try lia.
      { rewrite evar_open_size'. simpl. lia. }
      { rewrite svar_open_size'. simpl. lia. }
  Qed.

  Lemma named_free_evars_ln2named (ϕ : Pattern) (x : evar):
    x ∈ named_free_evars (ln2named ϕ) ->
    (x ∈ free_evars ϕ) \/ (exists (s : string), x = string2evar ("A" +:+ s))
  .
  Proof.
    move: x.
    funelim (ln2named ϕ); cbn; intros x0 Hx.
    { left. exact Hx. }
    { left. exact Hx. }
    { exfalso. clear -Hx. set_solver. }
    { exfalso. clear -Hx. set_solver. }
    { exfalso. clear -Hx. set_solver. }
    {
      rewrite elem_of_union in Hx.
      destruct Hx as [Hx|Hx].
      {
        specialize (H x0 Hx).
        destruct H as [H|H].
        {
          left. clear -H. set_solver.
        }
        {
          right. exact H.
        }
      }
      {
        specialize (H0 x0 Hx).
        destruct H0 as [H0|H0].
        {
          left. clear -H0. set_solver.
        }
        {
          right. exact H0.
        }
      }
    }
    {
      exfalso. clear -Hx. set_solver.
    }
    {
      rewrite elem_of_union in Hx.
      destruct Hx as [Hx|Hx].
      {
        specialize (H x0 Hx).
        destruct H as [H|H].
        {
          left. clear -H. set_solver.
        }
        {
          right. exact H.
        }
      }
      {
        specialize (H0 x0 Hx).
        destruct H0 as [H0|H0].
        {
          left. clear -H0. set_solver.
        }
        {
          right. exact H0.
        }
      }
    }
    {
      rewrite elem_of_difference in Hx.
      destruct Hx as [Hx1 Hx2].
      rewrite elem_of_singleton in Hx2.
      specialize (H x0 Hx1).
      destruct H as [H|H].
      {
        rewrite free_evars_evar_open'' in H.
        destruct H as [[H1 H2]|H].
        {
          right.
          subst x0.
          eexists. reflexivity.
        }
        {
          left. exact H.
        }
      }
      {
        right. exact H.
      }
    }
    {
      specialize (H x0 Hx).
      destruct H as [H|H].
      {
        rewrite free_evars_svar_open in H.
        left. exact H.
      }
      {
        right. exact H.
      }
    }
  Qed.


  Lemma named_free_svars_ln2named (ϕ : Pattern) (X : svar):
    X ∈ named_free_svars (ln2named ϕ) ->
    (X ∈ free_svars ϕ) \/ (exists (s : string), X = string2svar ("B" +:+ s))
  .
  Proof.
    move: X.
    funelim (ln2named ϕ); cbn; intros X0 HX.
    { left. exact HX. }
    { left. exact HX. }
    { exfalso. clear -HX. set_solver. }
    { exfalso. clear -HX. set_solver. }
    { exfalso. clear -HX. set_solver. }
    {
      rewrite elem_of_union in HX.
      destruct HX as [HX|HX].
      {
        specialize (H X0 HX).
        destruct H as [H|H].
        {
          left. clear -H. set_solver.
        }
        {
          right. exact H.
        }
      }
      {
        specialize (H0 X0 HX).
        destruct H0 as [H0|H0].
        {
          left. clear -H0. set_solver.
        }
        {
          right. exact H0.
        }
      }
    }
    {
      exfalso. clear -HX. set_solver.
    }
    {
      rewrite elem_of_union in HX.
      destruct HX as [HX|HX].
      {
        specialize (H X0 HX).
        destruct H as [H|H].
        {
          left. clear -H. set_solver.
        }
        {
          right. exact H.
        }
      }
      {
        specialize (H0 X0 HX).
        destruct H0 as [H0|H0].
        {
          left. clear -H0. set_solver.
        }
        {
          right. exact H0.
        }
      }
    }
    {
      specialize (H X0 HX).
      destruct H as [H|H].
      {
        rewrite free_svars_evar_open in H.
        left. exact H.
      }
      {
        right. exact H.
      }
    }
    {
      rewrite elem_of_difference in HX.
      destruct HX as [HX1 HX2].
      rewrite elem_of_singleton in HX2.
      specialize (H X0 HX1).
      destruct H as [H|H].
      {
        rewrite free_svars_svar_open'' in H.
        destruct H as [[H1 H2]|H].
        {
          right.
          subst X0.
          eexists. reflexivity.
        }
        {
          left. exact H.
        }
      }
      {
        right. exact H.
      }
    }
  Qed.

  Lemma ename_nonempty phi:
    list_ascii_of_string (evar2string (ename phi)) <> []
  .
  Proof.
    induction phi; cbn.
    {
      rewrite cancele2. rewrite list_ascii_of_string_app. cbn.
      discriminate.
    }
    {
      rewrite cancele2. rewrite list_ascii_of_string_app. cbn.
      discriminate.
    }
    {
      unfold empty_evar.
      rewrite cancele2.
      discriminate.
    }
    {
      unfold empty_evar.
      rewrite cancele2.
      discriminate.
    }
    {
      rewrite cancele2. rewrite list_ascii_of_string_app. cbn.
      discriminate.
    }
    {
      rewrite cancele2. rewrite list_ascii_of_string_app.
      intros HContra.
      rewrite app_nil in HContra.
      naive_solver.
    }
    {
      unfold empty_evar.
      rewrite cancele2.
      discriminate.
    }
    {
      rewrite cancele2. rewrite list_ascii_of_string_app.
      intros HContra.
      rewrite app_nil in HContra.
      naive_solver.
    }
    { assumption. }
    { assumption. }
  Qed.


  Lemma sname_nonempty phi:
    list_ascii_of_string (svar2string (sname phi)) <> []
  .
  Proof.
    induction phi; cbn.
    {
      rewrite cancels2. rewrite list_ascii_of_string_app. cbn.
      discriminate.
    }
    {
      rewrite cancels2. rewrite list_ascii_of_string_app. cbn.
      discriminate.
    }
    {
      unfold empty_svar.
      rewrite cancels2.
      discriminate.
    }
    {
      unfold empty_svar.
      rewrite cancels2.
      discriminate.
    }
    {
      rewrite cancels2. rewrite list_ascii_of_string_app. cbn.
      discriminate.
    }
    {
      rewrite cancels2. rewrite list_ascii_of_string_app.
      intros HContra.
      rewrite app_nil in HContra.
      naive_solver.
    }
    {
      unfold empty_svar.
      rewrite cancels2.
      discriminate.
    }
    {
      rewrite cancels2. rewrite list_ascii_of_string_app.
      intros HContra.
      rewrite app_nil in HContra.
      naive_solver.
    }
    { assumption. }
    { assumption. }
  Qed.

  Context
    (f : Pattern -> evar -> evar)
    (f_ex : forall ϕ y, (f (patt_exists ϕ) y) = (f ϕ y))
    (f_mu : forall ϕ y, (f (patt_mu ϕ) y) = (f ϕ y))
    (fs : Pattern -> svar -> svar)
    (fs_ex : forall ϕ Y, (fs (patt_exists ϕ) Y) = (fs ϕ Y))
    (fs_mu : forall ϕ Y, (fs (patt_mu ϕ) Y) = (fs ϕ Y))
  .
  Fixpoint ln2named_evar_open (sz : nat) (ϕ : Pattern) (y : evar) {struct sz}:
    size' ϕ <= sz ->
    well_formed ϕ ->
    let x := string2evar ("A" +:+ evar2string (ename ϕ)) in
    ln2named (evar_open y 0 ϕ) = rename_free_evar (ln2named (evar_open x 0 ϕ)) (f ϕ y) (ename ϕ)
  with ln2named_svar_open (sz : nat) (ϕ : Pattern) (Y : svar) {struct sz}:
    size' ϕ <= sz ->
    well_formed ϕ ->
    let X := string2svar ("B" +:+ svar2string (sname ϕ)) in
    ln2named (svar_open Y 0 ϕ) = rename_free_svar (ln2named (svar_open X 0 ϕ)) (fs ϕ Y) (sname ϕ)
  .
  Proof.
    all: intros Hsz Hwf; cbn.

    all: set (fun phi' =>
      let x := string2evar ("A" +:+ evar2string (ename phi')) in
      ln2named (evar_open x 0 phi')
    ) as ebody.
    all: replace (ln2named (evar_open (string2evar ("A" +:+ evar2string (ename ϕ)) ) 0 ϕ)) with (ebody ϕ) by (reflexivity).
    all: set (fun phi' => ln2named (svar_open (string2svar ("B" +:+ svar2string (sname phi'))) 0 phi')) as sbody.
    all: replace (ln2named (svar_open (string2svar ("B" +:+ svar2string (sname ϕ)) ) 0 ϕ)) with (sbody ϕ) by (reflexivity).
    {
      apply what_we_want_evar with (sname := sname)(sz := sz).
      { intros. simp ln2named. reflexivity. }
      { intros. simp ln2named. reflexivity. }
      { intros. simp ln2named. reflexivity. }
      { intros. simp ln2named. reflexivity. }
      { intros. simp ln2named. reflexivity. }
      { intros. simp ln2named. reflexivity. }
      { intros. simp ln2named. reflexivity. }
      { intros. simp ln2named. reflexivity. }
      { intros. simp ln2named. reflexivity. }
      { intros. simp ln2named. reflexivity. }
      { intros. simp ln2named. reflexivity. }
      { intros. simp ln2named. reflexivity. }
      {
        intros. unfold ebody. cbn.
        simp ln2named.
        rewrite cancele2.
        fold (evar_open ((string2evar
        ("A" +:+ evar2string (ename ϕ1) +:+ evar2string (ename ϕ2)))) 0 ϕ1).
        rewrite evar_open_closed.
        { wf_auto2. }
        fold (evar_open ((string2evar
        ("A" +:+ evar2string (ename ϕ1) +:+ evar2string (ename ϕ2)))) 0 ϕ2).
        rewrite evar_open_closed.
        { wf_auto2. }
        rewrite evar_open_closed.
        { wf_auto2. }
        rewrite evar_open_closed.
        { wf_auto2. }
        reflexivity.
      }
      {
        intros. unfold ebody. cbn.
        simp ln2named.
        rewrite cancele2.
        fold (evar_open ((string2evar
        ("A" +:+ evar2string (ename ϕ1) +:+ evar2string (ename ϕ2)))) 0 ϕ1).
        rewrite evar_open_closed.
        { wf_auto2. }
        fold (evar_open ((string2evar
        ("A" +:+ evar2string (ename ϕ1) +:+ evar2string (ename ϕ2)))) 0 ϕ2).
        rewrite evar_open_closed.
        { wf_auto2. }
        rewrite evar_open_closed.
        { wf_auto2. }
        rewrite evar_open_closed.
        { wf_auto2. }
        reflexivity.
      }
      { intros. simp ln2named. cbn. reflexivity. }
      {
        intros. unfold ebody. cbn. simp ln2named. cbn.
        fold (evar_open ((string2evar ("A" +:+ evar2string (ename ϕ0)))) 0 ϕ0).
        rewrite -> evar_open_wfc_aux with (phi := ϕ0) (db1 := 0).
        3: { wf_auto2. }
        2: { lia. }
        reflexivity.
      }
      { intros. simp ln2named. cbn. reflexivity. }
    }

    apply what_we_want with (sname := sname).
    { intros. cbn. simp ln2named. cbn.
      f_equal. rewrite svar_open_closed.
      { wf_auto2. }
      reflexivity.
    }
    { intros. simp ln2named. cbn. reflexivity. }
    { intros. reflexivity. }
    { intros. cbn. 
      intros HContra.
      apply (@f_equal _ _ evar2string) in HContra.
      rewrite cancele2 in HContra.
      apply (@f_equal _ _ list_ascii_of_string) in HContra.
      rewrite list_ascii_of_string_app in HContra.
      apply (@f_equal _ _ List.length) in HContra.
      rewrite app_length in HContra. cbn in HContra.
      clear -HContra. lia.
    }
    { intros. reflexivity. }
    { intros. reflexivity. }
    {
      (* ∀ ϕ0 : Pattern, ename ϕ0 ∉ named_free_evars (ebody ϕ0) *)
      intros phi0. unfold ebody.
      intros HContra.
      apply named_free_evars_ln2named in HContra.
      destruct HContra as [HContra|HContra].
      {
        rewrite free_evars_evar_open'' in HContra.
        destruct HContra as [[HContra1 HContra2]|HContra].
        {
          apply (@f_equal _ _ evar2string) in HContra1.
          rewrite cancele2 in HContra1.
          apply (@f_equal _ _ list_ascii_of_string) in HContra1.
          rewrite list_ascii_of_string_app in HContra1.
          apply (@f_equal _ _ List.length) in HContra1.
          rewrite app_length in HContra1. cbn in HContra1.
          clear -HContra1. lia.
        }
        {
          eapply ename_not_in_free. apply HContra.
        }
      }
      {
        induction phi0; cbn in HContra.
        {
          destruct HContra as [s HContra].
          apply (@f_equal _ _ evar2string) in HContra.
          rewrite 2!cancele2 in HContra.
          inversion HContra.
        }
        {
          destruct HContra as [s HContra].
          apply (@f_equal _ _ evar2string) in HContra.
          rewrite 2!cancele2 in HContra.
          inversion HContra.
        }
        {
          destruct HContra as [s HContra].
          apply (@f_equal _ _ evar2string) in HContra.
          rewrite 2!cancele2 in HContra.
          inversion HContra.
        }
        {
          destruct HContra as [s HContra].
          apply (@f_equal _ _ evar2string) in HContra.
          rewrite 2!cancele2 in HContra.
          inversion HContra.
        }
        {
          destruct HContra as [s HContra].
          apply (@f_equal _ _ evar2string) in HContra.
          rewrite 2!cancele2 in HContra.
          inversion HContra.
        }
        {
          {
            destruct HContra as [s HContra].
            apply (@f_equal _ _ evar2string) in HContra.
            rewrite 2!cancele2 in HContra.
            apply IHphi0_1.
            apply (@f_equal _ _ list_ascii_of_string) in HContra.
            rewrite 2!list_ascii_of_string_app in HContra.
            assert (HA: firstn 1 (list_ascii_of_string (evar2string (ename phi0_1))) = list_ascii_of_string "A").
            {
              cbn in HContra. cbn.
              destruct (list_ascii_of_string (evar2string (ename phi0_1))) eqn:Heq.
              {
                exfalso. apply ename_nonempty in Heq. exact Heq.
              }
              {
                cbn. rewrite take_0.
                cbn in HContra. inversion HContra.
                reflexivity.
              }
            }
            remember (firstn (List.length (list_ascii_of_string (evar2string (ename phi0_1))) - 1) (list_ascii_of_string s)) as mys.
            exists (string_of_list_ascii mys).
            subst mys.
            assert (Hs: list_ascii_of_string s = skipn 1 (list_ascii_of_string (evar2string (ename phi0_1)) ++
              list_ascii_of_string (evar2string (ename phi0_2)))).
            {
              rewrite HContra. cbn. rewrite drop_0. reflexivity.
            }
            rewrite Hs. clear Hs.
            remember (ename phi0_1) as ev.
            match goal with
            | [ |- ?l = ?r] => cut (evar2string l = evar2string r)
            end.
            {
              intros HH. congruence.
            }
            rewrite cancele2.
            match goal with
            | [ |- ?l = ?r] => cut (list_ascii_of_string l = list_ascii_of_string r)
            end.
            {
              intros HH. apply list_ascii_of_string_inj in HH. exact HH.
            }
            rewrite list_ascii_of_string_app.
            rewrite list_ascii_of_string_of_list_ascii.
            remember (list_ascii_of_string (evar2string ev)) as l.
            rewrite -skipn_firstn_comm.
            rewrite take_app.
            rewrite -HA.
            rewrite (take_drop 1 l).
            reflexivity.
          }
        }
        {
          destruct HContra as [s HContra].
          apply (@f_equal _ _ evar2string) in HContra.
          rewrite 2!cancele2 in HContra.
          inversion HContra.
        }
        {
          destruct HContra as [s HContra].
          apply (@f_equal _ _ evar2string) in HContra.
          rewrite 2!cancele2 in HContra.
          apply IHphi0_1.
          apply (@f_equal _ _ list_ascii_of_string) in HContra.
          rewrite 2!list_ascii_of_string_app in HContra.
          assert (HA: firstn 1 (list_ascii_of_string (evar2string (ename phi0_1))) = list_ascii_of_string "A").
          {
            cbn in HContra. cbn.
            destruct (list_ascii_of_string (evar2string (ename phi0_1))) eqn:Heq.
            {
              exfalso. apply ename_nonempty in Heq. exact Heq.
            }
            {
              cbn. rewrite take_0.
              cbn in HContra. inversion HContra.
              reflexivity.
            }
          }
          remember (firstn (List.length (list_ascii_of_string (evar2string (ename phi0_1))) - 1) (list_ascii_of_string s)) as mys.
          exists (string_of_list_ascii mys).
          subst mys.
          assert (Hs: list_ascii_of_string s = skipn 1 (list_ascii_of_string (evar2string (ename phi0_1)) ++
            list_ascii_of_string (evar2string (ename phi0_2)))).
          {
            rewrite HContra. cbn. rewrite drop_0. reflexivity.
          }
          rewrite Hs. clear Hs.
          remember (ename phi0_1) as ev.
          match goal with
          | [ |- ?l = ?r] => cut (evar2string l = evar2string r)
          end.
          {
            intros HH. congruence.
          }
          rewrite cancele2.
          match goal with
          | [ |- ?l = ?r] => cut (list_ascii_of_string l = list_ascii_of_string r)
          end.
          {
            intros HH. apply list_ascii_of_string_inj in HH. exact HH.
          }
          rewrite list_ascii_of_string_app.
          rewrite list_ascii_of_string_of_list_ascii.
          remember (list_ascii_of_string (evar2string ev)) as l.
          rewrite -skipn_firstn_comm.
          rewrite take_app.
          rewrite -HA.
          rewrite (take_drop 1 l).
          reflexivity.
        }
        { auto with nocore. }
        { auto with nocore. }
      }
    }
    {
      reflexivity.
    }
    
    
    {
      intros. cbn. reflexivity.
    }
    {
      intros. rewrite f_mu. reflexivity.
    }
    {
      intros. cbn. reflexivity.
    }
    {
      intros. unfold ebody. cbn. simp ln2named. reflexivity.
    }
    {
      intros. unfold sbody. cbn.
    }
  Qed.


End concrete.

Ltac invert_tuples :=
  repeat (match goal with
          | [H: (?x1,?y1)=(?x2,?y2) |- _] => inversion H; clear H; subst
          end).

Ltac do_rewrites_everywhere := 
  repeat (match goal with
  | [H: ?l = ?r , H' : _ |- _] => rewrite H in H'; simpl in H'
  end).

Ltac case_match_in_hyp H :=
  lazymatch type of H with
  | context [ match ?x with _ => _ end ] => destruct x eqn:?
  end.


Section ln2named.
  Context
    {Σ : Signature}
    (string2evar : string -> option evar)
    (evar2string : evar -> string)
    (string2svar : string -> option svar)
    (svar2string : svar -> string)
    (sym2string : symbols -> string)
    (string2sym : string -> option symbols)
    (s2ev_useful : forall str, exists ev, string2evar ("E" +:+ str) = Some ev)
    (s2ev_empty : forall str, (forall str', str <> "E" +:+ str' ) -> string2evar str = None)
    (s2sv_useful : forall str, exists sv, string2svar ("S" +:+ str) = Some sv)
    (s2sv_empty : forall str, (forall str', str <> "S" +:+ str' ) -> string2svar str = None)
    (s2sym_useful : forall str, exists sv, string2sym ("Y" +:+ str) = Some sv)
    (s2sym_empty : forall str, (forall str', str <> "Y" +:+ str' ) -> string2sym str = None)
    (cancele1 : forall ev str, string2evar str = Some ev -> evar2string ev = str)
    (cancele2 : forall ev, string2evar (evar2string ev) = Some ev)
    (cancels1 : forall sv str, string2svar str = Some sv -> svar2string sv = str)
    (cancels2 : forall sv, string2svar (svar2string sv) = Some sv)
    (cancelsym1 : forall sym str, string2sym str = Some sym -> sym2string sym = str)
    (cancelsym2 : forall sym, string2sym (sym2string sym) = Some sym)
    (evar_svar_distinct: forall x X, evar2string x <> svar2string X)
    (evar_sym_distinct: forall x s, evar2string x <> sym2string s)
    (sym_svar_distinct: forall s X, sym2string s <> svar2string X)
    (*sym2string_inj : Inj (=) (=) sym2string*)
  .
  #[local]
  Instance evar2string_inj : Inj (=) (=) evar2string.
  Proof. intros x y Hxy. apply (@f_equal string _ string2evar) in Hxy.
    do 2 rewrite cancele2 in Hxy. inversion Hxy. reflexivity.
  Qed.

  #[local]
  Instance svar2string_inj : Inj (=) (=) svar2string.
  Proof. intros x y Hxy. apply (@f_equal string _ string2svar) in Hxy.
    do 2 rewrite cancels2 in Hxy. inversion Hxy. reflexivity.
  Qed.
(*
  #[local]
  Instance string2evar_inj : Inj (=) (=) string2evar.
  Proof. apply cancel_inj. Qed.

  #[local]
  Instance string2svar_inj : Inj (=) (=) string2svar.
  Proof. apply cancel_inj. Qed.
*)  
  Fixpoint ln2str (ϕ : Pattern) : string :=
    match ϕ with
    | patt_bound_evar n => (*"BE" ++ pretty n*) ""
    | patt_bound_svar n => (*"BS" ++ pretty n*) ""
    | patt_free_evar x => (*"FE" ++*) evar2string x 
    | patt_free_svar X => (*"FS" ++*) svar2string X
    | patt_app ϕ₁ ϕ₂ => "(" ++ ln2str ϕ₁ ++ ")A(" ++ ln2str ϕ₂ ++ ")"
    | patt_imp ϕ₁ ϕ₂ => "(" ++ ln2str ϕ₁ ++ ")I(" ++ ln2str ϕ₂ ++ ")"
    | patt_sym s => sym2string s
    | patt_bott => "B"
    | patt_exists ϕ' => "X" ++ ln2str ϕ'
    | patt_mu ϕ' => "M" ++ ln2str ϕ'
    end
  .

  #[global]
  Lemma ln2str_inj :
    forall ϕ₁ ϕ₂,
      well_formed ϕ₁ ->
      well_formed ϕ₂ ->
      ln2str ϕ₁ = ln2str ϕ₂ ->
      ϕ₁ = ϕ₂
  .
    intros ϕ₁ ϕ₂.
    move: ϕ₂.
    induction ϕ₁; intros ϕ₂ wfϕ₁ wfϕ₂ H;
      try (solve[(destruct ϕ₂; cbn in *; simpl; inversion H as [H']; congruence)]);
      cbn in H.
    {
      apply (@f_equal string _ string2evar) in H.
      rewrite cancele2 in H.
      destruct ϕ₂; cbn in *.
      {
        rewrite cancele2 in H.
        inversion H.
        reflexivity.
      }
      all: symmetry in H.
      {
        exfalso.
        apply cancele1 in H.
        eapply evar_svar_distinct.
        exact H.
      }
      all: try solve [
        rewrite s2ev_empty in H;
        [intros str' Hstr'; inversion Hstr'|inversion H]
      ].
      apply cancele1 in H.
      exfalso. eapply evar_sym_distinct. exact H.
    }
    {
      apply (@f_equal string _ string2svar) in H.
      rewrite cancels2 in H.
      destruct ϕ₂; cbn in *.
      {
        exfalso.
        symmetry in H.
        apply cancels1 in H.
        symmetry in H.
        eapply evar_svar_distinct.
        exact H.
      }
      all: symmetry in H.
      all: try solve [
        rewrite s2sv_empty in H;
        [intros str' Hstr'; inversion Hstr'|inversion H]
      ].
      2: {
        apply cancels1 in H.
        exfalso. eapply sym_svar_distinct. symmetry. exact H.        
      }
      rewrite cancels2 in H.
      inversion H.
      reflexivity.
    }
    {
      cbn in wfϕ₁.
      case_match; try lia; try congruence.
    }
    {
      unfold well_formed,well_formed_closed in wfϕ₁.
      cbn in wfϕ₁.
      case_match; try lia; cbn in wfϕ₁; try congruence.
    }
    {
      apply (@f_equal string _ string2sym) in H.
      rewrite cancelsym2 in H.
      destruct ϕ₂; cbn in *.
      all: symmetry in H.
      all: try solve [
        rewrite s2sym_empty in H;
        [intros str' Hstr'; inversion Hstr'|inversion H]
      ].
      3: {
        rewrite cancelsym2 in H.
        inversion H.
        reflexivity.
      }
      {
        apply cancelsym1 in H.
        exfalso. eapply evar_sym_distinct. symmetry. exact H.        
      }
      {
        apply cancelsym1 in H.
        exfalso. eapply sym_svar_distinct. exact H.        
      }
    }
  Abort.


  Equations? ln2named (ϕ : Pattern) : NamedPattern by wf (size' ϕ) lt :=
  ln2named (patt_bound_evar _) => npatt_bott ;
  ln2named (patt_bound_svar _) => npatt_bott ;
  ln2named (patt_free_evar x) => npatt_evar x ;
  ln2named (patt_free_svar X) => npatt_svar X ;
  ln2named patt_bott := npatt_bott ;
  ln2named (patt_sym s) := npatt_sym s ;
  ln2named (patt_imp ϕ₁ ϕ₂) := npatt_imp (ln2named ϕ₁) (ln2named ϕ₂) ;
  ln2named (patt_app ϕ₁ ϕ₂) := npatt_app (ln2named ϕ₁) (ln2named ϕ₂) ;
  ln2named (patt_exists ϕ') with (string2evar ("E" +:+ ln2str ϕ')) => {
    | Some x => npatt_exists x (ln2named (evar_open x 0 ϕ'))
    | None => npatt_bott
  } ;
  ln2named (patt_mu ϕ') with (string2svar ("S" +:+ ln2str ϕ')) => {
    | Some X => npatt_mu X (ln2named (svar_open X 0 ϕ'))
    | None => npatt_bott
  }.
  Proof.
    all: simpl; try lia.
    { rewrite evar_open_size'. simpl. lia. }
    { rewrite svar_open_size'. simpl. lia. }
  Qed.

  Lemma not_s2e_l2s_eo ϕ x dbi:
    well_formed_closed_ex_aux ϕ dbi ->
    x ∉ free_evars ϕ ->
    ~ (string2evar (ln2str (bevar_subst (patt_free_evar x) dbi ϕ)) = Some x)
  .
  Proof.
    move: x dbi.
    destruct ϕ; intros x' dbi Hwf Hfrx'; cbn in *; intros HContra.
    {
      rewrite elem_of_singleton in Hfrx'.
      apply Hfrx'. clear Hfrx'.
      apply cancele1 in HContra.
      apply (inj evar2string) in HContra. exact HContra.
    }
    {
      eapply evar_svar_distinct with (x := x')(X := x).
      apply cancele1 in HContra. exact HContra.
    }
    {
      clear Hfrx'.
      repeat case_match; try lia; cbn in *.
      { rewrite s2ev_empty in HContra.
        { intros str'. intros HContra'. inversion HContra'. }
        inversion HContra.
      }
      { subst. exfalso. clear -Hwf. congruence. }
      { subst. exfalso. clear -Hwf. congruence. }
    }
    {
      rewrite s2ev_empty in HContra.
      { intros str' HContra'. inversion HContra'. }
      inversion HContra.
    }
    {
      eapply evar_sym_distinct with (x := x') (s := sigma).
      apply cancele1 in HContra. exact HContra.
    }
    {
      rewrite s2ev_empty in HContra.
      {
        intros str' HContra'. inversion HContra'.
      }
      inversion HContra.
    }
    {
      rewrite s2ev_empty in HContra.
      {
        intros str' HContra'. inversion HContra'.
      }
      inversion HContra.
    }
    {
      rewrite s2ev_empty in HContra.
      {
        intros str' HContra'. inversion HContra'.
      }
      inversion HContra.
    }
    {
      rewrite s2ev_empty in HContra.
      {
        intros str' HContra'. inversion HContra'.
      }
      inversion HContra.
    }
    {
      rewrite s2ev_empty in HContra.
      {
        intros str' HContra'. inversion HContra'.
      }
      inversion HContra.
    }
  Qed.

  Lemma ln2named_evar_open ϕ y x:
    x ∉ free_evars ϕ ->
    y ∉ free_evars ϕ ->
    well_formed ϕ ->
    rename_free_evar (ln2named (evar_open x 0 ϕ)) y x = ln2named (evar_open y 0 ϕ)
  .
  Proof.
    unfold evar_open at 1.
    remember (size' ϕ) as sz.
    assert (Hsz: size' ϕ <= sz) by lia.
    clear Heqsz.
    move: ϕ Hsz y x.
    induction sz; intros ϕ Hsz y x.
    {
      destruct ϕ; cbn in *; exfalso; lia.
    }
    intros Hfrx Hfry Hwfϕ.
    destruct ϕ.
    {
      cbn in *.
      simp ln2named. simpl.
      destruct (decide (x = x0)) as [H|H].
      2: { reflexivity. }
      subst. exfalso. clear -Hfrx. set_solver.
    }
    {
      cbn in *. simp ln2named. simpl. reflexivity.
    }
    {
      cbn in *.
      repeat case_match; simpl in *; try lia.
      {
        subst.
        simp ln2named. simpl.
        case_match.
        { reflexivity. }
        contradiction.
      }
      {
        simp ln2named. simpl. reflexivity.
      }
    }
    {
      cbn in *. simp ln2named. simpl. reflexivity.
    }
    {
      cbn in *. simp ln2named. simpl. reflexivity.
    }
    {
      cbn in *.
      simp ln2named.
      cbn.
      rewrite IHsz.
      { lia. }
      { set_solver. }
      { set_solver. }
      { wf_auto2. }
      rewrite IHsz.
      { lia. }
      { set_solver. }
      { set_solver. }
      { wf_auto2. }
      reflexivity.
    }
    {
      cbn in *. simp ln2named. simpl. reflexivity.
    }
    {
      cbn in *.
      simp ln2named.
      cbn.
      rewrite IHsz.
      { lia. }
      { set_solver. }
      { set_solver. }
      { wf_auto2. }
      rewrite IHsz.
      { lia. }
      { set_solver. }
      { set_solver. }
      { wf_auto2. }
      reflexivity.
    }
    {
      cbn in *.
      simp ln2named.
      unfold ln2named_unfold_clause_9.
      destruct (string2evar ("E" +:+ ln2str (bevar_subst (patt_free_evar x) 1 ϕ))) eqn:Heq1,
               (string2evar ("E" +:+ ln2str (bevar_subst (patt_free_evar y) 1 ϕ))) eqn:Heq2.
      {
        cbn.
        destruct (decide (x = e)).
        {
          subst e.
          fold (evar_open x 1 ϕ).
          fold (evar_open y 1 ϕ).
          exfalso. eapply not_s2e_l2s_eo. 3: apply Heq1.
          { wf_auto2. }
          { assumption. }
        }
        destruct (decide (y = e0)).
        {
          subst e0.
          exfalso. eapply not_s2e_l2s_eo. 3: apply Heq2.
          { wf_auto2. }
          { assumption. }
        }
        destruct (decide (e = e0)).
        {
          subst.
          apply cancele1 in Heq1.
          apply cancele1 in Heq2.
          rewrite Heq2 in Heq1.
          apply f_equal.
          fold (evar_open x 1 ϕ).
          fold (evar_open y 1 ϕ).
          rewrite -> evar_open_comm_higher at 1.
          2: { lia. }
          cbn.
          unfold evar_open.
          rewrite IHsz.
          {
            fold (evar_open e0 0 ϕ).
            rewrite evar_open_size'.
            lia.
          }
          {
            rewrite free_evars_evar_open''.
            naive_solver.
          }
          {
            rewrite free_evars_evar_open''.
            naive_solver.
          }
          {
            wf_auto2.
          }
          replace 0 with (Nat.pred 1) by reflexivity.
          rewrite -evar_open_comm_higher.
          { cbn. lia. }
          cbn.
          reflexivity.
        }
        (* Huh, it obviously does not hold. *)
        admit.
      }
      admit.
    }
    admit.
  Abort.
(*

  Lemma ln2named_evar_open ϕ y x:
    (string2evar ("E" +:+ ln2str ϕ)) = Some x ->
    x ∉ free_evars ϕ ->
    y ∉ free_evars ϕ ->
    well_formed ϕ ->
    rename_free_evar (ln2named (evar_open x 0 ϕ)) y x = ln2named (evar_open y 0 ϕ)
  .
  Proof.
    unfold evar_open at 1.
    remember (size' ϕ) as sz.
    assert (Hsz: size' ϕ <= sz) by lia.
    clear Heqsz.
    move: ϕ Hsz y x.
    induction sz; intros ϕ Hsz y x.
    {
      destruct ϕ; cbn in *; exfalso; lia.
    }
    intros Hx Hfrx Hfry Hwfϕ.
    destruct ϕ.
    {
      cbn in *.
      simp ln2named. simpl.
      destruct (decide (x = x0)) as [H|H].
      2: { reflexivity. }
      subst. rewrite elem_of_singleton in Hfry. exfalso. clear -Hfrx. set_solver.
    }
    {
      cbn in *. simp ln2named. simpl. reflexivity.
    }
    {
      cbn in *.
      repeat case_match; simpl in *; try lia.
      {
        subst.
        simp ln2named. simpl.
        case_match.
        { reflexivity. }
        contradiction.
      }
      {
        simp ln2named. simpl. reflexivity.
      }
    }
    {
      cbn in *. simp ln2named. simpl. reflexivity.
    }
    {
      cbn in *. simp ln2named. simpl. reflexivity.
    }
    {
      cbn in *.
      simp ln2named.
      cbn.
      rewrite IHsz.
      { lia. }
      { set_solver. }
      { set_solver. }
      { wf_auto2. }
      rewrite IHsz.
      { lia. }
      { set_solver. }
      { set_solver. }
      { wf_auto2. }
      reflexivity.
    }
    {
      cbn in *. simp ln2named. simpl. reflexivity.
    }
    {
      cbn in *.
      simp ln2named.
      cbn.
      rewrite IHsz.
      { lia. }
      { set_solver. }
      { set_solver. }
      { wf_auto2. }
      rewrite IHsz.
      { lia. }
      { set_solver. }
      { set_solver. }
      { wf_auto2. }
      reflexivity.
    }
    {
      cbn in *.
      simp ln2named.
      unfold ln2named_unfold_clause_9.
      destruct (string2evar (ln2str (bevar_subst (patt_free_evar x) 1 ϕ))) eqn:Heq1,
               (string2evar (ln2str (bevar_subst (patt_free_evar y) 1 ϕ))) eqn:Heq2.
      {
        cbn.
        destruct (decide (x = e)).
        {
          subst e.
          exfalso. eapply not_s2e_l2s_eo. 3: apply Heq1.
          { wf_auto2. }
          { assumption. }
        }
        destruct (decide (y = e0)).
        {
          subst e0.
          exfalso. eapply not_s2e_l2s_eo. 3: apply Heq2.
          { wf_auto2. }
          { assumption. }
        }
        destruct (decide (e = e0)).
        {
          subst.
          apply cancele1 in Heq1.
          apply cancele1 in Heq2.
          rewrite Heq2 in Heq1.
          apply f_equal.
          fold (evar_open x 1 ϕ).
          fold (evar_open y 1 ϕ).
          rewrite -> evar_open_comm_higher at 1.
          2: { lia. }
          cbn.
          unfold evar_open.
          rewrite IHsz.
          {
            fold (evar_open e0 0 ϕ).
            rewrite evar_open_size'.
            lia.
          }
          {
            rewrite free_evars_evar_open''.
            naive_solver.
          }
          {
            rewrite free_evars_evar_open''.
            naive_solver.
          }
          {
            wf_auto2.
          }
          replace 0 with (Nat.pred 1) by reflexivity.
          rewrite -evar_open_comm_higher.
          { cbn. lia. }
          cbn.
          reflexivity.
        }
        (* Huh, it obviously does not hold. *)
        admit.
      }
      admit.
    }
    admit.
  Abort.
*)
(*
  Lemma ln2named_evar_open ϕ y:
    ln2named (evar_open y 0 ϕ)
    = rename_free_evar
      (ln2named (evar_open (string2evar ("E" +:+ ln2str ϕ)) 0 ϕ))  
      y
      (string2evar ("E" +:+ ln2str ϕ))
  .
  Proof.
    unfold evar_open at 1.
    remember (size' ϕ) as sz.
    assert (Hsz: size' ϕ <= sz) by lia.
    clear Heqsz.
    move: ϕ Hsz y.
    induction sz; intros ϕ Hsz y.
    {
      destruct ϕ; cbn in *; exfalso; lia.
    }
    destruct ϕ.
    {
      cbn in *.
      simp ln2named. simpl.
      destruct (decide (string2evar ("FE" +:+ evar2string x) = x)) as [H|H].
      2: { reflexivity. }
      exfalso.
      rewrite <- (cancel string2evar evar2string x) in H at 2.
      apply (inj string2evar) in H.
      match type of H with
      | ?l = ?r => assert (String.length l = String.length r) by congruence
      end.
      simpl in H0.
      lia.
    }
    {
      cbn in *. simp ln2named. simpl. reflexivity.
    }
    {
      cbn in *.
      repeat case_match; simpl in *; try lia.
      {
        subst.
        simp ln2named. simpl.
        case_match.
        { reflexivity. }
        contradiction.
      }
      {
        simp ln2named. simpl. reflexivity.
      }
    }
    {
      cbn in *. simp ln2named. simpl. reflexivity.
    }
    {
      cbn in *. simp ln2named. simpl. reflexivity.
    }
    {
      cbn in Hsz.
      remember (ln2str (patt_app ϕ1 ϕ2)) as zz.
      cbn. simp ln2named. simpl.
      rewrite IHsz;[lia|].
      remember (ln2named (evar_open (string2evar (ln2str ϕ1)) 0 ϕ1))
        as ϕ1'.
      rewrite IHsz;[lia|].
      remember (ln2named (evar_open (string2evar (ln2str ϕ2)) 0 ϕ2))
        as ϕ2'.
      rewrite IHsz;[lia|].
      rewrite -Heqϕ1'.
      rewrite IHsz;[lia|].
      rewrite -Heqϕ2'.
      (*
      remember (string2evar ("(" +:+ ln2str ϕ1 +:+ ")A(" +:+ ln2str ϕ2 +:+ ")")) as y2.
      remember (string2evar (ln2str ϕ1)) as z1.
      remember (string2evar (ln2str ϕ2)) as z2.
      *)
      rewrite rename_free_evar_chain.
      {
        subst ϕ1'. 
        (* NEED SOME IDEA HERE *)
        intros HContra.
        (*
          Consider [HContra].
          Then at least one of the following has to hold:
          - (a) [y2 = z1]
          - (b) y2 ∈ free_evars ϕ1
          - (c) there exists some subformula ϕsub of ϕ1
                nested under some [k] existential quantifiers
                such that y2 = ln2str ϕsub 
        *)
        subst y2. 

        unfold evar_open.
        rewrite IHsz.
        { lia. }
        rewrite IHsz.
        { lia. }
        intros HContra.
        (* NEED SOME IDEA HERE *)
        subst z1 z2. clear IHsz. 
      }
      f_equal.
    }
  Abort.
*)      
  Definition pf_ln2named
    (Γ : Theory)
    (ϕ : Pattern)
    (wfϕ : well_formed ϕ)
    (pf : ML_proof_system Γ ϕ)
    : NP_ML_proof_system (ln2named <$> Γ) (ln2named ϕ).
  Proof.
    induction pf.
    {
      apply N_hypothesis.
      { admit. (* WF *)}
      {
        rewrite elem_of_fmap.
        exists axiom.
        split;[reflexivity|assumption].
      }
    }
    {
      simp ln2named.
      apply N_P1.
      { admit. (* WF *)}
      { admit. (* WF *)}
    }
    {
      simp ln2named.
      apply N_P2.
      { admit. (* WF *)}
      { admit. (* WF *)}
      { admit. (* WF *)}
    }
    {
      simp ln2named.
      apply N_P3.
      { admit. (* WF *)}
    }
    {
      simp ln2named.
      simp ln2named in IHpf2.
      eapply N_Modus_ponens.
      4: {
        apply IHpf2.
        wf_auto2.
      }
      3: {
        apply IHpf1.
        wf_auto2.
      }
      { admit. (* WF *)}
      { admit. (* WF *)}
    }
    {
      unfold instantiate.
      fold (evar_open y 0 phi).
      simp ln2named.
      Fail apply N_Ex_quan.
      simpl.
      unfold evar_open.
      apply N_Ex_quan.
    }
  Defined.
  

End ln2named.

Print ML_proof_system.



(* In an empty context, this rewrites: *)
(* ∃ (x.x) /\ (∃ y.y) ~> (∃ x.x) /\ (∃ x.x) *)
(* But in some other context C, it might rewrite *)
(* C[∃ (x.x) /\ (∃ y.y)] ~> C[(∃ z.z) /\ (∃ z.z)] *)
(* because we might see some ∃ z.z in the context C. *)


(* TODO we have to implement the two-phase approach to proof system translation.
   The cache-based on was too complicated, so I removed the proofs from this file.
*)
(*
Record AlphaConversion {Σ : Signature} :=
  {
    ac_list : list evar ;
  }.

Definition AlphaConversion_valid {Σ : Signature}
  (ac : AlphaConversion) (nϕ : NamedPattern)
  := (ac_list ac) ## elements (named_free_evars nϕ).

Print NamedPattern.
*)

(*
Definition head_or_id {Σ : Signature}
  (l : list evar) (p : NamedPattern) : NamedPattern 
  match l with
  | [] => p
  | (x::xs) => 
*)

Fixpoint number_of_exists
  {Σ : Signature} (ϕ : NamedPattern) : nat :=
  match ϕ with
  | npatt_app phi1 phi2
    => number_of_exists phi1 + number_of_exists phi2
  | npatt_imp phi1 phi2
    => number_of_exists phi1 + number_of_exists phi2
  | npatt_exists _ phi
    => S (number_of_exists phi)
  | npatt_mu _ phi
    => number_of_exists phi
  | _ => 0
  end.

  Fixpoint number_of_mus
  {Σ : Signature} (ϕ : NamedPattern) : nat :=
  match ϕ with
  | npatt_app phi1 phi2
    => number_of_mus phi1 + number_of_mus phi2
  | npatt_imp phi1 phi2
    => number_of_mus phi1 + number_of_mus phi2
  | npatt_exists _ phi
    => (number_of_mus phi)
  | npatt_mu _ phi
    => S ( number_of_mus phi)
  | _ => 0
  end.

Fixpoint rename {Σ : Signature}
  (bevs : list evar)
  (bsvs : list svar)
  (fevs : gmap evar evar)
  (fsvs : gmap svar svar)
  (nϕ : NamedPattern)
  : NamedPattern :=
  match nϕ with
  | npatt_evar x
    => match (fevs !! x) with
       | None => npatt_evar x
       | Some y => npatt_evar y
       end
  | npatt_svar X
       => match (fsvs !! X) with
          | None => npatt_svar X
          | Some Y => npatt_svar Y
          end
  | npatt_sym s => npatt_sym s
  | npatt_bott => npatt_bott
  | npatt_imp phi1 phi2 =>
    npatt_imp
      (rename bevs bsvs fevs fsvs phi1)
      (rename (drop (number_of_exists phi1) bevs)
              (drop (number_of_mus phi1) bsvs)
              fevs fsvs phi2) 
  | npatt_app phi1 phi2 =>
    npatt_app
      (rename bevs bsvs fevs fsvs phi1)
      (rename (drop (number_of_exists phi1) bevs)
      (drop (number_of_exists phi1) bsvs)
              fevs fsvs phi2) 
  | npatt_exists x phi =>
    match bevs with
    | [] => npatt_exists x phi
    | (y::ys)
      => npatt_exists y
          (rename ys bsvs (<[x:=y]>fevs) fsvs phi)
    end
  | npatt_mu X phi =>
    match bsvs with
    | [] => npatt_mu X phi
    | (Y::Ys)
      => npatt_mu Y
          (rename bevs Ys fevs (<[X:=Y]>fsvs) phi)
    end
  end.


  Record PartialBijection (A : Type)
    {_eqd : EqDecision A}
    {_cnt : Countable A}
     :=
  mkPartialBijection
  {
    pbr : gset (prod A A) ;
    pb1 : forall (x y1 y2 : A),
      (x,y1) ∈ pbr -> (x,y2) ∈ pbr -> y1 = y2 ;
    pb2 : forall (x1 x2 y : A),
      (x1,y) ∈ pbr -> (x2,y) ∈ pbr -> x1 = x2 ;
  }.

  Lemma pb_eq_dep (A : Type) 
    {_eqd : EqDecision A}
    {_cnt : Countable A}
    (s s' : gset (prod A A))
    pf1 pf1' pf2 pf2'
    : s = s' ->
      @mkPartialBijection A _eqd _cnt s pf1 pf2 = @mkPartialBijection A _eqd _cnt s' pf1' pf2'.
    Proof.
      intros H.
      subst s'.
      f_equal; apply proof_irrelevance.
    Qed.

  Arguments pbr {A%type_scope} {_eqd _cnt} p.

  Definition myswap {A : Type} (p : prod A A) : prod A A := (p.2, p.1).

  Program Definition pbr_converse {A : Type}
    {_eqd : EqDecision A}
    {_cnt : Countable A}
    (R : PartialBijection A) : PartialBijection A
  := {|
    pbr := (set_map myswap (pbr R))  ;
  |}.
  Next Obligation.
    intros ??????? H1 H2.
    rewrite elem_of_map in H1.
    rewrite elem_of_map in H2.
    destruct H1 as [[x11 x12] [H11 H12]].
    destruct H2 as [[x21 x22] [H21 H22]].
    simpl in *.
    inversion H11; clear H11; inversion H21; clear H21; subst.
    destruct R as [r pf1 pf2]; simpl in *.
    naive_solver.
  Qed.
  Next Obligation.
    intros ??????? H1 H2.
    rewrite elem_of_map in H1.
    rewrite elem_of_map in H2.
    destruct H1 as [[x11 x12] [H11 H12]].
    destruct H2 as [[x21 x22] [H21 H22]].
    simpl in *.
    inversion H11; clear H11; inversion H21; clear H21; subst.
    destruct R as [r pf1 pf2]; simpl in *.
    naive_solver.
  Qed.
 
  Lemma pbr_converse_sym (A : Type)
    {_eqd : EqDecision A}
    {_cnt : Countable A}
    (R : PartialBijection A)
    : forall (x y : A), ((x,y) ∈ (pbr (pbr_converse R))) <-> ((y,x) ∈ (pbr R)).
  Proof.
    intros x y.
    destruct R as [r pf1 pf2]; simpl.
    rewrite elem_of_map.
    unfold myswap.
    split; intros H.
    {
      destruct H as [[a1 a2] [H1 H2]].
      simpl in *.
      naive_solver.
    }
    {
      exists (y,x).
      split;[reflexivity|assumption].
    }
  Qed.

  Definition related {A : Type} (u v : prod A A) : Prop
  := u.1 = v.1 \/ u.2 = v.2.

  Definition unrelated {A : Type} (u v : prod A A) : Prop
  := ~ (related u v).

  #[global]
  Instance related_dec (A : Type)
    {eq_dec : EqDecision A}
  : RelDecision (@unrelated A).
  Proof.
    solve_decision.
  Defined.

  Program Definition pb_update
  {A : Type}
  {_eqd : EqDecision A}
  {_cnt : Countable A}
  (pb : PartialBijection A)
  (x y : A)
  : PartialBijection A := {|
    pbr := (filter (unrelated (x,y)) (pbr pb) ) ∪ {[ (x,y) ]} ;
  |}.
  Next Obligation.
    intros ???? ????? H1 H2.
    rewrite elem_of_union in H1.
    rewrite elem_of_union in H2.
    rewrite elem_of_singleton in H1.
    rewrite elem_of_singleton in H2.
    rewrite elem_of_filter in H1.
    rewrite elem_of_filter in H2.
    destruct pb.
    unfold unrelated,related in *.
    simpl in *.
    naive_solver.
  Qed.
 Next Obligation.
  intros ???? ????? H1 H2.
  rewrite elem_of_union in H1.
  rewrite elem_of_union in H2.
  rewrite elem_of_singleton in H1.
  rewrite elem_of_singleton in H2.
  rewrite elem_of_filter in H1.
  rewrite elem_of_filter in H2.
  destruct pb.
  unfold unrelated,related in *.
  simpl in *.
  naive_solver.
 Qed.

 Lemma pbr_update_converse
  {A : Type}
  {_eqd : EqDecision A}
  {_cnt : Countable A}
  (R : PartialBijection A)
  : forall x y, pbr_converse (pb_update R x y) = pb_update (pbr_converse R) y x.
  Proof.
    intros x y.
    destruct R as [r pf1 pf2]; simpl in *.
    unfold pb_update,pbr_converse; simpl.
    apply pb_eq_dep.
    rewrite set_map_union_L.
    rewrite set_map_singleton_L.
    simpl.

    cut ((@set_map (A * A) (gset (A * A)) _ (A * A) (gset (A * A)) _ _ _ myswap (filter (unrelated (x, y)) r)) = (filter (unrelated (y, x)) (set_map myswap r))).
    {
      intros H. rewrite H. reflexivity.
    }
    apply anti_symm with (S := @subseteq (gset (prod A A)) _).
    { apply _. }
    1,2: rewrite elem_of_subseteq; intros x0 Hx0.
    {
      rewrite elem_of_map in Hx0.
      destruct Hx0 as [[x' y'] [Hx'y'1 Hx'y'2]].
      rewrite elem_of_filter in Hx'y'2.
      rewrite elem_of_filter.
      rewrite elem_of_map.
      unfold unrelated,related,myswap in *.
      simpl in *.
      subst.
      naive_solver.
    }
    {
      rewrite elem_of_filter in Hx0.
      rewrite elem_of_map in Hx0.
      rewrite elem_of_map.
      unfold unrelated,related,myswap in *.
      simpl in *.
      exists (x0.2, x0.1). simpl.
      rewrite -surjective_pairing.
      rewrite elem_of_filter. simpl.
      naive_solver.
    }
  Qed.

  Inductive alpha_equiv'
    {Σ : Signature}
    (R : PartialBijection evar)
    (R' : PartialBijection svar)
    : relation NamedPattern
    :=
    | ae_evar (x y : evar) (pf : (x, y) ∈ (pbr R))
      : alpha_equiv' R R' (npatt_evar x) (npatt_evar y)
    | ae_svar (X Y : svar) (pf : (X, Y) ∈ (pbr R'))
      : alpha_equiv' R R' (npatt_svar X) (npatt_svar Y)
    | ae_app
      (t t' u u' : NamedPattern)
      (tEt' : alpha_equiv' R R' t t')
      (uEu' : alpha_equiv' R R' u u')
      : alpha_equiv' R R' (npatt_app t u) (npatt_app t' u')
    | ae_imp
      (t t' u u' : NamedPattern)
      (tEt' : alpha_equiv' R R' t t')
      (uEu' : alpha_equiv' R R' u u')
      : alpha_equiv' R R' (npatt_imp t u) (npatt_imp t' u')
    | ae_bott : alpha_equiv' R R' npatt_bott npatt_bott
    | ae_sym (s : symbols) : alpha_equiv' R R' (npatt_sym s) (npatt_sym s) 
    | ae_ex (x y : evar) (t u : NamedPattern)
      (tEu : alpha_equiv'
        (pb_update R x y) R' t u)
      : alpha_equiv' R R'
        (npatt_exists x t)
        (npatt_exists y u)
    | ae_mu (X Y : svar) (t u : NamedPattern)
      (tEu : alpha_equiv'
        R (pb_update R' X Y) t u)
      : alpha_equiv' R R'
        (npatt_mu X t)
        (npatt_mu Y u)
  .

  #[global]
  Instance myswap_involutive
    (A : Type) :
    Involutive (=) (@myswap A).
  Proof.
    unfold Involutive.
    intros p.
    destruct p.
    unfold myswap.
    reflexivity.
  Qed.

  #[global]
  Instance myswap_inj (A : Type) : Inj (=) (=) (@myswap A).
  Proof.
    intros p1 p2 Hp1p2.
    unfold myswap in Hp1p2.
    destruct p1,p2.
    simpl in *.
    inversion Hp1p2.
    subst.
    reflexivity.
  Qed.

  Check @set_map.

  #[global]
  Instance set_map_involutive (A C : Type)
    {_eoAC : ElemOf A C}
    {_eleAC : Elements A C}
    {_singAC : Singleton A C}
    {_emptyC : Empty C}
    {_uniC : Union C}
    {_interC : Intersection C}
    {_difC : Difference C}
    {_eqdecA : EqDecision A}
    {_finac : FinSet A C}
    (f : A -> A)
    {_injF : Inj (=) (=) f}
    {_invF : Involutive (=) f}
    {_lC : LeibnizEquiv C}
    :
    Involutive (=) (@set_map A C _eleAC A C _singAC _emptyC _uniC f).
  Proof.
    intros x.
    unfold set_map.
    Search list_to_set elements.
    rewrite -[x in _ = x]list_to_set_elements_L.
    rewrite elements_list_to_set.
    {
      rewrite NoDup_fmap.
      apply NoDup_elements.
    }
    rewrite -list_fmap_compose.
    unfold compose.
    under [fun x0 => _]functional_extensionality => x0.
    {
      rewrite _invF.
      over.
    }
    fold (@Coq.Init.Datatypes.id A).
    rewrite list_fmap_id.
    reflexivity.
  Qed.

  #[global]
  Instance pbr_converse_involutive
    (A : Type)
    {_eqd : EqDecision A}
    {_cnt : Countable A}
     : Involutive (=) (@pbr_converse A _eqd _cnt).
  Proof.
    unfold Involutive.
    intros R.
    destruct R.
    apply pb_eq_dep.
    simpl.
    rewrite cancel.
    reflexivity.
  Qed.

  Lemma alpha_equiv_converse'
    {Σ : Signature}
    (R : PartialBijection evar)
    (R' : PartialBijection svar)
    : forall x y,
      alpha_equiv' R R' x y ->
      alpha_equiv' (pbr_converse R) (pbr_converse R') y x.
  Proof.
    intros x y H.
    induction H; try (solve [constructor; auto]).
      { constructor. rewrite pbr_converse_sym; assumption. }
      { constructor. rewrite pbr_converse_sym; assumption. }
      { constructor. rewrite pbr_update_converse in IHalpha_equiv'. assumption. }
      { constructor. rewrite pbr_update_converse in IHalpha_equiv'. assumption. }
  Qed.

  Lemma alpha'_sym
    {Σ : Signature}
    (R : PartialBijection evar)
    (R' : PartialBijection svar)
    : forall x y,
      alpha_equiv' R R' x y <->
      alpha_equiv' (pbr_converse R) (pbr_converse R') y x.
  Proof.
    intros x y; split; intros H.
    {
      apply alpha_equiv_converse'.
      apply H.
    }
    { 
      rewrite -[R](@cancel (PartialBijection evar) _ eq (@pbr_converse evar _ _)).
      rewrite -[R'](@cancel (PartialBijection svar) _ eq (@pbr_converse svar _ _)).
      apply alpha_equiv_converse'.
      apply H.
    }
  Qed.

  #[global]
  Instance alpha'_dec
    {Σ : Signature}
    (R : PartialBijection evar)
    (R' : PartialBijection svar)
    : RelDecision (alpha_equiv' R R').
  Proof.
    unfold RelDecision.
    intros x y.
    unfold Decision.
    move: R R' y.
    (*remember (size' x) as szx.*)
    induction x; intros R R' y; destruct y; try (solve [repeat constructor]);
      try (solve [right; intros HH; inversion HH]).
    {
      destruct (decide ((x, x0) ∈ pbr R)).
      {
        left. constructor. assumption.
      }
      {
        right. intros HContra. inversion HContra.
        contradiction.
      }
    }
    {
      destruct (decide ((X, X0) ∈ pbr R')).
      {
        left. constructor. assumption.
      }
      {
        right. intros HContra. inversion HContra.
        contradiction.
      }
    }
    {
      destruct (decide (sigma = sigma0)).
      {
        left. subst. constructor.
      }
      {
        right. intros HContra. inversion HContra.
        contradiction.
      }
    }
    {
      specialize (IHx1 R R' y1).
      specialize (IHx2 R R' y2).
      destruct IHx1, IHx2.
      {
        left. constructor; assumption.
      }
      all: right; intros HContra; inversion HContra; contradiction.
    }
    {
      specialize (IHx1 R R' y1).
      specialize (IHx2 R R' y2).
      destruct IHx1, IHx2.
      {
        left. constructor; assumption.
      }
      all: right; intros HContra; inversion HContra; contradiction.
    }
    {
      pose proof (IH' := IHx (pb_update R x x1) R' y).
      destruct IH'.
      {
        left. constructor. assumption.
      }
      {
        right. intros HContra. inversion HContra. clear HContra.
        subst.
        contradiction.
      }
    }
    {
      pose proof (IH' := IHx R (pb_update R' X X0) y).
      destruct IH'.
      {
        left. constructor. assumption.
      }
      {
        right. intros HContra. inversion HContra. clear HContra.
        subst.
        contradiction.
      }
    }
  Defined.

  Definition twice {A : Type} (x : A) : prod A A := (x, x).

  #[global]
  Instance twice_inj {A : Type} : Inj (=) (=) (@twice A).
  Proof.
    intros x y H.
    inversion H.
    reflexivity.
  Qed.

  Program Definition diagonal
    {A : Type}
    {_eqd : EqDecision A}
    {_cnt : Countable A}
    (S : gset A)
     : PartialBijection A :=
    {|
      pbr := set_map twice S ;
    |}.
  Next Obligation.
    intros ??????? H1 H2.
    rewrite elem_of_map in H1.
    rewrite elem_of_map in H2.
    destruct H1 as [w1 [Hw1 H'w1]].
    destruct H2 as [w2 [Hw2 H'w2]].
    inversion Hw1; clear Hw1; subst.
    inversion Hw2; clear Hw2; subst.
    reflexivity.
  Qed.
  Next Obligation.
    intros ??????? H1 H2.
    rewrite elem_of_map in H1.
    rewrite elem_of_map in H2.
    destruct H1 as [w1 [Hw1 H'w1]].
    destruct H2 as [w2 [Hw2 H'w2]].
    inversion Hw1; clear Hw1; subst.
    inversion Hw2; clear Hw2; subst.
    reflexivity.
  Qed.

  Definition alpha_equiv {Σ : Signature} (phi psi : NamedPattern) : Prop :=
    alpha_equiv'
      (diagonal (named_free_evars phi ∪ named_free_evars psi))
      (diagonal (named_free_svars phi ∪ named_free_svars psi))
      phi psi
  .

  #[global]
  Instance alpha_dec
    {Σ : Signature}
    : RelDecision alpha_equiv.
  Proof.
    intros x y.
    apply alpha'_dec.
  Defined.

  Lemma myswap_twice (A : Type) : myswap ∘ (@twice A) = twice.
  Proof.
    apply functional_extensionality.
    intros x. reflexivity.
  Qed.

  Lemma pbr_converse_diagonal (A : Type) {_eqd : EqDecision A} {_cnt : Countable A} (S : gset A):
    pbr_converse (diagonal S) = diagonal S.
  Proof.
    unfold diagonal,pbr_converse.
    apply pb_eq_dep.
    simpl.
    unfold set_map.
    apply anti_symm with (S := @subseteq (gset (prod A A)) _).
    { apply _. }
    1,2: rewrite elem_of_subseteq; intros x Hx.
    {
      rewrite elem_of_list_to_set in Hx.
      rewrite elem_of_list_to_set.
      rewrite elements_list_to_set in Hx.
      { apply NoDup_fmap.
        { apply _. }
        { apply NoDup_elements. }
      }
      rewrite -list_fmap_compose in Hx.
      rewrite myswap_twice in Hx.
      exact Hx.
    }
    {
      rewrite elem_of_list_to_set.
      rewrite elem_of_list_to_set in Hx.
      rewrite elements_list_to_set.
      { apply NoDup_fmap.
        { apply _. }
        { apply NoDup_elements. }
      }
      rewrite -list_fmap_compose.
      rewrite myswap_twice.
      exact Hx.
    }
  Qed.

  Lemma alpha_equiv_sym
  {Σ : Signature}
  : forall x y,
    alpha_equiv x y <->
    alpha_equiv y x.
  Proof.
    intros x y.
    unfold alpha_equiv.
    rewrite alpha'_sym.
    rewrite !pbr_converse_diagonal.
    rewrite [named_free_evars y ∪ named_free_evars x]union_comm_L.
    rewrite [named_free_svars y ∪ named_free_svars x]union_comm_L.
    apply reflexivity.
  Qed.

  Lemma alpha_equiv_refl {Σ : Signature} :
    forall p, alpha_equiv p p.
  Proof.
    intros p.
    unfold alpha_equiv.
    do 2 rewrite union_idemp_L.
    cut (forall R R', pbr (diagonal (named_free_evars p)) ⊆ (pbr R) ->
      pbr (diagonal (named_free_svars p)) ⊆ (pbr R')
     -> alpha_equiv' R R' p p).
    {
      intros H. apply H; apply reflexivity.
    }
    
    induction p; intros H1 H2; constructor; try set_solver.
    {
      simpl in *.
      apply IHp.
      {
        simpl in *.
        rewrite elem_of_subseteq.
        intros x0 Hx0.
        rewrite elem_of_map in Hx0.
        destruct Hx0 as [x' [Hx'1 Hx'2]].
        subst.
        rewrite elem_of_union.
        rewrite elem_of_singleton.
        unfold twice.
        destruct (decide (x = x')).
        {
          subst. right. reflexivity.
        }
        {
          left.
          rewrite elem_of_filter.
          unfold unrelated,related.
          simpl.
          set_solver.
        }
      }
      {
        assumption.
      }
    }
    {
      apply IHp.
      {
        assumption.
      }
      {
        simpl in *.
        rewrite elem_of_subseteq.
        intros [X1 X2] HX1X2.
        rewrite elem_of_map in HX1X2.
        destruct HX1X2 as [X3 [HX3 HX4]].
        unfold twice in *.
        simpl in *.
        inversion HX3. clear HX3. subst.
        rewrite elem_of_union. 
        destruct (decide (X3 = X)).
        {
          subst. right. rewrite elem_of_singleton. reflexivity.
        }
        {
          left.
          rewrite elem_of_filter.
          unfold unrelated,related.
          simpl.
          set_solver.
        }
      }
    }
  Qed.

  Fixpoint npfoldtopdown {Σ : Signature} {State : Type} 
    (f : State -> NamedPattern -> State)
    (state : State) (nϕ : NamedPattern)
    : (State)%type
  :=
    match nϕ with
    | npatt_evar x => f state (npatt_evar x)
    | npatt_svar X => f state (npatt_svar X)
    | npatt_sym s => f state (npatt_sym s)
    | npatt_bott => f state npatt_bott
    | npatt_imp nϕ1 nϕ2 =>
      let state' := f state (npatt_imp nϕ1 nϕ2) in
      let state'' := npfoldtopdown f state' nϕ1 in
      let state''' := npfoldtopdown f state' nϕ2 in
      state'''      
    | npatt_app nϕ1 nϕ2 =>
      let state' := f state (npatt_app nϕ1 nϕ2) in
      let state'' := npfoldtopdown f state' nϕ1 in
      let state''' := npfoldtopdown f state' nϕ2 in
      state'''
    | npatt_exists x nϕ' =>
      let state' := f state (npatt_exists x nϕ') in
      let state'' := npfoldtopdown f state' nϕ' in
      state''
    | npatt_mu X nϕ' =>
      let state' := f state (npatt_mu X nϕ') in
      let state'' := npfoldtopdown f state' nϕ' in
      state''
    end.
  

  Record CollapseState {Σ : Signature} := mkCollapseState {
    cs_history : list NamedPattern;
  }.

  Definition lookup_or
    {Σ : Signature}
    (state : CollapseState)
    (nϕ : NamedPattern)
    (owise : (CollapseState * NamedPattern)%type)
    : (CollapseState * NamedPattern)%type
    := match (list_find (alpha_equiv nϕ) (cs_history state)) with
    | Some (_, nϕ') => (state, nϕ')
    | None => owise
    end.


  Definition lookup_or_node
    {Σ : Signature}
    (state : CollapseState)
    (nϕ : NamedPattern)
    (owise : (CollapseState * NamedPattern)%type)
    : (CollapseState * NamedPattern)%type
    := lookup_or state nϕ (mkCollapseState Σ ((owise.2)::(cs_history owise.1)), (owise.2)).

  Definition lookup_or_leaf
    {Σ : Signature}
    (state : CollapseState)
    (nϕ : NamedPattern)
    : (CollapseState * NamedPattern)%type
    := lookup_or_node state nϕ (state, nϕ).


  Program Fixpoint collapse_aux
    {Σ : Signature}
    (state : CollapseState)
    (nϕ : NamedPattern)
    : (CollapseState * NamedPattern)%type
  :=
    match nϕ with
    | npatt_evar x
      => lookup_or_leaf state nϕ
    | npatt_svar X
      => lookup_or_leaf state nϕ
    | npatt_bott
      => lookup_or_leaf state nϕ
    | npatt_sym s
      => lookup_or_leaf state nϕ
    | npatt_imp nϕ1 nϕ2
      => lookup_or_node state nϕ
        ( let res := collapse_aux state nϕ1 in
          let res' := collapse_aux (res.1) nϕ2 in
          (res'.1, (npatt_imp res.2 res'.2))
        )
    | npatt_app nϕ1 nϕ2
        => lookup_or_node state nϕ
          ( let res := collapse_aux state nϕ1 in
            let res' := collapse_aux (res.1) nϕ2 in
            (res'.1, (npatt_app res.2 res'.2))
          )
    | npatt_exists x nϕ'
      => lookup_or_node state nϕ
        (
          let res := collapse_aux state nϕ' in
          (res.1, (npatt_exists x res.2))
        )
    | npatt_mu X nϕ'
        => lookup_or_node state nϕ
          (
            let res := collapse_aux state nϕ' in
            (res.1, (npatt_mu X res.2))
          )
    end.

    (* (exists x. x) ---> (exists y. (y ---> exists z. z)) *)

    Lemma lookup_or_leaf_alpha
      {Σ : Signature}
      (state : CollapseState)
      (nϕ : NamedPattern)
      : alpha_equiv (lookup_or_leaf state nϕ).2 nϕ.
    Proof.
      unfold lookup_or_leaf, lookup_or_node, lookup_or.
      simpl.
      destruct (list_find (alpha_equiv nϕ) (cs_history state)) as [[n phi] |] eqn:Heq; simpl.
      {
        rewrite list_find_Some in Heq.
        destruct Heq as [H1 [H2 H3]].
        apply alpha_equiv_sym.
        assumption.
      }
      {
        apply alpha_equiv_refl.
      }
    Qed.


    Lemma alpha_equiv'_impl_almost_same_evars {Σ : Signature} R R' nϕ1 nϕ2:
      alpha_equiv' R R' nϕ1 nϕ2 ->
      forall x1, x1 ∈ (named_free_evars nϕ1) ->
        exists x2, x2 ∈ (named_free_evars nϕ2) /\
          (x1, x2) ∈ pbr R.
    Proof.
      intros Halpha x1 Hx1.
      induction Halpha; simpl in *.
      {
        rewrite elem_of_singleton in Hx1.
        subst.
        exists y.
        rewrite elem_of_singleton.
        split;[reflexivity|assumption].
      }
      { exfalso. set_solver. }
      {
        rewrite elem_of_union in Hx1.
        destruct Hx1 as [Hx1|Hx1].
        {
          specialize (IHHalpha1 Hx1).
          destruct IHHalpha1 as [x2 [Hx21 Hx22]].
          exists x2.
          rewrite elem_of_union.
          naive_solver.
        }
        {
          specialize (IHHalpha2 Hx1).
          destruct IHHalpha2 as [x2 [Hx21 Hx22]].
          exists x2.
          rewrite elem_of_union.
          naive_solver.
        }
      }
      {
        rewrite elem_of_union in Hx1.
        destruct Hx1 as [Hx1|Hx1].
        {
          specialize (IHHalpha1 Hx1).
          destruct IHHalpha1 as [x2 [Hx21 Hx22]].
          exists x2.
          rewrite elem_of_union.
          naive_solver.
        }
        {
          specialize (IHHalpha2 Hx1).
          destruct IHHalpha2 as [x2 [Hx21 Hx22]].
          exists x2.
          rewrite elem_of_union.
          naive_solver.
        }
      }
      { exfalso. set_solver. }
      { exfalso. set_solver. }
      {
        destruct (decide (x1 = x)).
        {
          subst. clear -Hx1. exfalso. set_solver.
        }
        {
          feed specialize IHHalpha.
          {
            set_solver.
          }
          destruct IHHalpha as [x2 [Hx21 Hx22]].
          rewrite elem_of_union in Hx22.
          rewrite elem_of_filter in Hx22.
          unfold unrelated,related in Hx22.
          rewrite elem_of_singleton in Hx22.
          simpl in Hx22.
          destruct Hx22; try naive_solver.
          exists x2. set_solver.
        }
      }
      {
        specialize (IHHalpha Hx1).
        exact IHHalpha.
      }
    Qed.

    Lemma alpha_equiv'_impl_almost_same_svars {Σ : Signature} R R' nϕ1 nϕ2:
      alpha_equiv' R R' nϕ1 nϕ2 ->
      forall X1, X1 ∈ (named_free_svars nϕ1) ->
        exists X2, X2 ∈ (named_free_svars nϕ2) /\
          (X1, X2) ∈ pbr R'.
    Proof.
      intros Halpha X1 HX1.
      induction Halpha; simpl in *.
      { exfalso. set_solver. }
      {
        rewrite elem_of_singleton in HX1.
        subst.
        exists Y.
        rewrite elem_of_singleton.
        split;[reflexivity|assumption].
      }
      {
        rewrite elem_of_union in HX1.
        destruct HX1 as [HX1|HX1].
        {
          specialize (IHHalpha1 HX1).
          destruct IHHalpha1 as [X2 [HX21 HX22]].
          exists X2.
          rewrite elem_of_union.
          naive_solver.
        }
        {
          specialize (IHHalpha2 HX1).
          destruct IHHalpha2 as [X2 [HX21 HX22]].
          exists X2.
          rewrite elem_of_union.
          naive_solver.
        }
      }
      {
        rewrite elem_of_union in HX1.
        destruct HX1 as [HX1|HX1].
        {
          specialize (IHHalpha1 HX1).
          destruct IHHalpha1 as [X2 [HX21 HX22]].
          exists X2.
          rewrite elem_of_union.
          naive_solver.
        }
        {
          specialize (IHHalpha2 HX1).
          destruct IHHalpha2 as [X2 [HX21 HX22]].
          exists X2.
          rewrite elem_of_union.
          naive_solver.
        }
      }
      { exfalso. set_solver. }
      { exfalso. set_solver. }
      {
        specialize (IHHalpha HX1).
        exact IHHalpha.
      }
      {
        destruct (decide (X1 = X)).
        {
          subst. clear -HX1. exfalso. set_solver.
        }
        {
          feed specialize IHHalpha.
          {
            set_solver.
          }
          destruct IHHalpha as [X2 [HX21 HX22]].
          rewrite elem_of_union in HX22.
          rewrite elem_of_filter in HX22.
          unfold unrelated,related in HX22.
          rewrite elem_of_singleton in HX22.
          simpl in HX22.
          destruct HX22; try naive_solver.
          exists X2. set_solver.
        }
      }
    Qed.

    Lemma alpha_equiv_impl_same_evars {Σ : Signature} nϕ1 nϕ2:
      alpha_equiv nϕ1 nϕ2 ->
      (named_free_evars nϕ1) = (named_free_evars nϕ2).
    Proof.
      intros Halpha.
      unfold alpha_equiv in Halpha.
      pose proof (H1 := alpha_equiv'_impl_almost_same_evars _ _ nϕ1 nϕ2 Halpha).
      pose proof (H2 := alpha_equiv'_impl_almost_same_evars _ _ nϕ2 nϕ1 (proj1 (alpha_equiv_sym nϕ1 nϕ2) Halpha)).
      simpl in *. unfold twice in *.
      apply anti_symm with (S := @subseteq (gset (evar)) _).
      { apply _. }
      {
        rewrite elem_of_subseteq.
        intros x Hx.
        specialize (H1 _ Hx).
        destruct H1 as [x2 [Hx21 Hx22]].
        rewrite elem_of_map in Hx22.
        destruct Hx22 as [x0 [Hx01 Hx02]].
        inversion Hx01; clear Hx01; subst.
        assumption.
      }
      {
        rewrite elem_of_subseteq.
        intros x Hx.
        specialize (H2 _ Hx).
        destruct H2 as [x2 [Hx21 Hx22]].
        rewrite elem_of_map in Hx22.
        destruct Hx22 as [x0 [Hx01 Hx02]].
        inversion Hx01; clear Hx01; subst.
        assumption.
      }
    Qed.

    Lemma alpha_equiv_impl_same_svars {Σ : Signature} nϕ1 nϕ2:
      alpha_equiv nϕ1 nϕ2 ->
      (named_free_svars nϕ1) = (named_free_svars nϕ2).
    Proof.
      intros Halpha.
      unfold alpha_equiv in Halpha.
      pose proof (H1 := alpha_equiv'_impl_almost_same_svars _ _ nϕ1 nϕ2 Halpha).
      pose proof (H2 := alpha_equiv'_impl_almost_same_svars _ _ nϕ2 nϕ1 (proj1 (alpha_equiv_sym nϕ1 nϕ2) Halpha)).
      simpl in *. unfold twice in *.
      apply anti_symm with (S := @subseteq (gset (svar)) _).
      { apply _. }
      {
        rewrite elem_of_subseteq.
        intros x Hx.
        specialize (H1 _ Hx).
        destruct H1 as [x2 [Hx21 Hx22]].
        rewrite elem_of_map in Hx22.
        destruct Hx22 as [x0 [Hx01 Hx02]].
        inversion Hx01; clear Hx01; subst.
        assumption.
      }
      {
        rewrite elem_of_subseteq.
        intros x Hx.
        specialize (H2 _ Hx).
        destruct H2 as [x2 [Hx21 Hx22]].
        rewrite elem_of_map in Hx22.
        destruct Hx22 as [x0 [Hx01 Hx02]].
        inversion Hx01; clear Hx01; subst.
        assumption.
      }
    Qed.

    Lemma alpha_equiv_same_size {Σ : Signature}
      (nϕ1 nϕ2 : NamedPattern) R R'
      : alpha_equiv' R R' nϕ1 nϕ2 ->
        nsize' nϕ1 = nsize' nϕ2.
    Proof.
      intros H.
      induction H; simpl; lia.
    Qed.

    Lemma collapse_aux_nsize' {Σ : Signature}
      (state : CollapseState)
      (nϕ : NamedPattern)
      : nsize' (collapse_aux state nϕ).2 = nsize' nϕ.
    Proof.
      move: state.
      induction nϕ; intros state; simpl;
        unfold lookup_or_leaf,lookup_or_node,lookup_or,alpha_equiv;
        repeat case_match; subst; simpl; try lia;
      match goal with
      | [H' : list_find _ _ = Some _ |- _] =>
        rewrite list_find_Some in H';
        destruct_and!;
        match goal with
        | [ Ha: alpha_equiv' _ _ _ _ |- _] => apply alpha'_sym in Ha
        end;
        erewrite alpha_equiv_same_size;[|eassumption];reflexivity
      | _ => congruence
      end.
    Qed.

    Definition list_of_pairs_apply {A B : Type}
    {_eqdA : EqDecision A}
    {_eqdB : EqDecision B}
    (x : A) (s : list (prod A B))
     : list B
   := fmap snd (filter (fun p => p.1 = x) s).

   Definition list_of_pairs_compose {A B C : Type}
      {_eqdA : EqDecision A}
      {_eqdB : EqDecision B}
      {_eqdC : EqDecision C}
      (s1 : list (prod A B))
      (s2 : list (prod B C))
      : list (prod A C)
    := foldr (fun (p : prod A B) (g' : list (prod A C)) =>
        let a := p.1 in
        let b := p.2 in
        g' ++ (fmap (fun (c : C) => (a,c))  (list_of_pairs_apply b s2))
    ) [] s1.


    Lemma list_of_pairs_compose_correct {A B C : Type}
    {_eqdA : EqDecision A}
    {_eqdB : EqDecision B}
    {_eqdC : EqDecision C}
    (s1 : list (prod A B))
    (s2 : list (prod B C))
    : forall (a : A) (c : C),
      (a, c) ∈ (list_of_pairs_compose s1 s2)
      <-> exists (b : B), (a, b) ∈ s1 /\ (b, c) ∈ s2.
    Proof.
      intros a c.
      unfold list_of_pairs_compose.
      split; intros H'.
      {
        induction s1; simpl in *.
        {
          inversion H'.
        }
        {
          rewrite elem_of_app in H'.
          destruct H' as [H'|H'].
          {
            specialize (IHs1 H').
            destruct IHs1 as [b [Hb1 Hb2]].
            exists b.
            split.
            {
              right. exact Hb1.
            }
            {
              exact Hb2.
            }
          }
          {
            unfold fmap in H'.
            rewrite elem_of_list_fmap in H'.
            destruct H' as [y [Hy1 Hy2]].
            inversion Hy1; clear Hy1; subst.
            unfold list_of_pairs_apply in Hy2.
            unfold fmap in Hy2.
            rewrite elem_of_list_fmap in Hy2.
            destruct Hy2 as [[b c][Hc1 Hc2]].
            simpl in Hc1. subst y.
            unfold filter in Hc2.
            rewrite elem_of_list_filter in Hc2.
            destruct a0 as [a0 b0]. simpl in *.
            destruct Hc2 as [Hc2 Hc3].
            simpl in Hc2. subst b.
            exists b0.
            split.
            {
              left.
            }
            {
              exact Hc3.
            }
          }
        }
      }
      {
        move: a c H'.
        induction s1; intros a' c' H'; simpl.
        {
          destruct H' as [b [Hb1 Hb2]].
          inversion Hb1.  
        }
        {
          destruct H' as [b [Hb1 Hb2]].
          rewrite elem_of_app.
          destruct a as [a'' b'']. simpl in *.
          inversion Hb1; clear Hb1; subst.
          {
            specialize (IHs1 a'' c').
            destruct (decide ((a'',b'') ∈ s1)).
            {
              feed specialize IHs1.
              {
                exists b''. split; assumption.
              }
              left. apply IHs1.
            }
            {
              right.
              unfold fmap.
              rewrite elem_of_list_fmap.
              exists c'.
              split;[reflexivity|].
              unfold list_of_pairs_apply.
              unfold filter.
              rewrite elem_of_list_fmap.
              exists (b'', c').
              split;[reflexivity|].
              rewrite elem_of_list_filter.
              simpl.
              split;[reflexivity|assumption].
            }
          }
          {
            specialize (IHs1 a' c').
            feed specialize IHs1.
            {
              exists b.
              split; assumption.
            }
            left. apply IHs1.
          }
        }
      }
    Qed.

    Program Definition pb_compose {A : Type}
      {_eqd : EqDecision A }
      {_cnd : Countable A }
      (pb1 pb2 : PartialBijection A)
      : PartialBijection A
    := {|
      pbr := list_to_set (list_of_pairs_compose (elements (pbr pb1)) (elements (pbr pb2))) ;
    |}.
    Next Obligation.
      intros A _eqd _cnt pb1 pb2 x y1 y2 H1 H2.
      rewrite elem_of_list_to_set in H1.
      rewrite elem_of_list_to_set in H2.
      rewrite list_of_pairs_compose_correct in H1.
      rewrite list_of_pairs_compose_correct in H2.
      destruct H1 as [B1 [HB11 HB12]].
      destruct H2 as [B2 [HB21 HB22]].
      rewrite elem_of_elements in HB11.
      rewrite elem_of_elements in HB22.
      rewrite elem_of_elements in HB12.
      rewrite elem_of_elements in HB21.

      destruct pb1 as [pbA pbApf1 pbApf2], pb2 as [pbB pbBpf1 pbBpf2].
      simpl in *.
      pose proof (pbApf1 _ _ _ HB11 HB21).
      subst B2.
      pose proof (pbBpf1 _ _ _ HB22 HB12).
      subst y2.
      reflexivity.
    Qed.
    Next Obligation.
    intros A _eqd _cnt pb1 pb2 x y1 y2 H1 H2.
    rewrite elem_of_list_to_set in H1.
    rewrite elem_of_list_to_set in H2.
    rewrite list_of_pairs_compose_correct in H1.
    rewrite list_of_pairs_compose_correct in H2.
    destruct H1 as [B1 [HB11 HB12]].
    destruct H2 as [B2 [HB21 HB22]].
    rewrite elem_of_elements in HB11.
    rewrite elem_of_elements in HB22.
    rewrite elem_of_elements in HB12.
    rewrite elem_of_elements in HB21.

    destruct pb1 as [pbA pbApf1 pbApf2], pb2 as [pbB pbBpf1 pbBpf2].
    simpl in *.
    pose proof (pbBpf2 _ _ _ HB22 HB12).
    subst B2.
    pose proof (pbApf2 _ _ _ HB11 HB21).
    subst y1.
    reflexivity.
  Qed.
  
  Lemma compose_update {A : Type} {_eqd : EqDecision A} {_cnt : Countable A}
    (R1 R2 : PartialBijection A) (x y z : A) :
  pbr (pb_compose (pb_update R1 x y) (pb_update R2 y z))
  ⊆ pbr (pb_update (pb_compose R1 R2) x z).
  Proof.
    destruct R1, R2.
    simpl.
      rewrite elem_of_subseteq.
      intros [e1 e2] H.
      rewrite elem_of_list_to_set in H.
      rewrite list_of_pairs_compose_correct in H.
      destruct H as [e' [He'1 He'2]].
      rewrite elem_of_elements in He'1.
      rewrite elem_of_elements in He'2.
      rewrite elem_of_union in He'1.
      rewrite elem_of_union in He'2.
      rewrite elem_of_filter in He'1.
      rewrite elem_of_filter in He'2.
      rewrite elem_of_singleton in He'1.
      rewrite elem_of_singleton in He'2.
      rewrite elem_of_union.
      rewrite elem_of_filter.
      rewrite elem_of_singleton.
      rewrite elem_of_list_to_set.
      rewrite list_of_pairs_compose_correct.
      setoid_rewrite elem_of_elements.
      unfold unrelated, related in *.
      naive_solver.
  Qed.

  Lemma pb_update_mono {A : Type}
    {_eqd : EqDecision A }
    {_cnd : Countable A }
    (R1 R2 : PartialBijection A)
    (x y : A) :
    pbr R1 ⊆ pbr R2 ->
    pbr (pb_update R1 x y) ⊆ pbr (pb_update R2 x y).
  Proof.
    intros H.
    unfold pb_update. simpl.
    apply union_mono.
    {
      unfold filter.
      rewrite elem_of_subseteq.
      intros aa Haa.
      rewrite elem_of_filter in Haa.
      rewrite elem_of_filter.
      destruct Haa as [H1 H2].
      split;[assumption|].
      set_solver.
    }
    {
      apply reflexivity.
    }
  Qed.


  Lemma alpha'_mono {Σ : Signature}
    (R1 R2 : PartialBijection evar)
    (R'1 R'2 : PartialBijection svar)
    (t u : NamedPattern)
    : 
      pbr R1 ⊆ pbr R2 ->
      pbr R'1 ⊆ pbr R'2 ->
      alpha_equiv' R1 R'1 t u ->
      alpha_equiv' R2 R'2 t u.
  Proof.
    intros H1 H2 Ha.
    move: R2 R'2 H1 H2.
    induction Ha; intros R2 R'2 H1 H2; constructor; auto.
    {
      apply IHHa.
      {
        apply pb_update_mono.
        exact H1.
      }
      {
        apply H2.
      }
    }
    {
      apply IHHa.
      { apply H1. }
      {
        apply pb_update_mono.
        exact H2.
      }
    }
  Qed.


  Lemma compose_alpha' {Σ : Signature}
    (R1 R2 : PartialBijection evar)
    (R'1 R'2 : PartialBijection svar)
    (t u v : NamedPattern):
    alpha_equiv' R1 R'1 t u ->
    alpha_equiv' R2 R'2 u v ->
    alpha_equiv' (pb_compose R1 R2) (pb_compose R'1 R'2) t v.
  Proof.
    intros Htu Huv.
    move : R1 R2 R'1 R'2 t v Htu Huv.
    induction u; intros R1 R2 R'1 R'2 t v Htu Huv; inversion Htu; inversion Huv; clear Htu; clear Huv; subst;
      constructor.
    {
      unfold pb_compose. simpl.
      rewrite elem_of_list_to_set.
      rewrite list_of_pairs_compose_correct.
      exists x.
      do 2 rewrite elem_of_elements.
      split; assumption.
    }
    {
      unfold pb_compose. simpl.
      rewrite elem_of_list_to_set.
      rewrite list_of_pairs_compose_correct.
      exists X.
      do 2 rewrite elem_of_elements.
      split; assumption.
    }
    { naive_solver. }
    { naive_solver. }
    { naive_solver. }
    { naive_solver. }
    { 
      pose proof (H'' := IHu _ _ _ _ _ _ tEu tEu0).
      eapply alpha'_mono;[apply compose_update|idtac|].
      2: apply H''.
      apply reflexivity.
    }
    {
      eapply alpha'_mono;[|apply compose_update|idtac].
      2: apply IHu.
      3: apply tEu0.
      2: apply tEu.
      apply reflexivity.
    }
  Qed.

  Lemma diagonal_mono {A : Type}
  {_eqd : EqDecision A }
  {_cnd : Countable A }
  ( R1 R2 : gset A)
  : R1 ⊆ R2 -> pbr (diagonal R1) ⊆ pbr (diagonal R2).
  Proof.
    intros H.
    unfold diagonal. simpl.
    apply set_map_mono;[|assumption].
    unfold pointwise_relation.
    intros a. reflexivity.
  Qed.


    Lemma collapse_aux_alpha'
      {Σ : Signature}
      (state : CollapseState)
      (nϕ : NamedPattern)
      : alpha_equiv (collapse_aux state nϕ).2 nϕ.
    Proof.
      remember (nsize' nϕ) as sz.
      assert (Hsz: nsize' nϕ <= sz) by lia.
      clear Heqsz.

      move: nϕ Hsz state.
      induction sz; intros nϕ Hsz state; destruct nϕ;
        simpl in *; try lia; try apply lookup_or_leaf_alpha.
      {
        unfold lookup_or_node,lookup_or. simpl.
        repeat case_match.
        {
          subst. simpl.
          rewrite list_find_Some in H.
          destruct H as [H1 [H2 H3]].
          apply alpha_equiv_sym.
          apply H2.
        }
        {
          simpl.
          clear H.

          constructor; simpl; unfold alpha_equiv in *.
          {
            pose proof (IH1 := (IHsz nϕ1 ltac:(lia) state)).
            pose proof (IH2 := (IHsz nϕ2 ltac:(lia) state)).
            pose proof (H1e := alpha_equiv_impl_same_evars _ _ IH1).
            pose proof (H1s := alpha_equiv_impl_same_svars _ _ IH1).
    
            rewrite H1e H1s.

            eapply alpha'_mono;[idtac|idtac|apply IH1].
            {
              apply diagonal_mono.
              rewrite H1e. clear. set_solver.
            }
            {
              apply diagonal_mono.
              rewrite H1s. clear. set_solver.
            }
          }
          {
            erewrite alpha_equiv_impl_same_evars.
            2: apply IHsz; lia.
            erewrite alpha_equiv_impl_same_svars.
            2: apply IHsz; lia.
            
            eapply alpha'_mono.
            3: { eapply IHsz. lia. }
            { apply diagonal_mono. clear. set_solver. } 
            { apply diagonal_mono. clear. set_solver. } 
          }
        }
      }
      {
        unfold lookup_or_node,lookup_or. simpl.
        repeat case_match.
        {
          subst. simpl.
          rewrite list_find_Some in H.
          destruct H as [H1 [H2 H3]].
          apply alpha_equiv_sym.
          apply H2.
        }
        {
          simpl.
          clear H.

          constructor; simpl; unfold alpha_equiv in *.
          {
            pose proof (IH1 := (IHsz nϕ1 ltac:(lia) state)).
            pose proof (IH2 := (IHsz nϕ2 ltac:(lia) state)).
            pose proof (H1e := alpha_equiv_impl_same_evars _ _ IH1).
            pose proof (H1s := alpha_equiv_impl_same_svars _ _ IH1).
    
            rewrite H1e H1s.

            eapply alpha'_mono;[idtac|idtac|apply IH1].
            {
              apply diagonal_mono.
              rewrite H1e. clear. set_solver.
            }
            {
              apply diagonal_mono.
              rewrite H1s. clear. set_solver.
            }
          }
          {
            erewrite alpha_equiv_impl_same_evars.
            2: apply IHsz; lia.
            erewrite alpha_equiv_impl_same_svars.
            2: apply IHsz; lia.
            
            eapply alpha'_mono.
            3: { eapply IHsz. lia. }
            { apply diagonal_mono. clear. set_solver. } 
            { apply diagonal_mono. clear. set_solver. } 
          }
        }
      }
      {
        unfold lookup_or_node,lookup_or. simpl.
        repeat case_match; simpl.
        {
          rewrite list_find_Some in H.
          destruct H as [H1 [H2 H3]].
          apply alpha_equiv_sym.
          apply H2.
        }
        {
          clear H.
          constructor.
          eapply alpha'_mono.
          3: apply IHsz; lia.
          { 
            eapply transitivity.
            {
              eapply diagonal_mono.
              erewrite alpha_equiv_impl_same_evars.
              2: apply IHsz; lia.
              rewrite union_idemp_L.
              apply reflexivity.
            }
            simpl.
            rewrite elem_of_subseteq.
            intros [e1 e2] He1e2.
            rewrite elem_of_map in He1e2.
            destruct He1e2 as [x' [H1 H2]].
            unfold twice in H1. inversion H1. subst. clear H1.
            rewrite elem_of_union.
            rewrite elem_of_singleton.
            destruct (decide (x = x')).
            {
              subst. right. reflexivity.
            }
            {
              rewrite elem_of_filter.
              unfold unrelated,related.
              simpl.
              left.
              split;[naive_solver|].
              rewrite elem_of_map.
              exists x'.
              split;[reflexivity|].
              rewrite elem_of_union.
              left.
              rewrite elem_of_difference.
              rewrite elem_of_singleton.
              split;[|congruence].
              erewrite alpha_equiv_impl_same_evars.
              { exact H2. }
              apply IHsz.
              lia.
            }
          }
          {
            eapply transitivity.
            {
              eapply diagonal_mono.
              erewrite alpha_equiv_impl_same_svars.
              2: apply IHsz; lia.
              rewrite union_idemp_L.
              apply reflexivity.
            }
            simpl.
            rewrite elem_of_subseteq.
            intros [e1 e2] He1e2.
            rewrite elem_of_map in He1e2.
            destruct He1e2 as [x' [H1 H2]].
            unfold twice in H1. inversion H1. subst. clear H1.
            rewrite elem_of_map.
            exists x'.
            split;[reflexivity|].
            rewrite elem_of_union.
            right. assumption.
          }
        }
      }
      {
        unfold lookup_or_node,lookup_or. simpl.
        repeat case_match; simpl.
        {
          rewrite list_find_Some in H.
          destruct H as [H1 [H2 H3]].
          apply alpha_equiv_sym.
          apply H2.
        }
        {
          clear H.
          constructor.
          eapply alpha'_mono.
          3: apply IHsz; lia.
          { 
            eapply transitivity.
            {
              eapply diagonal_mono.
              erewrite alpha_equiv_impl_same_evars.
              2: apply IHsz; lia.
              rewrite union_idemp_L.
              apply reflexivity.
            }
            simpl.
            rewrite elem_of_subseteq.
            intros [e1 e2] He1e2.
            rewrite elem_of_map in He1e2.
            destruct He1e2 as [x' [H1 H2]].
            unfold twice in H1. inversion H1. subst. clear H1.

            rewrite elem_of_map.
            exists x'.
            split;[reflexivity|].
            rewrite elem_of_union.
            right. assumption.
          }
          {
            eapply transitivity.
            {
              eapply diagonal_mono.
              erewrite alpha_equiv_impl_same_svars.
              2: apply IHsz; lia.
              rewrite union_idemp_L.
              apply reflexivity.
            }
            simpl.
            rewrite elem_of_subseteq.
            intros [e1 e2] He1e2.
            rewrite elem_of_map in He1e2.
            destruct He1e2 as [X' [H1 H2]].
            unfold twice in H1. inversion H1. subst. clear H1.
            
            rewrite elem_of_union.
            rewrite elem_of_singleton.
            destruct (decide (X = X')).
            {
              subst. right. reflexivity.
            }
            {
              rewrite elem_of_filter.
              unfold unrelated,related.
              simpl.
              left.
              split;[naive_solver|].
              rewrite elem_of_map.
              exists X'.
              split;[reflexivity|].
              rewrite elem_of_union.
              left.
              rewrite elem_of_difference.
              rewrite elem_of_singleton.
              split;[|congruence].
              erewrite alpha_equiv_impl_same_svars.
              { exact H2. }
              apply IHsz.
              lia.
            }
          }
        }
      }
    Qed.

  (*
  (* TESTS *)
From MatchingLogic Require Import StringSignature.

Definition Σ : Signature :=
  {|
   |}
#[local]
Example ex_rename {Σ : Signature} :
  rename  = patt_bott.
*)