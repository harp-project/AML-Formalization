Require Import AML_definition.
Require Import Coq.Sets.Ensembles.
Require Import Coq.Program.Basics.

Ltac proof_ext_val :=
simpl;intros;
repeat
  (* Normalize *)
   rewrite (Same_set_to_eq (Union_Empty_l _))
|| rewrite (Same_set_to_eq (Compl_Compl_Ensembles _ _))
|| rewrite
   (Same_set_to_eq (Compl_Union_Compl_Intes_Ensembles_alt _ _ _))
|| rewrite (Same_set_to_eq (FA_rel _ _ _))
  (* Apply *)
|| (eapply (proj1 Same_set_Compl) ; intros)
|| (eapply FA_Inters_same ; intros)
  (* Final step *)
|| exact Complement_Empty_is_Full
|| exact (Symdiff_val _ _)
|| exact (Same_set_refl _).

Check Build_Sigma_model.

Definition model := Build_Sigma_model
  string
  ""%string
  string_dec
  (fun (l r c: string) => (append l r) = c)
  (compose (Singleton _) id_si).

Definition pattern1 := sp_const (sigma_c "apple").

Lemma test1 : Same_set _ (Singleton _ "apple"%string)
(ext_valuation (sm:=model) id_ev (compose (Singleton _) id_sv) pattern1).
Proof.
proof_ext_val.
Qed.

Lemma test2 : In _
(ext_valuation (sm:=model) id_ev (compose (Singleton _) id_sv) pattern1)
"apple"%string.
Proof.
proof_ext_val.
eapply In_singleton.
Qed.

Definition var1 := (evar_c "tree").
Definition pattern2 :=
  sp_exists var1 (sp_app (sp_const (sigma_c "apple")) (sp_var var1)).

Lemma test3 : In _
(ext_valuation (sm:=model) id_ev (compose (Singleton _) id_sv) pattern2)
"appletree"%string.
Proof.
proof_ext_val.
unfold compose.
unfold id_si.
eapply FA_Uni_intro.
unfold pointwise_app. simpl.
eapply (ex_intro _ (id_ev var1)).
eapply (ex_intro _ "apple"%string).
eapply (ex_intro _ "tree"%string).
split. apply In_singleton.
split. unfold change_val. simpl. apply In_singleton.
reflexivity.
Qed.

Definition var2 := (evar_c "").
Definition pattern3 :=
  sp_exists var1 (sp_app (sp_const (sigma_c "apple")) (sp_var var2)).

Lemma test4 : In _
(ext_valuation (sm:=model) id_ev (compose (Singleton _) id_sv) pattern2)
"apple"%string.
Proof.
proof_ext_val.
unfold compose.
unfold id_si.
eapply FA_Uni_intro.
unfold pointwise_app. simpl.
eapply (ex_intro _ (id_ev var2)).
eapply (ex_intro _ "apple"%string).
eapply (ex_intro _ ""%string).
split. apply In_singleton.
split. unfold change_val. simpl. apply In_singleton.
reflexivity.
Qed.
