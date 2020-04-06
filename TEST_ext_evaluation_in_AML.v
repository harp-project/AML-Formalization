Require Import AML_definition.
Require Import String.
Require Import Coq.Sets.Ensembles.
Require Import Coq.Program.Basics.
Require Import Ensembles_Ext.

Definition model := Build_Sigma_model
  string
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

Definition var1 := (evar_c "var1").
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
reflexivity.
Qed.

Lemma test4 : In _
(ext_valuation (sm:=model) id_ev (compose (Singleton _) id_sv) pattern2)
"apple"%string.
Proof.
proof_ext_val.
unfold compose.
unfold id_si.
eapply FA_Uni_intro.
unfold pointwise_app. simpl.
eapply (ex_intro _ (id_ev var1)).
eapply (ex_intro _ "apple"%string).
eapply (ex_intro _ ""%string).
reflexivity.
Qed.
