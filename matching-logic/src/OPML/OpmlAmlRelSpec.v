From MatchingLogic Require Export ModelIsomorphism.
From MatchingLogic.OPML Require Export OpmlSignature OpmlModel.

Record OpmlAmlSigRel
    {Σo : OPMLSignature} {Σa : Signature} := {

    oasr_sym : opml_symbol -> symbols ;
    oasr_sym_inj : Inj (=) (=) oasr_sym ;

    oasr_no_junk : symbols;
    oasr_no_junk_distinct :
        forall s, oasr_sym s <> oasr_no_junk ;

}.

Record OpmlAmlModRel
    {Σo : OPMLSignature}
    {Σa : Signature}
    (Mo : OPMLModel)
    (Ma : Model)
:= {

    oamr_sig : OpmlAmlSigRel ;

    oamr_ele :
        om_unified_carrier Mo -> Domain Ma ;
    
    oamr_ele_inj : Inj (=) (=) oamr_ele ;

    (* The 'no_junk' symbol is interpreted as all the 'original' (OPML) model elements. *)
    oamr_no_junk :
        forall (ma : Domain Ma),
            ((ma ∈ (sym_interp Ma (oasr_no_junk oamr_sig)))
            <-> exists (mo : om_unified_carrier Mo),
                ma = oamr_ele mo
            )
            ; 
}.

Lemma oamr_no_junk_fmap
    {Σo : OPMLSignature}
    {Σa : Signature}
    (Mo : OPMLModel)
    (Ma : Model)
    (r : OpmlAmlModRel Mo Ma)
    :
    ((oamr_ele Mo Ma r) <$> (@propset_top (om_unified_carrier Mo))) ≡ (sym_interp Ma (oasr_no_junk (oamr_sig Mo Ma r)))
.
Proof.
    rewrite set_equiv.
    intros x.
    rewrite elem_of_fmap.
    rewrite oamr_no_junk.
    set_solver.
Qed.

Definition OpmlAmlModRel_preserves_isom
    {Σo : OPMLSignature}
    {Σa : Signature}
    (Mo : OPMLModel)
    (Ma : Model)
    (r : OpmlAmlModRel Mo Ma)
    :=
    forall Mo' Ma',
        OPMLModelIsomorphism Mo Mo' ->
        @ModelIsomorphism _ Ma Ma' ->
        OpmlAmlModRel Mo' Ma'
.


