From Coq Require Import ssreflect ssrfun ssrbool.

From stdpp Require Import base list list_numbers propset.

From MatchingLogic Require Import Signature Semantics ModelIsomorphism.
From MatchingLogic.OPML Require Import OpmlSignature OpmlModel.

Record OpmlAmlSigRel
    {Σo : OPMLSignature} {Σa : Signature} := {

    oasr_sym : opml_symbol -> symbols ;
    oasr_sym_inj : Inj (=) (=) oasr_sym ;

    oasr_junk : symbols;
    oasr_junk_distinct :
        forall s, oasr_sym s <> oasr_junk ;

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

    oamr_junk :
        forall (ma : Domain Ma),
            ((ma ∈ (sym_interp Ma (oasr_junk oamr_sig)))
            <-> ~ exists (mo : om_unified_carrier Mo),
                ma = oamr_ele mo
            )
            ;    

}.

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


