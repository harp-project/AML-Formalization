From MatchingLogic.Utils Require Export Surj.
From MatchingLogic.OPML Require Export OpmlSignature.
From stdpp Require Export propset.

Polymorphic Cumulative
Record OPMLModel {Σ : OPMLSignature} := {
    om_unified_carrier :
        Type ;

    om_carrier :
        opml_sort -> propset om_unified_carrier ;

    om_carrier_no_junk :
        forall (m : om_unified_carrier),
            exists (s : opml_sort),
                m ∈ om_carrier s ;

    om_subsort_1 :
        forall
            (from to : opml_sort)
            (subsort : opml_subsort from to),
            om_carrier from ⊆ om_carrier to ;
            
    (* not sure if the following is needed: *)
    (*
    om_subsort_2 :
        forall
            (from to : opml_sort)
            (not_subsort : not (opml_subsort from to)),
            om_carrier from ## om_carrier to ;
    *)
    
    om_app :
        opml_symbol ->
        list om_unified_carrier ->
        propset om_unified_carrier ;
    
    om_app_wellsorted :
        forall
            (sym : opml_symbol)
            (args : list om_unified_carrier)
            (args_ws : forall i arg sort,
                args !! i = Some arg ->
                (opml_arg_sorts sym) !! i = Some sort ->
                arg ∈ om_carrier sort
            ),
            (om_app sym args) ⊆ (om_carrier (opml_ret_sort sym)) ;
}.

Record OPMLModelIsomorphism {Σ : OPMLSignature} (M1 M2 : OPMLModel) := {
    omi_f : (om_unified_carrier M1) -> (om_unified_carrier M2) ;
    omi_inj :: Inj (=) (=) omi_f ;
    omi_surj :: Surj' (=) omi_f ;
    omi_app :
        ∀ (s : opml_symbol) (args : list (om_unified_carrier M1)),
        omi_f <$> (@om_app Σ M1 s args) ≡ @om_app Σ M2 s (omi_f <$> args) ;
}.
