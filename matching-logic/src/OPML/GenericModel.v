From Coq Require Import ssreflect ssrfun ssrbool.

From stdpp Require Import base list list_numbers propset.
(* This is unset by stdpp. We need to set it again.*)
Set Transparent Obligations.

From Equations Require Import Equations.
(* Set Equations Transparent. *)

Require Import Coq.Program.Equality. (* Dependent destruction *)
Require Import Coq.Logic.Classical_Prop. (* Proof irrelevance *)

From MatchingLogic.OPML Require Import
    OpmlSignature
    OpmlModel
.

Definition UnifiedCarrierInfo := Type.

Definition UnifiedCarrierFunctor : Type
    := Type -> UnifiedCarrierInfo
.

Definition UnifiedCarrierCtorFamily
    (UCF : UnifiedCarrierFunctor) (A : Type)
: Type
    := ((list nat)*(list A))%type -> (* Choose a particuar constructor from the family, and arguments of the constructor from the underlying type *)
       option (UCF A) (* maybe return something, and maybe not *)
.

Definition is_monotone (F : UnifiedCarrierFunctor)
    : Type
:= forall x y, (x -> y) -> (F x -> F x)
.

Record UnifiedCarrierComponent := {
    ucc_functor : UnifiedCarrierFunctor ;
    ucc_functor_monotone : is_monotone ucc_functor ;
    ucc_ctor_family : forall A, UnifiedCarrierCtorFamily ucc_functor A ;
    ucc_ctor_family_inj : forall A args1 args2 ret,
        (ucc_ctor_family A args1 = Some ret) ->
        (ucc_ctor_family A args2 = Some ret) ->
        args1 = args2 ;
}.

(* We can bypass the check because of the `is_monotone` requirement. *)
#[bypass_check(positivity=yes)]
Inductive UnifiedCarrier
    (F: UnifiedCarrierFunctor)
    (pos : is_monotone F)
: Type :=
| c (st : F (UnifiedCarrier F pos))
.

Definition CompInvertorT
    (UCC : UnifiedCarrierComponent)
: Type
    := forall (A : Type) (x : ucc_functor UCC A),
        option ({ nla : ((list nat)*(list A))%type | ucc_ctor_family UCC A nla = Some x })
.

Record Component := {
    comp_UCC
        : UnifiedCarrierComponent ;

    comp_invertor
        : CompInvertorT comp_UCC ;

    comp_invertor_complete
        : forall
            (A : Type)
            (nla : ((list nat)*(list A))%type)
            (x : ucc_functor comp_UCC A),
            ucc_ctor_family comp_UCC A nla = Some x ->
            exists pf,
                comp_invertor A x = Some (exist _ nla pf)
        ;
}.


Section constant.
    Context
        (UCI : UnifiedCarrierInfo)
    .

    Definition constant_UnifiedCarrierFunctor : UnifiedCarrierFunctor
        := fun _ => UCI
    .

    Lemma constant_UnifiedCarrierFunctor_monotone : is_monotone constant_UnifiedCarrierFunctor.
    Proof.
        unfold is_monotone,constant_UnifiedCarrierFunctor,UnifiedCarrierInfo in *.
        intros T1 T2 f x.
        exact x.
    Qed.

    (* TODO *)
    Definition constant_inversion
        {A : Type}
        (x : constant_UnifiedCarrierFunctor A)
    := 0.


End constant.

Program Definition bool_UCC : UnifiedCarrierComponent := {|
    ucc_functor
        := constant_UnifiedCarrierFunctor bool ;

    ucc_functor_monotone
        := constant_UnifiedCarrierFunctor_monotone bool ;

    ucc_ctor_family
        := fun A nla =>
        match nla with
        | ([0], []) => Some true
        | ([1], []) => Some false
        | _ => None
        end
        ;
|}.
Next Obligation.
    (* Injectivity *)
    (repeat case_match); simplify_eq/=; reflexivity.
Qed.

Program Definition bool_component : Component := {|
    comp_UCC :=  bool_UCC ;
    comp_invertor := fun A x =>
        match x return option ({ nla : ((list nat)*(list A))%type | ucc_ctor_family bool_UCC A nla = Some x }) with 
        | true => Some (exist (fun y => ucc_ctor_family bool_UCC A y = Some true) ([0],([]):(list A)) erefl)
        | false => Some (exist _ ([1],([]):(list A)) erefl)
        end
        ;
|}.
Next Obligation.
    destruct l.
    { inversion H. }
    destruct n,l,l0; inversion H; subst; clear H.
    {
        exists erefl.
        reflexivity.
    }
    destruct n; (simplify_eq /=).
    {
        exists erefl.
        reflexivity.
    }
    destruct n; (simplify_eq /=).
    destruct n; (simplify_eq /=).
    destruct n; (simplify_eq /=).
Qed.
Fail Next Obligation.

Program Definition empty_component : Component := {|
    comp_UCC := {|
        ucc_functor
            := constant_UnifiedCarrierFunctor Empty_set ;

        ucc_functor_monotone
            := constant_UnifiedCarrierFunctor_monotone Empty_set ;
        
        ucc_ctor_family
            := fun A nla => None ;
    |};

    comp_invertor :=
        fun A x => match x with end
        ;
    
    comp_invertor_complete
        := _;
|}.
Fail Next Obligation.

Section paircomb_ucf.
    Context
        (F1 F2 : UnifiedCarrierComponent)
    .

    Definition paircomb_ucf_UnifiedCarrierFunctor : UnifiedCarrierFunctor
    :=
        fun A => ((ucc_functor F1 A)+(ucc_functor F2 A))%type
    .

    Lemma paircomb_ucf_UnifiedCarrierFunctor_monotone : is_monotone paircomb_ucf_UnifiedCarrierFunctor.
    Proof.
        assert (M1 := ucc_functor_monotone F1).
        assert (M2 := ucc_functor_monotone F2).
        unfold is_monotone, paircomb_ucf_UnifiedCarrierFunctor in *.
        intros T1 T2 f.
        specialize (M1 T1 T2 f).
        specialize (M2 T1 T2 f).
        intros H.
        destruct H as [H|H].
        {
            specialize (M1 H).
            left. exact M1.
        }
        {
            specialize (M2 H).
            right. exact M2.
        }
    Qed.

End paircomb_ucf.

Section paircomb.
    Context
        (C1 C2 : Component)
    .

    Program Definition paircomb : Component := {|
        comp_UCC := {|
            ucc_functor :=
                paircomb_ucf_UnifiedCarrierFunctor
                    (comp_UCC C1)
                    (comp_UCC C2)
                ;
            
            ucc_functor_monotone :=
                paircomb_ucf_UnifiedCarrierFunctor_monotone
                    (comp_UCC C1)
                    (comp_UCC C2)
                ;
            
            ucc_ctor_family :=
                fun A nla =>
                match nla with
                | (0::ns, la) => @fmap option _ _ _ inl (@ucc_ctor_family (comp_UCC C1) A (ns,la))
                | (1::ns, la) => @fmap option _ _ _ inr (@ucc_ctor_family (comp_UCC C2) A (ns,la))
                | _ => None
                end
                ;

        |};

        comp_invertor := fun A x =>
            match x with 
            | inl y =>
                let inv := (@comp_invertor C1 A y) in
                @fmap option _ _ _ (fun tmp => exist _ (0::((proj1_sig tmp).1), (proj1_sig tmp).2) _) inv
            | inr y => @fmap option _ _ _ (fun tmp => exist _ (1::((proj1_sig tmp).1), (proj1_sig tmp).2) _) (@comp_invertor C2 A y)
            end
            ;
    |}.
    Next Obligation.
        (* Injectivity *)
        (repeat case_match); simplify_eq/=; try reflexivity.
        {
            rewrite fmap_Some in H.
            rewrite fmap_Some in H0.
            destruct H as [a [Ha1 Ha2]].
            destruct H0 as [b [Hb1 Hb2]].
            rewrite Ha2 in Hb2. inversion Hb2; subst; clear Hb2.
            pose proof (ucc_ctor_family_inj (comp_UCC C1) A (l4,l2) (l3, l0) b Ha1 Hb1).
            simplify_eq/=. reflexivity.
        }
        {
            rewrite fmap_Some in H.
            rewrite fmap_Some in H0.
            destruct H as [a [Ha1 Ha2]].
            destruct H0 as [b [Hb1 Hb2]].
            rewrite Ha2 in Hb2. inversion Hb2; subst; clear Hb2.
        }
        {
            rewrite fmap_Some in H.
            rewrite fmap_Some in H0.
            destruct H as [a [Ha1 Ha2]].
            destruct H0 as [b [Hb1 Hb2]].
            rewrite Ha2 in Hb2. inversion Hb2; subst; clear Hb2.
        }
        {
            rewrite fmap_Some in H.
            rewrite fmap_Some in H0.
            destruct H as [a [Ha1 Ha2]].
            destruct H0 as [b [Hb1 Hb2]].
            rewrite Ha2 in Hb2. inversion Hb2; subst; clear Hb2.
            pose proof (ucc_ctor_family_inj (comp_UCC C2) A (l4,l2) (l3, l0) b Ha1 Hb1).
            simplify_eq/=. reflexivity.
        }
    Qed.
    Next Obligation.
        rewrite H. reflexivity.
    Defined.
    Next Obligation.
        rewrite H. reflexivity.
    Defined.
    Next Obligation.
        unfold paircomb_ucf_UnifiedCarrierFunctor in *.
        destruct x.
        {
            destruct l.
            { inversion H. }
            destruct n.
            {
                exists H.
                unfold fmap,option_fmap,option_map.
                destruct (comp_invertor C1 A u) eqn:Heq.
                {
                    destruct s. simpl.
                    destruct x. simpl in *.
                    pose proof ( H' := H).
                    rewrite fmap_Some in H'.
                    destruct H' as [y [Hy1 Hy2]].
                    inversion Hy2; subst; clear Hy2.
                    pose proof (Htmp := ucc_ctor_family_inj (comp_UCC C1) A (l1,l2) (l, l0) y e Hy1).
                    simplify_eq/=.
                    f_equal.
                    
                    lazymatch goal with
                    | [|- (_ ↾ ?pf1) = ( _ ↾ ?pf2)] => assert (Hpi: pf1 = pf2) by (apply proof_irrelevance)
                    end.
                    rewrite Hpi.
                    reflexivity.
                }
                {
                    exfalso.
                    rewrite fmap_Some in H.
                    destruct H as [y [Hy1 Hy2]].
                    inversion Hy2; subst; clear Hy2.
                    apply (comp_invertor_complete C1 A (l,l0)) in Hy1.
                    destruct Hy1 as [pf Hpf].
                    simplify_eq/=.
                }
            }
            {
                exists H.
                destruct n.
                {
                    pose proof (H' := H).
                    rewrite fmap_Some in H'.
                    destruct H' as [x [H1x H2x]].
                    inversion H2x.
                }
                {
                    inversion H.
                }
            }
        }
        {
            destruct l.
            { inversion H. }
            destruct n.
            {
                exists H.
                unfold fmap,option_fmap,option_map.
                destruct (comp_invertor C2 A u) eqn:Heq.
                {
                    destruct s. simpl.
                    destruct x. simpl in *.
                    pose proof ( H' := H).
                    rewrite fmap_Some in H'.
                    destruct H' as [y [Hy1 Hy2]].
                    inversion Hy2.
                }
                {
                    exfalso.
                    rewrite fmap_Some in H.
                    destruct H as [y [Hy1 Hy2]].
                    inversion Hy2; subst; clear Hy2.
                }
            }
            {
                exists H.
                destruct n.
                {
                    pose proof (H' := H).
                    rewrite fmap_Some in H'.
                    destruct H' as [x [H1x H2x]].
                    simplify_eq/=.
                    simpl.
                    unfold fmap,option_fmap,option_map.
                    case_match.
                    {
                        destruct s as [y pfy].
                        simpl.
                        pose proof (Htmp := ucc_ctor_family_inj (comp_UCC C2) A (l, l0) y x H1x pfy).
                        subst y. simpl.
                        lazymatch goal with
                        | [|- Some (_ ↾ ?pf1) = Some ( _ ↾ ?pf2)] => assert (Hpi: pf1 = pf2) by (apply proof_irrelevance)
                        end.
                        rewrite Hpi.
                        reflexivity.
                    }
                    {
                        exfalso.
                        pose proof (H' := H).
                        rewrite fmap_Some in H'.
                        destruct H' as [y [H1y H2y]].
                        inversion H2y; subst; clear H2y.
                        apply (comp_invertor_complete C2 A (l,l0)) in H1x.
                        destruct H1x as [pf Hpf].
                        simplify_eq/=.
                    }
                }
                {
                    inversion H.
                }
            }
        }
    Qed.

End paircomb.

Section combine.
    Context
        (l : list Component)
    .

    Definition combine : Component := foldr paircomb empty_component l.

End combine.


Section with_signature.
    Context
        {Σ : OPMLSignature}
        (UCI : UnifiedCarrierInfo)
        (UCF : UnifiedCarrierFunctor)
        (pos : is_monotone UCF)
    .

    Definition CarrierFunctor : Type :=
        forall (s : opml_sort),
            propset UCI
    .

    (*
    Context
        (CF : CarrierFunctor)
        (cfi : CarrierFunctorInvertor)
    .

    
    Definition lift_cf : propset (UnifiedCarrier UCF pos)
    := PropSet (fun (e : UnifiedCarrier UCF pos) =>
        match e with
        | c _ _ x =>
            match (cfi x) with
            | None => False
            | Some ((A:Type),(y:A),pf) =>
                (* Need to know that `x` came from UCF *)
                True
            end
        end
    ).

    *)
End with_signature.
(*
(*
Definition ModelInfo : Type :=
    ()%type
.
*)
Record ModelInfo := {

}.

Definition ModelFunctor : Type -> Type :=
    fun (CarrierBase : Type) =>
    (Type*(ModelInfo))%type
.

Definition proj_carrier (MF : ModelFunctor) : CarrierFunctor
:=
    fun A => (MF A).1
.
*)

