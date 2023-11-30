From Coq Require Import ssreflect ssrfun ssrbool.

From stdpp Require Import base list list_numbers propset.
(* This is unset by stdpp. We need to set it again.*)
Set Transparent Obligations.

From Equations Require Import Equations.
(* Set Equations Transparent. *)

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
    := (nat*(list A))%type -> (* Choose a particuar constructor from the family, and arguments of the constructor from the underlying type *)
       option (UCF A) (* maybe return something, and maybe not *)
.

Definition is_monotone (F : UnifiedCarrierFunctor)
    : Type
:= forall x, (x -> F x)
.

Record UnifiedCarrierComponent := {
    ucc_functor : UnifiedCarrierFunctor ;
    ucc_functor_monotone : is_monotone ucc_functor ;
    ucc_ctor_family : forall A, UnifiedCarrierCtorFamily ucc_functor A ;
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
        option ({ nla : (nat*(list A))%type | ucc_ctor_family UCC A nla = Some x })
.

Record Component := {
    comp_UCC
        : UnifiedCarrierComponent ;

    comp_invertor
        : CompInvertorT comp_UCC ;

    comp_invertor_complete
        : forall
            (A : Type)
            (nla : (nat*(list A))%type)
            (x : ucc_functor comp_UCC A),
            ucc_ctor_family comp_UCC A nla = Some x ->
            exists pf,
                comp_invertor A x = Some (exist _ nla pf)
        ;
}.


Section constant.
    Context
        (UCI : UnifiedCarrierInfo)
        (inh_UCI : Inhabited UCI)
    .

    Definition constant_UnifiedCarrierFunctor : UnifiedCarrierFunctor
        := fun _ => UCI
    .

    Lemma constant_UnifiedCarrierFunctor_monotone : is_monotone constant_UnifiedCarrierFunctor.
    Proof.
        unfold is_monotone,constant_UnifiedCarrierFunctor,UnifiedCarrierInfo in *.
        intros T x.
        destruct inh_UCI as [inhabitant].
        exact inhabitant.
    Qed.

    (* TODO *)
    Definition constant_inversion
        {A : Type}
        (x : constant_UnifiedCarrierFunctor A)
    := 0.


End constant.

Definition bool_UCC : UnifiedCarrierComponent := {|
    ucc_functor
        := constant_UnifiedCarrierFunctor bool ;

    ucc_functor_monotone
        := constant_UnifiedCarrierFunctor_monotone bool _ ;

    ucc_ctor_family
        := fun A nla =>
        match nla with
        | (0, []) => Some true
        | (1, []) => Some false
        | _ => None
        end
        ;
|}.

Program Definition bool_component : Component := {|
    comp_UCC :=  bool_UCC ;
    comp_invertor := fun A x =>
        match x return option ({ nla : (nat*(list A))%type | ucc_ctor_family bool_UCC A nla = Some x }) with 
        | true => Some (exist (fun y => ucc_ctor_family bool_UCC A y = Some true) (0,([]):(list A)) erefl)
        | false => Some (exist _ (1,([]):(list A)) erefl)
        end
        ;
|}.
Next Obligation.
    destruct n,l.
    {
        inversion H; subst; clear H.
        exists erefl.
        reflexivity.
    }
    { inversion H. }
    {
        destruct n; inversion H; subst.
        {
            exists erefl.
            reflexivity.
        }
    }
    {
        destruct n; inversion H.
    }
Qed.
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
        intros T x.
        specialize (M1 T x).
        specialize (M2 T x).
        (* This is highly suspicious. Our definition of monotonicity is probably wrong. *)
        left. assumption.
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
        |};

    |}.
    Next Obligation. Admitted.
    Next Obligation. Admitted.
    Next Obligation. Admitted.
    Next Obligation. Admitted.

End paircomb.

Section combine_ucf.
    Context
        (l : list (UnifiedCarrierFunctor))
        (pf : forall (F : UnifiedCarrierFunctor), F ∈ l -> is_monotone F)
    .

    Definition combine_ucf : UnifiedCarrierFunctor
    := fun A =>
            let l' := (fun F => F A) <$> l in
        foldr sum Empty_set l'
    .

End combine_ucf.

Section combine.

    Context
        (l : list Component)
    .

    (*
    Definition combine : Component := {|
        comp_UCC := 
    |}.
    *)

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

