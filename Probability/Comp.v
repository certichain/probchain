From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat seq ssrfun eqtype bigop fintype choice.

Require Import Reals Fourier FunctionalExtensionality.
From infotheo
Require Import proba ssrR Reals_ext logb ssr_ext ssralg_ext bigop_ext Rbigop .

Require Import Nsatz.

Require Import Bvector.
Set Implicit Arguments.

(* Computation definition - from FCF*)
Section Comp.

(* 
    Inductive Comp (A : finType) :  Type :=
        | Ret : forall a : A, Comp A 
        | Bind : forall B, Comp B -> (B -> Comp A) -> Comp A
        | Repeat :  Comp A -> pred A -> Comp A
        | Rnd : forall n : nat, Comp A.
 *)


    Inductive Comp : finType -> Type :=
        | Ret : forall (A : finType) (a : A), Comp A 
        | Bind : forall (A B : finType), Comp B -> (B -> Comp A) -> Comp A
        | Repeat : forall (A : finType),  Comp A -> pred A -> Comp A
        | Rnd : forall (A : finType) (n : nat), Comp A.
    


    
    Fixpoint getSupport(A : finType) (c : Comp A) : list A :=
        match c with
            | Ret _ a => [:: a]
            | Bind _ _ c1 c2 => 
            (flatten 
                (map 
                    (fun b => (getSupport (c2 b)))
                    (getSupport c1)
                )
            )
            | Repeat _ c P => (filter P (getSupport c))
            | Rnd A n => (flatten (map (fun x => match pickle_inv A x with 
                                                        | Some value => [:: value]
                                                        | None => [::]
                                                        end) (index_iota 0 n)))
        end.


    Inductive well_formed_comp : forall (A : finType), Comp A -> Prop :=
        | well_formed_Ret :
            forall (A : finType) (a : A),
                well_formed_comp (Ret A a)
        | well_formed_Bind : forall (A B : finType) (c1 : Comp B) (c2 : B -> Comp A),
            well_formed_comp c1 ->
            (forall b, b \in (getSupport c1) -> well_formed_comp (c2 b)) ->
            well_formed_comp (Bind c1 c2)
        | well_formed_Rnd : forall (A : finType) n,
            well_formed_comp (Rnd A n)
        | well_formed_Repeat :
            forall (A : finType) (c : Comp A) P b,
                well_formed_comp c ->
                    b \in (filter P (getSupport c)) ->
                    well_formed_comp (Repeat c P).
                


    Fixpoint evalDist(A : finType) (c : Comp A) : dist A :=
        match c with
            Ret _ a => fun a' => if pickle a == pickle a' then 1 else 0 
        end
    .




End Comp.
