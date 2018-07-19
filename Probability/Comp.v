From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat seq ssrfun eqtype bigop fintype choice.

From infotheo
Require Import proba.

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


End Comp.