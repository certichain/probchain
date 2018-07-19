From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat seq ssrfun eqtype bigop fintype.

From infotheo
Require Import proba.

Require Import Bvector.
Set Implicit Arguments.

(* Computation definition - from FCF*)
Section Comp.


    Inductive Comp (A : finType) :  Type :=
        | Ret : forall a : A, Comp A 
        | Bind : forall B, Comp B -> (B -> Comp A) -> Comp A
        | Repeat :  Comp A -> pred A -> Comp A
        | Rnd : forall n : nat, Comp A.



End Comp.