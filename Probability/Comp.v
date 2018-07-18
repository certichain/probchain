From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat seq ssrfun eqtype bigop.

Require Import Bvector.
Set Implicit Arguments.

(* Computation definition - from FCF*)
Section Comp.

    Inductive Comp : eqType -> Type :=
        | Ret : forall A : eqType, A -> Comp A
        | Bind : forall A B, Comp A -> (A -> Comp B) -> Comp B
        | Repeat : forall A, Comp A -> pred A -> Comp A
        | Rnd : forall n, Comp n.



End Comp.