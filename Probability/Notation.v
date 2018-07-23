Set Implicit Arguments.

From mathcomp.ssreflect
Require Import ssreflect ssrnat seq ssrbool ssrfun fintype choice.
From Probchain
Require Import Comp.

Notation "'ret' v" := (Ret _ v) (at level 75).

Notation "{ 0 , 1 } ^ n" := (Rnd _ (2^n))
    (right associativity, at level 77).

Notation "{ 0 , 1 }" := (Rnd _ _ 2) 
    (right associativity, at level 75).

Notation "x <-$ c1 ; c2" := (@Bind _ _ c1 (fun x => c2))
    (right associativity, at level 81, c1 at next level).

Notation "x <- e1 ; e2" := ((fun x => e2) e1)
    (right associativity, at level 81, e1 at next level).

Check 'I_3.

Section temp.
    Definition A := ordinal 3.
    Print Canonical Projections.
    Variable a : A.
    Locate "#| _ |".


    Lemma is_valid : 2 < #| A |.

    Definition example : Comp A := 
        x <- 3; 
        y <-$ {0,1};
        ret y.

About Rnd.

