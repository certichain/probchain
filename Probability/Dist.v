
From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat seq ssrfun eqtype bigop.

From mathcomp.algebra
Require Import rat.

Set Implicit Arguments.

Definition Dist A := A -> rat.

Section definitions.
    (* A distribution on A maps values in A to a probability*)
    Variable A : eqType.
    Variable P : Dist A.
    Variable sample_space : seq A.

    Definition prob event := \big[addq/0%Q]_(i <- event) (P i).
    Notation "Pr[ x ]" := (prob x) .

    Hypothesis wf_sample_space : Pr[ sample_space ] = 1%Q.
    Hypothesis wf_probability :  forall x, x \in sample_space -> Pr[ [:: x] ] = 0%Q.


End definitions.
