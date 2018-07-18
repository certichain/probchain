
From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat seq ssrfun eqtype bigop.

From mathcomp.algebra
Require Import rat.

Set Implicit Arguments.

(* A distribution on A maps values in A to a probability*)
Definition Dist A := A -> rat.

Section Probability.
    Variable A : Type.
    Variable P : Dist A.
    Variable sample_space : seq A.

    Definition prob_event_explicit event := \big[addq/0%Q]_(i <- event) (P i).
    Notation "Pr[ x ]" := (prob_event_explicit x) .

    Definition prob_event_implicit (p : pred A) :=
        \big[addq/0%Q]_(i <- sample_space | p i) (P i).

    Notation "Pr[ x | f ]" := (prob_event_implicit (fun x => f)).


End Probability.


Section Expectation.
    Variable P : Dist rat.
    Variable sample_space : seq rat.



    Definition expect_event_explicit event := \big[addq/0%Q]_(i <- event) (mulq i (P i)).
    Definition expect_event_implicit (p : pred rat) :=
        \big[addq/0%Q]_(i <- sample_space | p i) (mulq i (P i)).


    Notation "Pr[ x ]" := (prob_event_explicit P x) .
    Notation "Pr[ x | f ]" := (prob_event_implicit P sample_space (fun x => f)).

    Notation "E[ x ]" := (expect_event_explicit x).
    Notation "E[ x | f ]" := (expect_event_implicit (fun x => f)).


End Expectation.

Section Theorems.
    Variable P : Dist rat.
    Variable sample_space : seq rat.

    Notation "Pr[ x ]" := (prob_event_explicit P x) .
    Notation "Pr[ x | f ]" := (prob_event_implicit P sample_space (fun x => f)).
    Notation "E[ x ]" := (expect_event_explicit P x).
    Notation "E[ x | f ]" := (expect_event_implicit P sample_space (fun x => f)).

    Hypothesis wf_sample_space : Pr[ sample_space ] = 1%Q.
    Hypothesis wf_probability :  forall x, ~~ (x \in sample_space) -> Pr[ [:: x] ] = 0%Q.

End Theorems.
