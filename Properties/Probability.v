From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat seq ssrfun eqtype bigop fintype choice.

Require Import Reals Fourier FunctionalExtensionality.
From infotheo
Require Import proba ssrR Reals_ext logb ssr_ext ssralg_ext bigop_ext Rbigop .

Require Import Nsatz.

Require Import Bvector.


From Probchain
Require Import Deterministic Comp Notationv1 BlockChain Protocol OracleState BlockMap InvMisc Parameters FixedList FixedMap.

Set Implicit Arguments.

Definition is_valid_schedule (schedule : seq.seq RndGen) :=
    w' <-$ world_step initWorld schedule;
    v <- isSome w';
    ret v.

(* Probability a given schedule is valid? *)
Definition p_valid_schedule  (schedule : seq.seq RndGen) :=
    evalDist (is_valid_schedule schedule) true  .

true.
Locate "Pr[ _ ]".
