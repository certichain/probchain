From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat seq ssrfun eqtype bigop fintype choice.

From mathcomp.ssreflect
Require Import tuple.

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
    evalDist (is_valid_schedule schedule) true .

    Variable probability_constant : R.

Definition has_chain_quality_property (s: seq.seq RndGen) (l u : nat) (agent : 'I_n_max_actors) :=
    o_current_w <-$ world_step initWorld s;
    result <- if o_current_w is Some(current_w) then (((fixlist_length (honest_current_chain (fst (tnth (world_actors current_w) agent)))) > l)%nat &&
    chain_quality_prop_agent current_w l u agent) else false;
    ret result.

Definition p_has_chain_quality_property (s : seq.seq RndGen) (l u : nat) (agent : 'I_n_max_actors) :=
    evalDist (has_chain_quality_property s l u agent) true.



Lemma p_chain_quality (l u : nat) : forall  (s: seq.seq RndGen) (agent : 'I_n_max_actors),
   (* Forall schedules, *)
   (* if the schedule is capable of producing a world *)
    (p_valid_schedule s > R0) ->
    (* Pr( result_w is some AND has_chain_quality_property ) / Pr (result_w is some) = *)
    (* Pr (result_w has chain_quality_property, given that result_w is some) *)
    (* The probability of recieving a world with the chain quality property, given
    that world step is done with a valid sequence is equal to probability constant*)
    (p_has_chain_quality_property s l u agent) / (p_valid_schedule s) = probability_constant.
    Admitted.

