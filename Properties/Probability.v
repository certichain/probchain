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
Require Import ValidSchedule Deterministic Comp Notationv1 BlockChain Protocol OracleState BlockMap InvMisc Parameters FixedList FixedMap.

Set Implicit Arguments.

(* Todo(Kiran) Replace this with the actual constant*)
Variable probability_constant : R.


(* The chain quality lemma is defined, given that... *)
Definition chain_quality_givens (schedule : seq.seq RndGen) (l u : nat) (agent : 'I_n_max_actors) :=
    o_w' <-$ world_step initWorld schedule;
    (* the schedule produces a world *)
    (* this first if should always return true if the schedule has been validated *)
    v <- if o_w' is Some(w')  then
        let: (actor, is_corrupt) := (tnth (world_actors w') agent) in
        let: current_chain := honest_current_chain actor in
            (* the selected actor is honest *)
            (~~ is_corrupt) && 
            (* the length of the actor's chain is greater than l *)
            ((fixlist_length current_chain ) > l)%nat
         else false;
    ret v.

Definition p_chain_quality_givens  (schedule : seq.seq RndGen) (l u : nat) (agent : 'I_n_max_actors) :=
    evalDist (chain_quality_givens schedule l u agent) true.




Definition has_chain_quality_property (s: seq.seq RndGen) (l u : nat) (agent : 'I_n_max_actors) :=
    o_current_w <-$ world_step initWorld s;
    result <- if o_current_w is Some(current_w) then 
        (((fixlist_length (honest_current_chain (fst (tnth (world_actors current_w) agent)))) > l)%nat &&
    chain_quality_prop_agent current_w l u agent) else false;
    ret result.

Definition p_has_chain_quality_property (s : seq.seq RndGen) (l u : nat) (agent : 'I_n_max_actors) :=
    evalDist (has_chain_quality_property s l u agent) true.



(* Probability that the ratio of blocks of an honest player is bounded by t / n-t, given that 
    the schedule produces a value
    the selected actor is honest
    the selected actors chain is longer than l
*)
Lemma p_chain_quality (l u : nat) : forall  (s: seq.seq RndGen) (agent : 'I_n_max_actors),
   (* Forall *valid* schedules, *)
   (valid_schedule s) -> 
   (* if the schedule is capable of producing worlds satisfying the givens *)
    (p_chain_quality_givens s l u agent > R0) ->
    (* Pr( givens_of result_w AND has_chain_quality_property ) / Pr (givens_of result_w ) = *)
    (* Pr (result_w has chain_quality_property, given the givens) *)

    (p_has_chain_quality_property s l u agent) / (p_chain_quality_givens s l u agent) = probability_constant.
    Admitted.



Definition adopted_at_round (c : BlockChain) (r : 'I_N_rounds) (w: World) :=
    (length (filter (fun rec => 
        let: (chain, round, addr) := rec in
        (chain == c) && (round == r))
    (fixlist_unwrap (world_adoption_history w))) > 0)%nat.


Definition common_prefix_givens 
    (* Todo: Add typical execution assumption*)
    (schedule : seq.seq RndGen)  (r : 'I_N_rounds) (c1 c2: BlockChain)  :=
    (* Consider two chains c1 c2 st, len(C2) >= len (C1)*)
    (w' <-$ world_step initWorld schedule;
    r <-
        if w' is Some(current_w) then
        (* if c1 is adopted by an honest party at round r and c2 is adopted or diffused at round r*)
            [&& (adopted_at_round c1 r current_w) & (adopted_at_round c2 r current_w) ]
        else 
            false;
    ret r).

Definition p_common_prefix_givens
    (schedule : seq.seq RndGen)  (r : 'I_N_rounds)  (c1 c2: BlockChain)  :=
    evalDist (common_prefix_givens schedule  r c1 c2 ) true.


Definition has_common_prefix_property
    (* Todo: Add typical execution assumption*)
    (* Todo: Assert that k >= 2 eta k f *)
    (schedule : seq.seq RndGen) (k : nat) (r : 'I_N_rounds) (c1 c2: BlockChain)  :=
    (* Consider two chains c1 c2 st, len(C2) >= len (C1)*)
    (w' <-$ world_step initWorld schedule;
    r <-
        if w' is Some(current_w) then
        (* if c1 is adopted by an honest party at round r and c2 is adopted or diffused at round r*)
            [&& (adopted_at_round c1 r current_w), 
                (adopted_at_round c2 r current_w) ,
               (* then pruning k blocks from the head of c1 will make it a prefix or equal to c2 and visa versa *) 
               prefix (drop k (BlockChain_unwrap c1)) (BlockChain_unwrap c2) &
               prefix (drop k (BlockChain_unwrap c2)) (BlockChain_unwrap c1) ]
        else 
            false;
    ret r).

Definition p_has_common_prefix_property
    (schedule : seq.seq RndGen) (k : nat) (r : 'I_N_rounds)  (c1 c2: BlockChain)  :=
    evalDist (has_common_prefix_property schedule k r c1 c2 ) true.

Lemma common_prefix: forall 
    (s: seq.seq RndGen) (k : nat) (r : 'I_N_rounds) (c1 c2: BlockChain) ,

   (valid_schedule s) -> 

    ((length c2 >= length c1)%nat ) ->
     (p_common_prefix_givens s r c1 c2 > R0) ->
    (* Pr( givens_of result_w AND has_chain_quality_property ) / Pr (givens_of result_w ) = *)
    (* Pr (result_w has chain_quality_property, given the givens) *)

    (p_has_common_prefix_property s k r c1 c2 ) / (p_common_prefix_givens s r c1 c2 ) = probability_constant.
    Admitted.
    
    
(*
Definition common_prefix_property (current_w : World) (k r1 r2 : nat) (a1 a2 : 'I_n_max_actors) (c1 c2 : BlockChain) :=
  (* current w is valid *)
  (world_round_no current_w) >= r2 ->
  r1 <= r2 ->
  (a1 < n_max_actors) -> (a2 < n_max_actors) ->
  ~~ (actor_n_is_corrupt current_w a1) -> ~~ (actor_n_is_corrupt current_w a1) ->
  (* players a1 a2 adopting the chains at rounds r1, r2 *)
  (exists (w' wr1 : World), 
  (* reachable initWorld w' -> reachable w' wr1 -> reachable wr1 current_w ->   *)
    adopt_at_round w' wr1 c1 (widen_ord (leq_addr _ _) a1) r1) ->
  (exists (w'' wr2 : World), 
  (* reachable initWorld w'' -> reachable w'' wr2 -> reachable wr2 current_w ->   *)
    adopt_at_round w'' wr2 c2 (widen_ord (leq_addr _ _) a2) r2) ->
  (* then pruning k blocks from the head of c1 is a subsequence of c2*)
  prefix (drop k c1) c2.

 *)

 Definition unique_round_givens (schedule : seq.seq RndGen) (n : nat) (chain : BlockChain) :=
    o_w' <-$ world_step initWorld schedule;
    r <- if o_w' is Some(w) then
        (chain \in (fixlist_unwrap (world_chain_history w))) &&
        (fixlist_length chain > n)%nat &&
        (nth_block_is_honest chain n w) &&
        (nth_block_hashed_in_a_uniquely_successful_round w chain n)

    else false;
    ret r.

 Definition p_unique_round_givens (schedule : seq.seq RndGen) (n : nat) (chain : BlockChain) :=
    evalDist (unique_round_givens schedule n chain) true.

Definition is_unique_round (schedule : seq.seq RndGen) (n : nat) (chain : BlockChain) :=
    o_w' <-$ world_step initWorld schedule;
    r <- if o_w' is Some(w) then
        (chain \in (fixlist_unwrap (world_chain_history w))) &&
        (fixlist_length chain > n)%nat &&
        (nth_block_is_honest chain n w) &&
        (if (nth_block_hashed_in_a_uniquely_successful_round w chain n) is Some(value) then
            (all (fun other_chain => 
                    if other_chain \in (fixlist_unwrap (world_chain_history w)) then
                        if (fixlist_length other_chain > n)%nat then
                            ((nth_block_is_adversarial w other_chain n) ||
                            (nth_block_equals w other_chain n (nth_block w chain n)))
                        else true
                    else true
                ) (fixlist_unwrap (world_chain_history w)))
        else false)
    else false;
    ret r.

Definition p_is_unique_round (schedule : seq.seq RndGen) (n : nat) (chain : BlockChain) :=
    evalDist (is_unique_round schedule n chain) true.


Lemma unique_round : forall  (s: seq.seq RndGen) (n : nat) (chain : BlockChain),
   (* Forall schedules, *)
   (* if the schedule is capable of producing worlds satisfying the givens *)
   (valid_schedule s) -> 

    (p_unique_round_givens s n chain > R0) ->

    (* Pr( givens_of result_w AND has_chain_quality_property ) / Pr (givens_of result_w ) = *)
    (* Pr (result_w has chain_quality_property, given the givens) *)

    (p_is_unique_round s n chain) / (p_unique_round_givens s n chain) = probability_constant.
    Admitted.
