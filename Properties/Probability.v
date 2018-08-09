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


Definition schedule_produces_none (s: seq.seq RndGen) :=
    o_w' <-$ world_step initWorld s;
    r <- if o_w' is Some(w) then false else true;
    ret r.
Definition p_schedule_produces_none (s:seq.seq RndGen) :=
    evalDist (schedule_produces_none s) true.

Lemma valid_schedules_can_not_fail : forall (s: seq.seq RndGen),
    (valid_schedule s) ->
    p_schedule_produces_none s = R0.
    (* Todo: Complete this proof. *)
Admitted.








(*
- - - - - - - - - - - - - - - - - - - - 
          Chain Quality Lemma
- - - - - - - - - - - - - - - - - - - - 
*)

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
    chain_quality_property current_w l u agent) else false;
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









(*
- - - - - - - - - - - - - - - - - - - - 
          Common Prefix Lemma
- - - - - - - - - - - - - - - - - - - - 
*)

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
    (INR k >= (INR 2) * f_probability_honest_success * Eta_block_to_round * (INR Hash_length_k ) + (INR (2 * delta))) ->

   (valid_schedule s) -> 

    ((length c2 >= length c1)%nat ) ->
     (p_common_prefix_givens s r c1 c2 > R0) ->
    (* Pr( givens_of result_w AND has_chain_quality_property ) / Pr (givens_of result_w ) = *)
    (* Pr (result_w has chain_quality_property, given the givens) *)

    (p_has_common_prefix_property s k r c1 c2 ) / (p_common_prefix_givens s r c1 c2 ) = probability_constant.
    Admitted.
    





(*
- - - - - - - - - - - - - - - - - - - - 
          Unique Round Lemma
- - - - - - - - - - - - - - - - - - - - 
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
        [&& 
        
        (chain \in (fixlist_unwrap (world_chain_history w))),

        (fixlist_length chain > n)%nat,

        (nth_block_is_honest chain n w) &

        (if (nth_block_hashed_in_a_uniquely_successful_round w chain n) is Some(value) then
            (all (fun other_chain => 
                    if other_chain \in (fixlist_unwrap (world_chain_history w)) then
                        if (fixlist_length other_chain > n)%nat then
                            ((nth_block_is_adversarial w other_chain n) ||
                            (nth_block_equals w other_chain n (nth_block w chain n)))
                        else true
                    else true
                ) (fixlist_unwrap (world_chain_history w)))
        else false)]
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


Definition chain_growth_givens (schedule : seq.seq RndGen) (r l : nat)  :=
    o_w' <-$ world_step initWorld schedule;
    r <- if o_w' is some(w) then
        (* suppose that at round r, an honest party has a chain of length r*)
        (has 
            (* there is an actor, with index actor index*)
            (fun actor_ind => 
                (* such that, *)
                [&&
                (* the actor is honest *)
                (actor_n_is_honest w actor_ind) &
                (* and *)
                (has
                    (* there is a record *)
                    (fun pr => 
                        let: (rec_chain, rec_round, rec_actr)  := pr in 
                       [&&
                         (* adopting a chain of length l *)
                        ((fixlist_length rec_chain)  == l),
                         (* at round r *)
                        (nat_of_ord rec_round == r) &
                        (* by the actor *) 
                        (nat_of_ord rec_actr == actor_ind) ]
                    
                    )
                (fixlist_unwrap (world_adoption_history w)))]
            ) 
            (iota 0 n_max_actors))
         else
         false;
    ret r.
Definition p_chain_growth_givens (schedule : seq.seq RndGen) (r l : nat)  :=
    evalDist (chain_growth_givens schedule r l) true.


Definition chain_growth_property (w : World) (r l s : nat) :=
        (* suppose that at round r, an honest party has a chain of length r*)
        [&& 
            (has 
                (* there is an actor, with index actor index*)
                (fun actor_ind => 
                    (* such that, *)
                    [&&
                    (* the actor is honest *)
                    (actor_n_is_honest w actor_ind) &
                    (* and *)
                    (has
                        (* there is a record *)
                        (fun pr => 
                            let: (rec_chain, rec_round, rec_actr)  := pr in 
                        [&&
                            (* adopting a chain of length l *)
                            ((fixlist_length rec_chain)  == l),
                            (* at round r *)
                            (nat_of_ord rec_round == r) &
                            (* by the actor *) 
                            (nat_of_ord rec_actr == actor_ind) ]
                        
                        )
                    (fixlist_unwrap (world_adoption_history w)))]
                ) 
                (iota 0 n_max_actors)) &
                (* then every honest party has adopted a chain of length
                at least l + sum r to s - delta X'i*)
                let sum_of_delta_rounds := no_bounded_successful_rounds w r (s - delta) in
                (* forall actors *)
                    (* for all rounds from s onwards *)
                        (* every chain adoption*)
                  all_chains_after_round_have_length_ge w s (l + sum_of_delta_rounds )
                                ].


Definition has_chain_growth_property (schedule : seq.seq RndGen) (r l : nat) (s : nat) :=
    o_w' <-$ world_step initWorld schedule;
    r <- if o_w' is some(w) then
            chain_growth_property w r l s
         else false;
    ret r.


Definition p_has_chain_growth_property (schedule : seq.seq RndGen) (r l s : nat)  :=
    evalDist (has_chain_growth_property schedule r l s) true.


Lemma chain_growth: forall (schedule : seq.seq RndGen) (r l s : nat),
    (valid_schedule schedule) ->
    (s >= r + delta - 1)%nat ->

    (p_chain_growth_givens schedule r l > R0) ->

    (p_has_chain_growth_property schedule r l s) / (p_chain_growth_givens schedule r l) = probability_constant.
    Admitted.

Definition comp_no_adversarial_blocks (schedule : seq.seq RndGen) (from to : nat) :=
    o_w' <-$ world_step initWorld schedule;
    r <- if o_w' is some(w) then
            no_adversarial_blocks w from to
        else
            (Ordinal valid_N_rounds_mul_n_max_actors);
    ret r.    

Definition expected_no_adversarial_blocks (schedule : seq.seq RndGen) (from to : nat) :=
    expected_value (comp_no_adversarial_blocks schedule from to).

Definition comp_no_successful_rounds (schedule : seq.seq RndGen) (from to : nat) :=
    o_w' <-$ world_step initWorld schedule;
    r <- if o_w' is some(w) then
            no_successful_rounds w from to
        else
            (Ordinal valid_N_rounds);
    ret r.    


Definition expected_no_successful_rounds (schedule : seq.seq RndGen) (from to : nat) :=
    expected_value (comp_no_successful_rounds schedule from to).

Definition comp_no_bounded_successful_rounds (schedule : seq.seq RndGen) (from to : nat) :=
    o_w' <-$ world_step initWorld schedule;
    r <- if o_w' is some(w) then
            no_bounded_successful_rounds w from to
        else
            (Ordinal valid_N_rounds);
    ret r.    

Definition expected_no_bounded_successful_rounds (schedule : seq.seq RndGen) (from to : nat) :=
    expected_value (comp_no_bounded_successful_rounds schedule from to).

Definition comp_no_bounded_uniquely_successful_rounds (schedule : seq.seq RndGen) (from to : nat) :=
    o_w' <-$ world_step initWorld schedule;
    r <- if o_w' is some(w) then
            no_bounded_uniquely_successful_rounds w from to
        else
            (Ordinal valid_N_rounds);
    ret r.    


Definition expected_no_bounded_uniquely_successful_rounds (schedule : seq.seq RndGen) (from to : nat) :=
    expected_value (comp_no_bounded_uniquely_successful_rounds schedule from to).

Definition unwrap_computation (schedule:seq.seq RndGen) : dist [finType of World] :=
    evalDist (
        o_w' <-$ world_step initWorld schedule;
        r <- if o_w' is some(w) then
                w
            else
                (*should never happen*)
                initWorld;
        ret r).

About no_bounded_uniquely_successful_rounds.

(* Given a world w, produced by a schedule s, asserts that typical_execution holds *)
Definition typical_execution (w : World) (schedule : seq.seq RndGen) (from to : nat) :=
    (* (R1 - eps) * E[ X'(S) ] < X'(S)*)
    (R1 - Epsilon_concentration_of_blocks) * (expected_no_bounded_successful_rounds schedule from to) < INR (nat_of_ord (no_bounded_successful_rounds w from to)) /\
    (* X(S) < (1 + eps)E[ X(S) ],*)
    INR (nat_of_ord (no_successful_rounds w from to)) < (R1 + Epsilon_concentration_of_blocks) * (expected_no_successful_rounds schedule from to) /\
    (* (1 - eps) * E[ Y'(S) ] < Y'(S) *)
    (R1 - Epsilon_concentration_of_blocks) * (expected_no_bounded_uniquely_successful_rounds schedule from to) < INR (nat_of_ord (no_bounded_uniquely_successful_rounds w from to)) /\
    (* Z (S) < (1 + eps) E[ Z(S) ] *)
    INR (nat_of_ord (no_adversarial_blocks w from to)) < (R1 + Epsilon_concentration_of_blocks) * (expected_no_adversarial_blocks schedule from to) /\
    (* no insertion occurred *)
    ~~ (insertion_occurred w from to) /\
    (* no copies occurred *)
    ~~ (copy_occurred w from to) /\
    (* no predictions occurred *)
    ~~ (prediction_occurred w from to).
    
