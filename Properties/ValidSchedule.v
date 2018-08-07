From Probchain
Require Import Comp Notationv1 BlockChain Protocol OracleState BlockMap InvMisc Parameters FixedList FixedMap.
(* Note: if coq complains about inconsistent assumptions over ...
  touch Probability/Comp.v, and run make*)



From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype fintype finfun choice ssrfun seq path.

From mathcomp.ssreflect
Require Import tuple.

(* Todo: Update world_step to allow an adversary to hash multiple times during its execution*)


Record ScheduleAccumulator := mkScheduleAcc {
    (* Used for validating the number of rounds doesn't exceed the limit*)
    acc_current_round : nat;
    (* Used for validating that honest blocks are hashed at the right round*)
    acc_current_addr: nat;
    (* Used for validating that the rounds only end at the right time*)
    acc_adversary_ended: bool;
     
}.


Definition initScheduleAccumulator := mkScheduleAcc  0 0 false.


(*
    We know that following a honest mint block, the current addr is increased.
    we also know that following a adversary end it is okay to round end
*)

(* this schedule bind checks for the following:
     1. To have an adversary end when the adversary is not active
     2. To recieve a round ended when the round has not ended
*)

Definition round_management_check (value : RndGen) (acc: ScheduleAccumulator) : option ScheduleAccumulator :=
        let current_round := acc_current_round acc in
        let current_addr := acc_current_addr acc in
        let adversary_ended := acc_adversary_ended acc in
        match value with
            | HonestTransactionGen (tx, addr) => Some(acc) 
            | TransactionDrop (txPool_ind) => Some(acc)
            | HonestMintBlock => 
                (* 
                    if any of
                        - current address has exceeded the number of actors
                        - the adversary has ended
                    when you get a honest mint
                    the schedule is invalid.
                *)
                if [|| (current_addr >= n_max_actors) | adversary_ended ] then
                    None
                else
                    (*Note: this condition means that current_addr could not equal n_max_actors*)
                    (* so we are safe to increment the current address *)
                    Some(mkScheduleAcc current_round current_addr.+1 adversary_ended)
            | AdvMintBlock    => 
                (*
                    if any of
                      - the current addr exceeds the number of players
                      - the adversary has ended
                *)
                if [|| (current_addr > n_max_actors) | adversary_ended ] then
                    None
                else
                    (* if the condition fails, this means that current_addr could equal n_max_actors.
                       this is fine. this represents a hash event when the main adversary is activated *)
                    if current_addr == n_max_actors then
                        (* 
                            we don't change our state at all
                            this one doesn't check for duplicate hashes
                        *)
                        Some(acc)
                    else
                       (* this means this hash is being called by an corrupted party, so increment the round *)
                        Some(mkScheduleAcc current_round current_addr.+1 adversary_ended)
            | AdvCorrupt addr => Some(acc)
            | AdvBroadcast addr_list => Some(acc)
            | AdvTransactionGen  => Some(acc)
            | RoundEnd => 
             (* 
                if any of
                  - current address doesn't equal the number of actors + 1 (following on from adversary end)
                  - the adversary has not ended
                the schedule is invalid
             *)
             if [|| current_addr != n_max_actors.+1 | ~~ adversary_ended ] then
               None
            else  
                Some(mkScheduleAcc current_round.+1 0 false)
            | AdversaryEnd  => 
            (* 
                if any of
                  - current address hasn't just exceeded the number of actors
                  - adversary has already ended
                when you get an adversary end
                the schedule is invalid
            *) 
            if [|| current_addr != n_max_actors | adversary_ended ] then
               None
            else  
                Some(mkScheduleAcc current_round current_addr.+1 true)
        end
.


(* Definition valid_schedule (schedule : seq RndGen) : bool := *)
    (* isSome (foldr schedule_step (Some initScheduleAccumulator) schedule). *)

(*
    To recieving an honest transaction gen for a node that has been corrupted
    To recieve an honest transaction gen with an invalid transaction
    To recieve an honest transaction gen when the honest transaction quota is exceeded
    To recieve a transaction drop index for an empty index
    for an Honest party to call hash on an invalid chain
    recieving an honest mint block when the currently active node is corrupted
    for the adversary to hash a block multiple times in a round
    To attempt to mint a block when not during an adversarial activation
    For an adversary to generate a transaction if it has exhausted it's quota
    To have advcorrupt when the adversary isnt' active
    To have advcorrupt of an uncorrupted node
    To have advcorrupt when the quota has been met
    To have a adv broadcast when the adversary isn't active or when it has exceeded it's quotas for the round
*)