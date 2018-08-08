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

(* 
    this checks for the following:
     1. To have an adversary end when the adversary is not active
     2. To recieve a round ended when the round has not ended
*)

Definition round_management_check (value : RndGen) (acc: (nat * nat * bool)) : option (nat * nat * bool) :=
        let: (current_round, current_addr, adversary_ended) := acc in
        match value with
            (* can occur whenever *)
            | HonestTransactionGen (tx, addr) => Some(acc) 
            (* can occur whenever (with regards to round end) *)
            | TransactionDrop (txPool_ind) => Some(acc)
            (* current_addr should be in the range 0 <= .. < n_max_actors *)
            | HonestMintBlock => 
                (* 
                    if any of
                        - current address has exceeded the number of actors
                        - the adversary has ended
                    the schedule is invalid.
                *)
                if [|| (current_addr >= n_max_actors) | adversary_ended ] then
                    None
                else
                    (*Note: this condition means that current_addr could not equal n_max_actors*)
                    (* so we are safe to increment the current address *)
                    Some(current_round, current_addr.+1, adversary_ended)
            (* current_addr should be in the range 0 <= .. <= n_max_actors *)
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
                        Some(current_round, current_addr.+1, adversary_ended)
            (* can only occur when current_addr is in the range or adversary has not ended *)
            | AdvCorrupt addr => 
                (*
                    if any of
                      - the current addr exceeds the number of players
                        (means addr = n_max_actors.+1 which implies the adversary has ended their round )
                      - the adversary has ended
                *)
                if [|| (current_addr > n_max_actors) | adversary_ended ] then
                    None
                else
                    Some(acc)
            (* can only occur when current_addr is in the range or adversary has not ended *)
            | AdvBroadcast addr_list => 
                 (*
                    if any of
                      - the current addr exceeds the number of players
                        (means addr = n_max_actors.+1 which implies the adversary has ended their round )
                      - the adversary has ended
                *)
                if [|| (current_addr > n_max_actors) | adversary_ended ] then
                    None
                else
                    Some(acc)
            (* can occur whenever *)
            | AdvTransactionGen  => Some(acc)
            (* current_addr should be in the range n_max_actors.+1 *)
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
                Some(current_round.+1, 0, false)
            (* current_addr should be n_max_actors *)
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
                Some(current_round, current_addr.+1, true)
        end
.

Definition rounds_correct_schedule (s : seq RndGen) : bool :=
    isSome (foldr
        (fun rnd state => if state is Some(pr) then round_management_check rnd pr else None)
        (Some (0, 0, false))
        s).


Check (n_max_actors.-tuple bool).




(* 
    this checks for the following:
        1. To recieving an honest transaction gen for a node that has been corrupted
        2. recieving an honest mint block when the currently active node is corrupted
        3. To attempt to mint a block when not during an adversarial activation
        4. To have advcorrupt of an uncorrupted node
        5. To have advcorrupt when the adversary isnt' active
        6. To have a adv broadcast when the adversary isn't active or 
*)

Definition corrupt_players_check (value : RndGen) (acc: (n_max_actors.-tuple bool)) : option (n_max_actors.-tuple bool) :=
        match value with
            | HonestTransactionGen (tx, addr) => Some(acc) 
            | TransactionDrop (txPool_ind) => Some(acc)
            | HonestMintBlock => Some(acc)
            | AdvMintBlock    => Some(acc)
            | AdvCorrupt addr => Some(acc)
            | AdvBroadcast addr_list => Some(acc)
            | AdvTransactionGen  => Some(acc)
            | RoundEnd => Some(acc)
            | AdversaryEnd  => Some(acc)
        end
.








(*
    To recieve an honest transaction gen with an invalid transaction
    To recieve an honest transaction gen when the honest transaction quota is exceeded

    To recieve a transaction drop index for an empty index
    for an Honest party to call hash on an invalid chain

    for the adversary to hash a block multiple times in a round
    For an adversary to generate a transaction if it has exhausted it's quota
    To have advcorrupt when the quota has been met

    To have a adv broadcast when it has exceeded it's quotas for the round

*)