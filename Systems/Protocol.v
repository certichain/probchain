
Require Import FMapAVL.
Require Import Coq.Structures.OrderedTypeEx.
Require Import OrderedType.
(* Implementation of Bitcoin Protocol *)
(* Does not compile yet - as probability issues have not been resolved. *)
From Probchain
Require Import BlockChain OracleState.

From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat seq ssrfun.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.



(* delay between activation and succes *)
Variable delta : nat.
(* given a random generator, a block and the oracle, updates the oracle state and returns a new hashed value *)
Variable hash : 
RndGen -> (Hashed * seq Transaction * nat) -> OracleState -> (OracleState * Hashed).



(*
  An adversary's state consists of
  1. all transactions it has been delivered.
  2. All chains it has ever seen
  3. an extra parameter to persist proof of work calculations between rounds. *)
Record Adversary := mkAdvrs {
  adversary_local_transaction_pool: seq Transaction;
  adversary_local_message_pool: seq BlockChain;
  adversary_proof_of_work: nat;
}.

(* A node's local state consists of 
    1. it's currently held chain
    2. all transactions it has been delivered 
    3. all chains that it has been sent since it's last activation
    4. an extra parameter to persist proof of work calculations between rounds. *)
Record LocalState := mkLclSt {
  honest_current_chain: BlockChain;
  honest_local_transaction_pool: seq Transaction;
  honest_local_message_pool: seq BlockChain;
  honest_proof_of_work: nat;
}.


(* GlobalState consists of 
      1. A sequence of LocalStates, and a boolean representing whether the state is corrupted
      2. An address representing the currently executing entity - when addr == length of local states + 1,
         the round is complete
      3. A number representing the current round
*)
Definition GlobalState := ((seq (LocalState * bool)) * Addr * nat)%type.


Definition MessagePool := seq Message.

Record World := mkWorld {
  world_global_state: GlobalState; 
  (* the transaction pools contains all sent transactions *)
  world_transaction_pool: TransactionPool; 
  (* the inflight pool contains all messages sent in the round *)
  world_inflight_pool: MessagePool;
  (* the world message pool is a queue of messages sent in the past round - once
  the length exceeds delta, the last entry is removed, and all messages delivered *)
  (* thus this achieves the simulation of a delta delay *)
  world_message_pool: seq MessagePool;
  (* represents the shared oracle state *)
  world_hash: OracleState
}.

(* A round is complete if the currently_active index is one greater than the length of the actors array *)
Definition round_ended (w: World) :=
(world_global_state w).1.2 = ((length (world_global_state w).1.1) + 1)
. 


(* Implements the round robin - each actor activated once a round mechanism *)
Definition update_round (state : GlobalState) : GlobalState := let: (actors, active, round) := state in 
  if (eqn active (length actors).+1) 
  then (actors, 0, round.+1) 
  else (actors, active.+1, round).


Inductive world_step (w w' : World) (random : RndGen) : Prop :=
  (* when a round changes... *)
   RoundChange of 
        round_ended w &
        (*  - we need to reset the currently active node to the start (round-robin) *)
        let: new_state := update_round (world_global_state w) in
        (*  - we need to add the current rounds inflight messages to the message pool *)
        (*  - we need to deliver messages older than delta rounds *)
        w' = mkWorld new_state (world_transaction_pool w) (world_inflight_pool w) (world_message_pool w) (world_hash w)
.    