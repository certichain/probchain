
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



Variable hash : 
RndGen -> (Hashed * seq Transaction * nat) -> OracleState -> (OracleState * Hashed).



Record Adversary := mkAdvrs {
  adversary_local_transaction_pool: seq Transaction;
  adversary_local_message_pool: seq BlockChain;
  adversary_proof_of_work: nat;
}.

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
  world_transaction_pool: TransactionPool;
  world_inflight_pool: MessagePool;
  world_message_pool: MessagePool;
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
   RoundChange of round_ended w &
  let: new_state := update_round (world_global_state w) in
  w' = mkWorld new_state (world_transaction_pool w) (world_inflight_pool w) (world_message_pool w) (world_hash w)
.    
