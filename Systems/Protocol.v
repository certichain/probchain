
Require Import FMapAVL.
Require Import Coq.Structures.OrderedTypeEx.
Require Import OrderedType.
(* Implementation of Bitcoin Protocol *)
(* Does not compile yet - as probability issues have not been resolved. *)
From Probchain
Require Import BlockChain OracleState.


Require Coq.Program.Tactics.
Require Coq.Program.Wf.

From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat seq ssrfun eqtype.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.



(* delay between activation and succes *)
Parameter delta : nat.

(* given a random generator, a block and the oracle, 
   updates the oracle state and returns a new hashed value *)
Definition hash 
  (rnd : RndGen) 
  (blk : (Hashed * seq Transaction * nat))
  (oracle : OracleState) : (OracleState * Hashed) :=
 match OracleState_find blk oracle with
  | Some(value) => (oracle, value)
  | None => let new_oracle := OracleState_put (blk, rnd) oracle in
          (new_oracle, rnd)
 end.




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
Definition GlobalState := ((seq (LocalState * bool) * Adversary) * Addr * nat)%type.


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
(world_global_state w).1.2 = ((length (world_global_state w).1.1.1) + 1)
. 


(* Implements the round robin - each actor activated once a round mechanism *)
Definition update_round (state : GlobalState) : GlobalState := let: ((actors, adversary), active, round) := state in 
  if (eqn active (length actors).+1) 
  then ((actors, adversary), 0, round.+1) 
  else ((actors,adversary), active.+1, round).

 



(* insert the corresponding message into the recipient's message pool *)
Definition insert_message 
  (addr: Addr) 
  (bc: BlockChain) 
  (state: GlobalState) : GlobalState := 
  let: ((actors, adversary), active, round) := state in 
  let: default := (mkLclSt nil nil nil 0, false) in
  let: (actor, corrupted) := nth default actors addr in 
  if corrupted 
  then
    let: local_transaction_pool := adversary_local_transaction_pool adversary in 
    (* TODO(Kiran): Check whether the blockchain is already in the pool *)
    let: local_message_pool := bc :: (adversary_local_message_pool adversary) in
    let: proof_of_work := adversary_proof_of_work adversary in
    let: new_adversary := mkAdvrs local_transaction_pool local_message_pool proof_of_work  in
    ((actors, new_adversary), active, round)
  else
    let: current_chain := honest_current_chain actor in
    let: local_transaction_pool := honest_local_transaction_pool actor in
    let: message_pool := (honest_local_message_pool actor) in
    (* TODO(Kiran): Check whether the blockchain is already in the pool *)
    let: message_pool := bc :: message_pool in
    let: proof_of_work := honest_proof_of_work actor in 
    let: new_actor := mkLclSt current_chain local_transaction_pool message_pool proof_of_work in
    let: new_actors := set_nth default actors addr (new_actor, false) in
    ((new_actors, adversary), active, round)
  .




(* insert the corresponding message into every actor's message pool *)
Definition broadcast_message (bc : BlockChain) (state: GlobalState) : GlobalState := state.

About foldr.

(* for each message in messages, send to corresponding actor *)
Definition deliver_messages_internal
  (messages : seq Message) 
  (state : GlobalState) :  GlobalState :=
  foldr 
  (fun (msg : Message) (st: GlobalState) => 
     match msg with
    | NormalMsg addr bc => insert_message addr bc st 
    | BroadcastMsg bc => broadcast_message bc st 
    end
  ) 
  state 
  messages.



(* deliver messages older than delta rounds *)
Program Fixpoint deliver_messages 
  (message_pool : seq (seq Message)) 
  (state : GlobalState) {measure (size message_pool)} : (seq (seq Message) * GlobalState)  :=
  if message_pool is h :: t' 
  then if  (size message_pool >= delta) 
        then 
          let: oldest_set := last h t' in
          let remaining := belast h t' in
          let new_state := deliver_messages_internal oldest_set state in
          deliver_messages remaining new_state
        else (message_pool, state)
  else (message_pool, state).
Next Obligation.
Proof. by rewrite size_belast. Qed.








Inductive world_step (w w' : World) (random : RndGen) : Prop :=
  (* when a round changes... *)
   RoundChange of 
        round_ended w &
        (*  - we need to reset the currently active node to the start (round-robin) *)
        let: updated_state := update_round (world_global_state w) in
        (*  - we need to add the current rounds inflight messages to the message pool *)
        let: new_inflight_pool := nil in
        let: old_message_pool := (world_inflight_pool w) :: (world_message_pool w) in
        (*  - we need to deliver messages older than delta rounds *)
        let: (new_message_pool, new_state) := deliver_messages old_message_pool updated_state in
        w' = 
          mkWorld 
            new_state 
            (world_transaction_pool w) 
            new_inflight_pool
            new_message_pool
            (world_hash w)
.    

