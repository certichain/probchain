
Require Import FMapAVL.
Require Import Coq.Structures.OrderedTypeEx.
Require Import OrderedType.
(* Implementation of Bitcoin Protocol *)
(* Does not compile yet - as probability issues have not been resolved. *)
From Probchain
Require Import BlockChain OracleState InvMisc.


Require Coq.Program.Tactics.
Require Coq.Program.Wf.

From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat seq ssrfun eqtype.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.



(* delay between activation and succes *)
Parameter t : nat.
Parameter delta : nat.

(* given a random generator, a block and the oracle, 
   updates the oracle state and returns a new hashed value *)
Definition hash 
  (rnd : nat) 
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
  adversary_local_transaction_pool: TransactionPool;
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

About nth.

(* A given world step is an honest activation if the current address
   is to a node which has not been corrupted *)
Definition honest_activation (state: GlobalState) :=
    let: ((actors, adversary), active, round) := state in 
    let: default := (mkLclSt nil nil nil 0, false) in
    (length actors) > active /\
    let: (actor, is_corrupt) := nth default  actors active in
      is_corrupt.

(* A given world step is an adversarial activation if the current address
   is to a node which has been corrupted, or the current address is equal to
   the length of the list 
   this is based on the fact that the bitcoin paper states that in the round
   robin scheduling, once all nodes have activated, the adversary activates *)
Definition adversary_activation (state: GlobalState) :=
    let: ((actors, adversary), active, round) := state in 
    let: default := (mkLclSt nil nil nil 0, false) in
    ((length actors) > active /\
    let: (actor, is_corrupt) := nth default  actors active in
      is_corrupt = false) \/ (length actors = active).



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
    (* TODO(Kiran): Check whether the blockchain is already in the pool *) let: local_message_pool := bc :: (adversary_local_message_pool adversary) in
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


Definition insert_multicast_message 
  (addresses: seq Addr) 
  (bc: BlockChain) 
  (initial_state: GlobalState) : GlobalState := 
      foldr
        (fun addr state => insert_message addr bc state)
        initial_state
        addresses.
 


(* insert the corresponding message into every actor's message pool *)
Definition broadcast_message (bc : BlockChain) (state: GlobalState) : GlobalState := state.


(* for each message in messages, send to corresponding actor *)
Definition deliver_messages
  (messages : seq Message) 
  (state : GlobalState) :  GlobalState :=
  foldr 
    (fun (msg : Message) (st: GlobalState) => 
      match msg with
      | MulticastMsg addr bc => insert_multicast_message addr bc st 
      | BroadcastMsg bc => broadcast_message bc st 
      end) 
    state 
    messages.


Definition update_message_pool_queue (message_list_queue: seq (seq Message)) (new_message_list : seq Message) : (seq Message * seq (seq Message)) :=
  if message_list_queue is h :: t
      (* remove the last message_list *)
  then let oldest_message_list := last h t in 
       let removed_message_queue := belast h t in
       (* insert the new message_list at the start of the queue *)
       (oldest_message_list, new_message_list :: removed_message_queue)
      (* else branch shouldn't be called, as the queue should always be at a fixed size *)
  else ([::], new_message_list :: nil).






Variable attempt_hash : (nat * OracleState) -> (LocalState) -> (LocalState * seq Message * OracleState). 


Inductive world_step (w w' : World) (random : RndGen) : Prop :=
  (* when a round changes... *)
   | RoundChange of 
        round_ended w &
        (*  - we need to reset the currently active node to the start (round-robin) *)
        let: updated_state := update_round (world_global_state w) in
        (*  - we need to add the current rounds inflight messages to the message pool *)
        let: new_inflight_pool := nil in
        let: old_inflight_pool := (world_inflight_pool w) in
        (* this will pop off the oldest message list, and insert the old inflight pool *)
        let: (messages_to_be_delivered, new_message_pool) := 
                update_message_pool_queue (world_message_pool w) old_inflight_pool in
        (*  - we need to deliver messages older than delta rounds *)
        let: new_state := deliver_messages messages_to_be_delivered updated_state in
        w' = 
          mkWorld 
            new_state 
            (world_transaction_pool w) 
            new_inflight_pool
            new_message_pool
            (world_hash w)
    | TransactionDrop (n : nat) of
        (* assert that random is of form TransactionDrop
           and index is actually an index into the transaction pool 
           then remove that entry*)
           random = TransactionDrop n &
           let: transaction_pool := world_transaction_pool w in
           n < length transaction_pool &
           let: new_transaction_pool := rem_nth n (world_transaction_pool w) in
           w' = 
            mkWorld
              (world_global_state w)
              new_transaction_pool
              (world_inflight_pool w)
              (world_message_pool w)
              (world_hash w)
    | HonestTransaction (transaction : Transaction) of
        (* assert that random is of form TransactionGen
            that the currently active is an uncorrupted node
           and that the transaction is valid with respect to the chain 
           of currently active*)
           random = HonestTransactionGen transaction &
           honest_activation (world_global_state w) &
           let: ((actors, adversary), active, round) := (world_global_state w) in 
           let: default := (mkLclSt nil nil nil 0, false) in
           let: (actor, _) := nth default actors active in 
           let: transactions := BlockChain_unwrap (honest_current_chain actor) in
           Transaction_valid transaction transactions &
           let: new_transaction_pool := (BroadcastTransaction transaction) :: (world_transaction_pool w) in
           w' = 
            mkWorld
              (world_global_state w)
              new_transaction_pool
              (world_inflight_pool w)
              (world_message_pool w)
              (world_hash w)
    | HonestMint (random_value : nat) of
        (* assert that random is of form MintBlock *)
           random = MintBlock random_value &
           (* that the currently active is an uncorrupted node *)
           honest_activation (world_global_state w) &
           let: ((actors, adversary), active, round) := (world_global_state w) in 
           let: default := (mkLclSt nil nil nil 0, false) in
           let: oracle := (world_hash w) in
           let: (actor, is_corrupt) := nth default actors active in 
           (* broadcast if successful - else increment proof of work *)
           (* an actor attempts a hash with a random value *)
           let: (updated_actor, new_message, new_oracle) := attempt_hash (random_value, oracle) actor in
           let: new_actors := set_nth default actors active (updated_actor, is_corrupt) in 
           (* then increment the currently active and perform bookkeeping *) 
           (* TODO(Kiran): Update transactions of newly activated node *)
           let: updated_state := update_round ((new_actors, adversary), active, round) in
           w' = 
             mkWorld
              updated_state 
              (world_transaction_pool w)
              (new_message ++ (world_inflight_pool w))
              (world_message_pool w)
              new_oracle
    | AdversaryTransaction (transaction: Transaction) (recipients : seq nat) of
        (* assert that random is of form TransactionGen *)
          random = AdvTransactionGen (transaction, recipients) &
           (* that the currently active node is a corrupted node  *)
           adversary_activation (world_global_state w)  &
           (* Note: No guarantees of validity here *)
           let: ((actors, adversary), active, round) := (world_global_state w) in 
           let: new_transaction_pool := (MulticastTransaction (transaction, recipients)) :: (world_transaction_pool w) in
           w' = 
            mkWorld
              (world_global_state w)
              new_transaction_pool
              (world_inflight_pool w)
              (world_message_pool w)
              (world_hash w)
    | AdversaryMint
        (* TODO(kiran): assert that random is of form MintBlock
           that the currently active node is a corrupted node, increment proof of work
           then increment the currently active and perform bookkeeping *)
    | AdversaryBroadcast (chain_no : nat) (recipients : seq nat) of
        (* assert that random is of form AdversaryBroadcast *)
        random = AdvBroadcast (chain_no, recipients) &
        (* that the currently active node is a corrupted one  *)
        adversary_activation (world_global_state w)  &
           (* that the index is valid *)
          let: ((actors, adversary), active, round) := (world_global_state w) in 
          let: blockchain_cache := adversary_local_message_pool adversary in
          (length blockchain_cache) < chain_no &
          let: ((actors, adversary), active, round) := (world_global_state w) in 
          let: blockchain_cache := adversary_local_message_pool adversary in
          let: chain := nth [::] blockchain_cache chain_no in
           w' = 
            mkWorld
              (world_global_state w)
              (world_transaction_pool w)
              ((MulticastMsg  recipients chain) :: (world_inflight_pool w))
              (world_message_pool w)
              (world_hash w)


    | AdversaryCorrupt
        (* assert that random is of form AdvCorrupt
          that the index is valid, and to a uncorrupt node
          and that the number of corrupt nodes is less than t *)
.    
