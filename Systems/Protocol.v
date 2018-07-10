
Require Import FMapAVL.
Require Import Coq.Structures.OrderedTypeEx.
Require Import OrderedType.
(* Implementation of Bitcoin Protocol *)
(* Does not compile yet - as probability issues have not been resolved. *)
From Probchain
Require Import BlockChain OracleState BlockMap InvMisc InvBlock.


Require Coq.Program.Tactics.
Require Coq.Program.Wf.
From mathcomp.ssreflect Require Import ssreflect ssrbool ssrnat seq ssrfun eqtype. Set Implicit Arguments.
(* Unset Strict Implicit. *)
(* Unset Printing Implicit Defensive. *)

Parameter adversary_internal_state : Type.
Parameter adversary_internal_initial_state : adversary_internal_state.
Parameter adversary_internal_state_change : adversary_internal_state -> adversary_internal_state.
Parameter adversary_internal_insert_transaction: adversary_internal_state -> Transaction -> adversary_internal_state.
Parameter adversary_internal_insert_chain: adversary_internal_state -> BlockChain -> adversary_internal_state.
Parameter adversary_internal_generate_block: adversary_internal_state -> MessagePool -> (adversary_internal_state * (Nonce * Hashed * seq Transaction * nat)).
Parameter adversary_internal_provide_block_hash_result: adversary_internal_state -> (Nonce * Hashed * seq Transaction * nat) -> Hashed -> adversary_internal_state.
Parameter adversary_internal_send_chain: adversary_internal_state -> (adversary_internal_state * BlockChain).
Parameter adversary_internal_send_transaction: adversary_internal_state -> (adversary_internal_state * Transaction).



Parameter n_max_actors : nat.
(* Should these have different names from the proof for legibility? *)
(* maximum number of nodes that can be corrupted *)
Parameter t_max_corrupted : nat.
(* a hash is valid iff hash(block) < T*)
Parameter T_Hashing_Difficulty : nat.
(* delay between activation and success *)
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

  
Definition verify_hash (blk : Block) (oracle : OracleState) : option Hashed := 
   OracleState_find (block_link blk, block_records blk, block_proof_of_work blk) oracle.


(*
  An adversary's state consists of
  1. Adversary's hidden state - can not be introspected
  2. Adversary's state change transition
  3. all transactions it has been delivered.
  4. All chains it has ever seen
  5. an extra parameter to persist proof of work calculations between rounds. 
  6. the last round it attempted a hash - it can only attempt hashing 
     if this value is less than the current round*)
Record Adversary := mkAdvrs {
  T : Type; (* Inner adversary's state, whose type cannot be introspected *)

  adversary_state : T;
  adversary_state_change: T -> T; (* Changing the state -- an operation provided by an adversary *) 
  adversary_insert_transaction: T -> Transaction -> T;
  adversary_insert_chain: T -> BlockChain -> T;

  (* Required to allow adversary limited queries to the oracle*)
  (* the adversary can propose a block to be hashed*)
  adversary_generate_block: T -> MessagePool -> (T * (Nonce * Hashed * seq Transaction * nat));
  (* the result of the hash is returned to the adversary through this method - is the block necassary? *)
  (* it has to be structured this way, as we can not allow the adversary access to the oracle directly*)
  adversary_provide_block_hash_result: T -> (Nonce * Hashed * seq Transaction * nat) -> Hashed -> T;

  (* Required to allow the adversary to broadcast chains *)
  (* I'm not sure how assertions about the blockchain being unable to randomly guess valid blockchains will be made*)
  adversary_send_chain: T -> (T * BlockChain);
  adversary_send_transaction: T -> (T * Transaction);

  (* adversary_local_transaction_pool: seq Transaction; *)
  (* adversary_local_message_pool: seq BlockChain; *)

  (* Additional info *)
  adversary_last_hashed_round: nat;
}.






Definition initAdversary  := 
  mkAdvrs 
    adversary_internal_initial_state 
    adversary_internal_state_change 
    adversary_internal_insert_transaction
    adversary_internal_insert_chain
    adversary_internal_generate_block
    adversary_internal_provide_block_hash_result
    adversary_internal_send_chain
    adversary_internal_send_transaction
    0.


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

Definition initLocalState := mkLclSt [::] [::] [::] 0.

(* GlobalState consists of 
      1. A sequence of LocalStates, and a boolean representing whether the state is corrupted
      2. An address representing the currently executing entity - when addr == length of local states + 1,
         the round is complete
      3. A number representing the current round
*)
Definition GlobalState := ((seq (LocalState * bool) * Adversary) * Addr * nat)%type.
Definition initGlobalState : GlobalState := ((repeat (initLocalState, false) n_max_actors, initAdversary), 0, 0).


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
  world_hash: OracleState;
  (* Contains every block seen *)
  world_block_history: BlockMap;
  (* Contains every chain ever seen*)
  world_chain_history: seq BlockChain;
}.

Definition initWorld := mkWorld initGlobalState [::] [::] (repeat [::] delta) OracleState_new BlockMap_new [::].

(* A round is complete if the currently_active index is one greater than the length of the actors array *)
Definition round_ended (w: World) :=
(world_global_state w).1.2 = ((length (world_global_state w).1.1.1) + 1)
. 

Definition world_current_addr (w : World) :=
  (world_global_state w).1.2.

Definition world_adversary (w : World) :=
  (world_global_state w).1.1.2.

Definition world_actors (w : World) :=
  (world_global_state w).1.1.1.

Definition world_round_no (w : World) :=
  (world_global_state w).2.

Definition no_corrupted_players (state: GlobalState) :=
    let: ((actors, adversary), active, round) := state in 
      length (filter (fun actor => actor.2) actors).



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



(* Implements the round robin - each actor activated once a round mechanism 
   Once the last actor, and then the adversary has activated, the function does
   not do anything else *)
Definition update_round (state : GlobalState) : GlobalState := let: ((actors, adversary), active, round) := state in 
  if (eqn active (length actors).+1) 
  then state
  else ((actors,adversary), active.+1, round).

Definition next_round  (state : GlobalState) : GlobalState := let: ((actors, adversary), active, round) := state in 
  if (eqn active (length actors).+1) 
  then ((actors, adversary), 0, round.+1)
  else state.






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
      let: old_adv_state := adversary_state adversary in
      let: new_adv_state := (adversary_insert_chain adversary) old_adv_state bc in
      let: new_adversary := 
                            mkAdvrs
                              new_adv_state
                              (adversary_state_change adversary)
                              (adversary_insert_transaction adversary)
                              (adversary_insert_chain adversary)
                              (adversary_generate_block adversary)
                              (adversary_provide_block_hash_result adversary)
                              (adversary_send_chain adversary)
                              (adversary_send_transaction adversary)
                              (adversary_last_hashed_round adversary) in
      ((actors, new_adversary), active, round)
  else
    let: current_chain := honest_current_chain actor in
    let: local_transaction_pool := honest_local_transaction_pool actor in
    (* Check whether the blockchain is already in the pool *)
    let: message_pool := (honest_local_message_pool actor) in
    if bc \in message_pool then
      state
    else
      let: new_message_pool := bc :: message_pool in
      let: proof_of_work := honest_proof_of_work actor in 
      let: new_actor := mkLclSt current_chain local_transaction_pool new_message_pool proof_of_work in
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

Definition update_adversary_round (adversary : Adversary) (round : nat) : Adversary :=
  mkAdvrs
    (adversary_state adversary)
    (adversary_state_change adversary)
    (adversary_insert_transaction adversary)
    (adversary_insert_chain adversary)
    (adversary_generate_block adversary)
    (adversary_provide_block_hash_result adversary)
    (adversary_send_chain adversary)
    (adversary_send_transaction adversary)
    round.




    
(* Small wrapper around arbitrary adversary strategy function*)
Definition adversary_attempt_hash 
    (adversary : Adversary) 
    (inflight_messages : MessagePool) 
    (hash_state : Hashed * OracleState) : (Adversary * OracleState * option Block) :=
  let: (new_hash, oracle_state) := hash_state in
  (* Adversary can generate the block however they want *)
  let: (adversary_partial, (nonce, hashed, transactions, pow)) := (adversary_generate_block adversary) (adversary_state adversary) inflight_messages in
  let: (new_oracle_state, result) := hash new_hash (hashed, transactions, pow) oracle_state in
  let: adversary_new_state := (adversary_provide_block_hash_result adversary) adversary_partial (nonce, hashed, transactions, pow) result in
  (* let: adversary_new_state := adversary_partial in *)
    if result < T_Hashing_Difficulty 
      then 
        let: block := Bl nonce hashed transactions pow in
        let: new_adv :=  mkAdvrs
          adversary_new_state
          (adversary_state_change adversary)
          (adversary_insert_transaction adversary)
          (adversary_insert_chain adversary)
          (adversary_generate_block adversary)
          (adversary_provide_block_hash_result adversary)
          (adversary_send_chain adversary)
          (adversary_send_transaction adversary)
          (adversary_last_hashed_round adversary) in
            (new_adv, new_oracle_state, Some block)
      else 
        let: new_adv :=  mkAdvrs 
          adversary_new_state
          (adversary_state_change adversary)
          (adversary_insert_transaction adversary)
          (adversary_insert_chain adversary)
          (adversary_generate_block adversary)
          (adversary_provide_block_hash_result adversary)
          (adversary_send_chain adversary)
          (adversary_send_transaction adversary)
          (adversary_last_hashed_round adversary) in
            (new_adv, new_oracle_state, None).


Definition validate_blockchain_links (bc : BlockChain) (oracle_state : OracleState) : bool :=
  match bc with
    | [::] => true (* Vacuously true *)
    | h :: t =>
        let: (_, result) := 
        foldr
          (fun pred_block last_pair  => 
            let: (block, has_failed) := last_pair in
            if has_failed
              then (pred_block, has_failed)
              else
                match verify_hash pred_block oracle_state with
                  | None => (pred_block, true)
                  | Some(hash_value) => 
                      if block_link block == hash_value 
                        then (pred_block, false)
                        else (pred_block, true)
                end
          )
          (h, false)  
          t
          in result
  end.

Definition validate_blockchain (bc : BlockChain) (oracle_state: OracleState) : bool :=
  (* a blockchain is valid if the links are well formed *)
  validate_blockchain_links bc oracle_state && 
  (* and all transactions are valid *)
  validate_transactions (BlockChain_unwrap bc).
  
(* finds the longest valid chain for a node *)
Definition honest_max_valid (state: LocalState) (oracle_state: OracleState) : BlockChain :=
  foldr 
  (fun new_chain best_chain => 
    (* First check whether the chain is valid *)
    if validate_blockchain new_chain oracle_state
      (* If it's longer, adopt it *)
      then if length new_chain > length best_chain
          then new_chain
          (* in cases where the lengths are equal... *)
          else if length new_chain == length best_chain
            (* Use the equiv of FCR to conclude *)
            then if BlockChain_compare_lt best_chain new_chain 
              then new_chain
              else best_chain
            else best_chain
      else best_chain 
  )
  (honest_current_chain state)
  (honest_local_message_pool state).


Definition find_maximal_valid_subset  (transactions : seq Transaction) (blk: BlockChain) : (seq Transaction * seq Transaction) :=
(* naive approach - iterate through transactions and only include those that are valid 
   specifically it's naive because it assumes that all transactions are delivered in order
    (i.e if invalid, reordering the sequence won't change whether it's valid or not)
   but I believe this is a correct assumption as transactions are delivered immediately *)
   let chain_transactions := BlockChain_unwrap blk in
   foldr
      (fun transaction prev_pair => 
            let: (already_included, remaining) := prev_pair in
            if Transaction_valid transaction (already_included ++ chain_transactions)
              then (transaction :: already_included, remaining)
              else (already_included, transaction :: remaining))
      ([::], [::])
      transactions.

Definition retrieve_head_link (b : BlockChain) (oracle_state : OracleState) : option Hashed :=
  match b with
    | [::] => Some(0)
    | h :: t => verify_hash h oracle_state
  end.


(* Implementation of the bitcoin backbone protocol *)
Definition honest_attempt_hash  
      (hash_state: Hashed * OracleState) 
      (nonce : Nonce) (state : LocalState) 
       : (LocalState * option Message * OracleState * option Block * option BlockChain) :=
      let: (random_value, oracle_state) := hash_state in
      (* Bitcoin backbone - Algorithm 4 - Line 5 *)
      (* first, find the longest valid chain *)
      let: best_chain := honest_max_valid state oracle_state in
      (* Retrieve the link to the previous block in the chain *)
      if retrieve_head_link best_chain oracle_state is Some(value)
        then
          let: transaction_pool := honest_local_transaction_pool state in
          (* Find a set of transactions to include in the new block *)
          let: (selected_transactions, remaining) := find_maximal_valid_subset transaction_pool best_chain in
          let: proof_of_work := honest_proof_of_work state in
          (* Calculate the hash of the block *)
          let: (new_oracle_state, hash) := hash random_value (value, selected_transactions, proof_of_work) oracle_state in
          if hash < T_Hashing_Difficulty then
            (* New block has been minted *)
            let: new_block := Bl nonce value selected_transactions proof_of_work in
            let: new_chain := new_block :: best_chain in
            let: new_state :=
                  mkLclSt 
                    new_chain
                    remaining
                    (rem best_chain (honest_local_message_pool state))
                    0 in (* reset the proof of work *)
            (new_state, Some(BroadcastMsg new_chain), new_oracle_state, Some new_block, Some new_chain)
          else
            (* Constructed block did not meet the difficulty level *)
            (* if the longest chain is actually the current chain *)
            if best_chain == (honest_current_chain state)
              (* then the only thing to change is to increment the proof of work*)
              then 
               let: new_state := 
                    mkLclSt 
                      (honest_current_chain state) 
                      (honest_local_transaction_pool state)
                      (honest_local_message_pool state)
                      ((honest_proof_of_work state).+1) in
              (new_state, None, new_oracle_state, None, None)
            else 
              (* Otherwise we need to move the best chain from the message pool to current*)
              let: new_state := 
                    mkLclSt 
                      best_chain 
                      (honest_local_transaction_pool state)
                      (rem best_chain (honest_local_message_pool state))
                      ((honest_proof_of_work state).+1) in
              (new_state, Some(BroadcastMsg best_chain), new_oracle_state, None, None)
        else 
          if best_chain == (honest_current_chain state)
            then (state, None, oracle_state, None, None)
          else 
            let: new_state := 
                  mkLclSt 
                    best_chain 
                    (honest_local_transaction_pool state)
                    (rem best_chain (honest_local_message_pool state))
                    (honest_proof_of_work state) in
            (new_state, Some(BroadcastMsg best_chain), oracle_state, None, None)
    .

    

Definition update_transaction_pool (addr : Addr) (initial_state : LocalState) (transaction_pool: TransactionPool) : LocalState :=
  foldr
  (fun (txMsg : TransactionMessage) state => 
      match txMsg with
        | BroadcastTransaction tx => 
             if tx \in (honest_local_transaction_pool state) 
              then state
              else 
                mkLclSt 
                  (honest_current_chain state)
                  (tx :: (honest_local_transaction_pool state))
                  (honest_local_message_pool state)
                  (honest_proof_of_work state)
        | MulticastTransaction (tx, recipients) =>
          if addr \in recipients 
            then if tx \in (honest_local_transaction_pool state) 
              then state
              else 
                mkLclSt 
                  (honest_current_chain state)
                  (tx :: (honest_local_transaction_pool state))
                  (honest_local_message_pool state)
                  (honest_proof_of_work state)
            else state
      end)
  initial_state
  transaction_pool.

Definition update_adversary_transaction_pool  (initial_adv: Adversary) (transaction_pool: TransactionPool) : Adversary :=
    foldr 
      (fun (txMsg : TransactionMessage) adversary => 
      let: adv_state := adversary_state adversary in
      let: partial_adv := (adversary_insert_transaction adversary) adv_state in
        match txMsg with
          | BroadcastTransaction tx => 
            let: new_adv_state := partial_adv tx in
                            mkAdvrs
                              new_adv_state
                              (adversary_state_change adversary)
                              (adversary_insert_transaction adversary)
                              (adversary_insert_chain adversary)
                              (adversary_generate_block adversary)
                              (adversary_provide_block_hash_result adversary)
                              (adversary_send_chain adversary)
                              (adversary_send_transaction adversary)
                              (adversary_last_hashed_round adversary) 
          | MulticastTransaction (tx, _) =>
            let: new_adv_state := partial_adv tx in
                            mkAdvrs
                              new_adv_state
                              (adversary_state_change adversary)
                              (adversary_insert_transaction adversary)
                              (adversary_insert_chain adversary)
                              (adversary_generate_block adversary)
                              (adversary_provide_block_hash_result adversary)
                              (adversary_send_chain adversary)
                              (adversary_send_transaction adversary)
                              (adversary_last_hashed_round adversary) 
        end)
      initial_adv
      transaction_pool.



Inductive world_step (w w' : World) (random : RndGen) : Prop :=
  (* when a round changes... *)
   | RoundChange of 
        round_ended w &
        (*  - we need to reset the currently active node to the start (round-robin) *)
        let: updated_state := next_round (world_global_state w) in
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
            (world_block_history w)
            (world_chain_history w)
    | TransactionDrop (n : nat) of
        (* assert that random is of form TransactionDrop
           and index is actually an index into the transaction pool 
           then remove that entry*)
           random = TransactionDrop n &
           let: transaction_pool := world_transaction_pool w in
           n < length transaction_pool & let: new_transaction_pool := rem_nth n (world_transaction_pool w) in
           w' = 
            mkWorld
              (world_global_state w)
              new_transaction_pool
              (world_inflight_pool w)
              (world_message_pool w)
              (world_hash w)
              (world_block_history w)
              (world_chain_history w)
    | HonestTransaction (transaction : Transaction) (addr : Addr) of
          (* assert that random is of form TransactionGen , round*)
           random = HonestTransactionGen (transaction, addr) &
          (* that the address is a valid uncorrupted one *)
           let: ((actors, _), _, _) := (world_global_state w) in 
           addr < length actors  &
           let: ((actors, _), _, _) := (world_global_state w) in 
           let: default := (mkLclSt nil nil nil 0, false) in
           let: (actor, is_corrupt) := nth default actors addr in 
           is_corrupt = false &
           (* that the transaction is valid with respect to the chain of the actor  *)
           let: ((actors, adversary), active, round) := (world_global_state w) in 
           let: default := (mkLclSt nil nil nil 0, false) in
           let: (actor, _) := nth default actors addr in 
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
              (world_block_history w)
              (world_chain_history w)
    | HonestMint (random_value : Hashed) (nonce: Nonce) of
           (* assert that random is of form MintBlock *)
           random = HonestMintBlock (random_value, nonce) &
           (* that the currently active is an uncorrupted node *)
           honest_activation (world_global_state w) &
           let: ((actors, adversary), active, round) := (world_global_state w) in 
           let: default := (mkLclSt nil nil nil 0, false) in
           let: oracle := (world_hash w) in
           let: (dated_actor, is_corrupt) := nth default actors active in 
           (* Update transactions of activated node - we only read transactions upon minting *)
           let: actor := update_transaction_pool active dated_actor (world_transaction_pool w) in
           (* broadcast if successful - else increment proof of work *)
           (* an actor attempts a hash with a random value *)
           let: (updated_actor, new_message, new_oracle, new_block, new_chain) := honest_attempt_hash (random_value, oracle) nonce actor in
           let: new_actors := set_nth default actors active (updated_actor, is_corrupt) in 
           (* then increment the currently active and perform bookkeeping *) 
           let: updated_state := update_round ((new_actors, adversary), active, round) in
           w' = 
             mkWorld
              updated_state 
              (world_transaction_pool w)
              (option_cons new_message (world_inflight_pool w))
              (world_message_pool w)
              new_oracle
              (BlockMap_put_honest_on_success new_block round (world_block_history w))
              (option_cons new_chain (world_chain_history w))
    | AdversaryTransaction (recipients : seq nat) of
        (* assert that random is of form TransactionGen *)
          random = AdvTransactionGen recipients &
          (* Note: Like honest actors, Adversaries can send transactions at any time *)
           (* Note: No guarantees of validity here *)
           let: ((actors, adversary), active, round) := (world_global_state w) in 
           let: adv_state := (adversary_state adversary) in
           let: (new_adv_state, tx) := (adversary_send_transaction adversary) adv_state in
           let: new_adversary :=
                            mkAdvrs
                              new_adv_state
                              (adversary_state_change adversary)
                              (adversary_insert_transaction adversary)
                              (adversary_insert_chain adversary)
                              (adversary_generate_block adversary)
                              (adversary_provide_block_hash_result adversary)
                              (adversary_send_chain adversary)
                              (adversary_send_transaction adversary)
                              (adversary_last_hashed_round adversary) in
           let: new_state := ((actors, new_adversary), active, round) in
           let: new_transaction_pool := (MulticastTransaction (tx, recipients)) :: (world_transaction_pool w) in
           w' = 
            mkWorld
              new_state
              new_transaction_pool
              (world_inflight_pool w)
              (world_message_pool w)
              (world_hash w)
              (world_block_history w)
              (world_chain_history w)
    | AdversaryMint  (random_value : Hashed) of
        (* assert that random is of form MintBlock *)
          random = AdvMintBlock random_value  &
           (* that the currently active node is a corrupted node, increment proof of work *)
           adversary_activation (world_global_state w)  &
           (* assert that last_hashed_round is less than current_round *)
           let: ((_, adversary), _, round) := (world_global_state w) in 
           adversary_last_hashed_round adversary < round &
           let: ((actors, dated_adversary), active, round) := (world_global_state w) in 
           let: oracle := (world_hash w) in
           let: adversary := update_adversary_transaction_pool dated_adversary (world_transaction_pool w) in
           let: (new_adversary, new_oracle, new_block) := adversary_attempt_hash adversary (world_inflight_pool w) (random_value, oracle) in
           let: updated_adversary := update_adversary_round new_adversary round in
           let: updated_state := update_round ((actors, updated_adversary), active, round) in
           w' = 
             mkWorld
              updated_state (world_transaction_pool w)
              (world_inflight_pool w)
              (world_message_pool w)
              new_oracle
              (BlockMap_put_adversarial_on_success new_block round (world_block_history w))
              (world_chain_history w)
    | AdversaryBroadcast (recipients : seq nat) of
        (* assert that random is of form AdversaryBroadcast *)
        random = AdvBroadcast (recipients) &
        (* that the currently active node is a corrupted one  *)
        adversary_activation (world_global_state w)  &
           (* that the index is valid *)
          let: ((actors, adversary), active, round) := (world_global_state w) in 
          let: adv_state := (adversary_state adversary) in
          let: (new_adv_state, chain) := (adversary_send_chain adversary) adv_state in
          let: new_adversary :=
                            mkAdvrs
                              new_adv_state
                              (adversary_state_change adversary)
                              (adversary_insert_transaction adversary)
                              (adversary_insert_chain adversary)
                              (adversary_generate_block adversary)
                              (adversary_provide_block_hash_result adversary)
                              (adversary_send_chain adversary)
                              (adversary_send_transaction adversary)
                              (adversary_last_hashed_round adversary) in
           w' = 
            mkWorld
              (world_global_state w)
              (world_transaction_pool w)
              ((MulticastMsg  recipients chain) :: (world_inflight_pool w))
              (world_message_pool w)
              (world_hash w)
              (world_block_history w)
              (world_chain_history w)
    | AdversaryCorrupt (addr : Addr) of
        (* assert that random is of form AdvCorrupt *)
        random = AdvCorrupt addr &
        (* That the current active node is a corrupted one *)
        adversary_activation (world_global_state w)  &
        (* that the index is valid, and to a uncorrupt node *)
        let: ((actors, _), _, _) := (world_global_state w) in 
        addr < length actors  &
        let: ((actors, _), _, _) := (world_global_state w) in 
        let: default := (mkLclSt nil nil nil 0, false) in
        let: (actor, is_corrupt) := nth default actors addr in 
        is_corrupt = false &
        (* and that the number of corrupt nodes is less than t  *)
        no_corrupted_players (world_global_state w) < t_max_corrupted  &
        let: ((actors, adversary), active, round) := (world_global_state w) in 
        let: default := (mkLclSt nil nil nil 0, false) in
        let: (actor, is_corrupt) := nth default actors addr in 
        let: new_actors := set_nth default actors addr (actor, true) in 
        let: new_global_state := ((new_actors, adversary), active, round) in
           w' = 
            mkWorld
              new_global_state
              (world_transaction_pool w)
              (world_inflight_pool w)
              (world_message_pool w)
              (world_hash w)
              (world_block_history w)
              (world_chain_history w)
      | AdversaryResign of 
       adversary_activation (world_global_state w)  &
       (* increment round *)
       let: updated_state := update_round (world_global_state w) in
           w' = 
            mkWorld
              (world_global_state w)
              (world_transaction_pool w)
              (world_inflight_pool w)
              (world_message_pool w)
              (world_hash w)
              (world_block_history w)
              (world_chain_history w)
.    


Fixpoint reachable_internal (w w' : World) (schedule : seq RndGen) : Prop :=
  match schedule with
    | [::] => w = w'
    | h :: t' => exists (y : World), world_step w y h /\ reachable_internal y w' t'
    end.

(* Clone of function from toychain *)
Definition reachable (w w' : World) : Prop :=
  exists (schedule : seq RndGen), reachable_internal w w' schedule.

Definition adversarial_minority (w : World) :=
  no_corrupted_players (world_global_state w) <= t_max_corrupted.


(* Trivial lemma to ensure that steps work *)
Lemma adversarial_minority_induction  (w w' : World) (q : RndGen) :
   world_step w w' q -> adversarial_minority w -> adversarial_minority w'.
Proof.

  (* TODO(kiran): Complete this proof*)
  move=> S.
  case (S) => w_end dest_w.
  destruct (update_message_pool_queue _ _).
  rewrite dest_w /adversarial_minority => //=.
  rewrite /next_round.
  destruct (world_global_state w).
  case l => //=.
Admitted.


Lemma initWorld_adversarial_minority : adversarial_minority initWorld.
Proof.
  rewrite /initWorld  /adversarial_minority /=.
  case: n_max_actors =>//=.
  suff filter_maintain (A : Type) (P : A -> bool) (x:A) (n:nat) : 
      (~~ P x) -> length (filter (fun actor => P actor) (repeat x n)) = 0.
  move=> n.
  by rewrite filter_maintain.
  move=> f_px.
  elim n.
    by [].
  move=> n0 IHn /=.
  by rewrite ifN.
Qed.


(* Generates an increasing sequence of nats from *from* to *to* inclusive *)
Fixpoint generate_sequence (from : nat) (to : nat) :=
  match to with
    | 0 => nil
    | S t' => if to >= from
              then (generate_sequence from t') ++ [:: to]
              else nil
   end.


Definition block_hash_round (b : Block) (w : World) :=
  match BlockMap_find b (world_block_history w) with
    | Some (is_corrupt, hash_round) => Some(hash_round)
    | None => None
    end.

Definition block_is_adversarial (b : Block) (w : World) :=
  match BlockMap_find b (world_block_history w) with
    | Some (is_corrupt, hash_round) => Some(is_corrupt)
    | None => None
    end.



Definition successful_round (w : World) (r : nat) : bool :=
  length
    (filter
      (fun block_pair =>
        let: (block, is_corrupt, hash_round) := block_pair in  
      (hash_round  == r) && (~~ is_corrupt))
      (world_block_history w)) > 0.


Definition unsuccessful_round (w : World) (r : nat) :=
  length
    (filter
      (fun block_pair =>
        let: (block, is_corrupt, hash_round) := block_pair in  
      (hash_round  == r) && (~~ is_corrupt))
      (world_block_history w)) == 0.



Definition uniquely_successful_round (w : World) (r : nat) :=
  length
    (filter
      (fun block_pair =>
        let: (block, is_corrupt, hash_round) := block_pair in  
      (hash_round  == r) && (~~ is_corrupt))
      (world_block_history w)) == 1.



Definition bounded_successful_round (w : World) (r : nat) :=
  (* (forallb (r' : nat), (r' < r) && (r' >= r - delta) -> unsuccessful_round w r') &&   *)
  (forallb (fun r' => unsuccessful_round w r') (generate_sequence (r - delta) (r - 1))) &&  
    successful_round w r.


Definition bounded_uniquely_successful_round (w : World) (r : nat) :=
  (* (forall (r' : nat), ((r' <= r + delta) && (r' >= r - delta) && (r' != r)) -> unsuccessful_round w r') /\ *)
  (forallb (fun r' => (unsuccessful_round w r') || (r' == r)) (generate_sequence (r - delta) (r + delta))) &&
    (uniquely_successful_round w r).


Definition adversarial_block_count (w : World) (r : nat) :=
  length (filter
      (fun block_pair =>
        let: (block, is_corrupt, hash_round) := block_pair in  
      (hash_round  == r) && is_corrupt)
      (world_block_history w)).

Definition nth_block_is_honest (c : BlockChain) (n : nat) (w : World) :=
  ~~ (block_is_adversarial (nth (Bl 0 0 [::] 0) c n) w).


Definition nth_block_hashed_in_a_uniquely_successful_round (w : World) (chain : BlockChain) (n : nat) :=
  if length chain <= n
    then False
    else 
      let: block := (nth (Bl 0 0 [::] 0) chain n) in
      let: round := block_hash_round block w in
      bounded_uniquely_successful_round w round.
    
Definition nth_block_is_adversarial (w : World) (chain : BlockChain) (n : nat) :=
  if length chain <= n 
    then False
    else
      let: block := (nth (Bl 0 0 [::] 0) chain n) in
      block_is_adversarial block w.

Definition nth_block_equals (w : World) (chain : BlockChain) (n : nat) (block : Block) :=
  if length chain <= n
    then False
    else
      let: other_block := (nth (Bl 0 0 [::] 0) chain n) in
      other_block = block.

Definition nth_block (w : World) (chain : BlockChain) (n : nat) :=
  (nth (Bl 0 0 [::] 0) chain n).

Lemma unique_round (w : World) (n : nat) (chain : BlockChain) :
  reachable initWorld w ->
    chain \in (world_chain_history w) ->
    length chain > n ->
    nth_block_is_honest chain n w  ->
    nth_block_hashed_in_a_uniquely_successful_round w chain n ->
    (forall (other_chain : BlockChain), 
    other_chain \in (world_chain_history w) -> 
    length other_chain > n -> 
    nth_block_is_adversarial w other_chain n  \/ nth_block_equals w other_chain n (nth_block w chain n)).
Admitted.


Definition no_successful_rounds (w : World) (from : nat) (to : nat) : nat :=
  length(filter
    (fun round => bounded_successful_round w round)
    (generate_sequence from to)).

Definition actor_n_chain_length (w : World) (n : nat) : nat :=
  let: (actor, is_corrupted) := nth (mkLclSt nil nil nil 0, false) ((world_global_state w).1.1.1) n in
  length (honest_current_chain actor) .

Definition world_round (w : World) : nat := 
  let: ((_, _), _, round) := world_global_state w in
    round
.

Definition actor_n_is_corrupt (w:World) (n:nat) : bool :=
  let: (actor, is_corrupted) := nth (mkLclSt nil nil nil 0, true) ((world_global_state w).1.1.1) n in
  is_corrupted
.


Lemma chain_growth (w : World) (round : nat) (l : nat) :
  reachable initWorld w ->
  (world_round w) = round ->
  (exists (n : nat), (n < n_max_actors) /\ (actor_n_chain_length w n = l) /\ ~~ (actor_n_is_corrupt w n)) ->
  (forall (future_w : World), 
    reachable w future_w ->
    ((world_round future_w) >= round + delta - 1) ->
    (forall (n : nat), n < n_max_actors -> 
      ~~ (actor_n_is_corrupt w n) ->
      actor_n_chain_length w n >= l + no_successful_rounds w round ((world_round future_w) - 1))).
Proof.
Admitted.


Definition adopt_at_round (w' : World) (w : World) (bc : BlockChain) (agent: Addr) (r : nat) :=
  match r with
    | 0 => false
    | r'.+1 => 
      if 
        (* If the two worlds represent worlds immediately after in rounds *)
        (world_round_no w == r) && 
        (world_round_no w' == r') && 
        (* If the address is valid *)
        (agent < n_max_actors) &&
        (* If the agent has been activated in both rounds *)
        (world_current_addr w  >= agent) &&
        (world_current_addr w'  >= agent) 
        then let: (w_state, w_is_corrupt) := (nth (initLocalState, true) (world_actors w) agent) in
             let: (w'_state, w'_is_corrupt) := (nth (initLocalState, true) (world_actors w') agent) in
              (~~ w_is_corrupt) && (~~ w'_is_corrupt) && 
              (honest_current_chain w'_state != bc) &&
              (honest_current_chain w_state == bc)
        else false
    end.

Definition common_prefix_property (current_w : World) (k r1 r2 : nat) (a1 a2 : Addr) (c1 c2 : BlockChain) :=
  (* current w is valid *)
  reachable initWorld current_w ->
  (world_round_no current_w) >= r2 ->
  r1 <= r2 ->
  (a1 < n_max_actors) -> (a2 < n_max_actors) ->
  ~~ (actor_n_is_corrupt current_w a1) -> ~~ (actor_n_is_corrupt current_w a1) ->
  (* players a1 a2 adopting the chains at rounds r1, r2 *)
  (exists (w' wr1 : World), reachable initWorld w' -> reachable w' wr1 -> reachable wr1 current_w ->  
    adopt_at_round w' wr1 c1 a1 r1) ->
  (exists (w'' wr2 : World), reachable initWorld w'' -> reachable w'' wr2 -> reachable wr2 current_w ->  
    adopt_at_round w'' wr2 c2 a2 r2) ->
  (* then pruning k blocks from the head of c1 is a subsequence of c2*)
  prefix (drop k c1) c2.

