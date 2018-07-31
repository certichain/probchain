From Probchain
Require Import Comp Notationv1 BlockChain Protocol OracleState BlockMap InvMisc Parameters FixedList FixedMap.
(* Note: if coq complains about inconsistent assumptions over ...
  touch Probability/Comp.v, and run make*)


From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype fintype finfun choice ssrfun seq path.

From mathcomp.ssreflect
Require Import tuple.



Definition gen_random : Comp Hashed :=
    y <-$ [0 ... Hash_value ];
    ret y.
About gen_random.

(* given a random generator, a block and the oracle, 
   updates the oracle state and returns a new hashed value *)
Definition hash 
  (blk : oraclestate_keytype)
  (oracle : OracleState) : Comp [finType of (OracleState * Hashed)] :=
 match oraclestate_find blk oracle with
  | Some(value) => ret (oracle, value)
  | None => 
      rnd <-$ gen_random;
      new_oracle <- oraclestate_put blk rnd oracle;
      ret (new_oracle, rnd)
 end.



Definition honest_attempt_hash  
      (oracle_state:  OracleState) 
      (nonce : Nonce) (state : LocalState) 
       : option (Comp [finType of (LocalState * option Message * OracleState * option Block * option BlockChain)]) :=
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
          Some(hash_result <-$ hash (nonce, value, selected_transactions, proof_of_work) oracle_state;
          result <- 
              let: (new_oracle_state, hash) := hash_result in
              (if hash < T_Hashing_Difficulty then
                let: new_block := Bl nonce value selected_transactions proof_of_work in
                            let: new_chain := fixlist_insert best_chain new_block in
                            let: new_state :=
                                  mkLclSt 
                                    new_chain
                                    remaining
                                    (fixlist_rem (honest_local_message_pool state) best_chain)
                                    (Ordinal valid_Maximum_proof_of_work) in (* reset the proof of work *)
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
                          (mod_incr Maximum_proof_of_work valid_Maximum_proof_of_work (honest_proof_of_work state)) in
                  (new_state, None, new_oracle_state, None, None)
                else 
                  (* Otherwise we need to move the best chain from the message pool to current*)
                  let: new_state := 
                        mkLclSt 
                          best_chain 
                          (honest_local_transaction_pool state)
                          (fixlist_rem (honest_local_message_pool state) best_chain)
                          (mod_incr Maximum_proof_of_work valid_Maximum_proof_of_work (honest_proof_of_work state))
                          in
                  (new_state, Some(BroadcastMsg best_chain), new_oracle_state, None, None));
                  ret result)
      (* this is an invalid state - head should always return a value *)
      else None.



Definition adversary_attempt_hash 
    (adversary : Adversary adversary_internal_state) 
    (inflight_messages : MessagePool) 
    (hash_state : Hashed * OracleState) : option (Comp [finType of (Adversary adversary_internal_state * OracleState * option Block)]) :=
  let: (new_hash, oracle_state) := hash_state in
  (* Adversary can generate the block however they want *)
  let: (adversary_partial, (nonce, hashed, transactions, pow)) := (adversary_generate_block adversary) (adversary_state adversary) inflight_messages in
    Some(hash_result <-$ hash (nonce, hashed, transactions, pow) oracle_state;
    result <- 
      let (new_oracle_state, result) := hash_result in
      let: adversary_new_state := (adversary_provide_block_hash_result adversary) adversary_partial (nonce, hashed, transactions, pow) result in
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
                (new_adv, new_oracle_state, None);
          ret result).


(* Inductive world_step (w w' : World) (random : RndGen) : Prop :=
  (* when a round changes... *)
   | RoundChange of 
        random = RoundEnd &
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
        random = AdversaryEnd &
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
 *)

(* Inductive RndGen  := 
    (* used by Honest Parties to generate transactions - nat specifies which actor *)
    | HonestTransactionGen of (Transaction * Addr)
    | TransactionDrop of (ordinal TransactionPool_length)
    (* used by both Honest Parties to mint blocks*)
    (* Hashed represents the return value of the random oracle if the block is new*)
    (* Nonce represents the nonce used to create the block*)
    (* Both parameters will be probabilistically generated *)
    | HonestMintBlock 
    (* the adversary gets an additional parameter specifying which chain
       in it's pool it should mint onto *)
    | AdvMintBlock 
    (* Used to represent the adversary corrupting players - nat is an index into
       which player to corrupt*)
    | AdvCorrupt of Addr
    (* used by adversary parties to broadcast chains - nat is an index into 
       the adversaries local blockchain pool*)
    | AdvBroadcast of (list Addr)
    (* Used by adversary parties to create transactions at any round *)
    | AdvTransactionGen of ((list Addr))
    | RoundEnd
    | AdversaryEnd 
    .
 *)

Fixpoint world_step (w : World) (s : seq RndGen) : option (Comp [finType of World]) :=
    match s with
      (* world_step uses the scheduler as it's decreasing argument *)
      | [::] => Some(ret w)
      | h :: t => 
        match h with
          | RoundEnd => 
            if round_ended w then
              (*  - we need to reset the currently active node to the start (round-robin) *)
              let: updated_state := next_round (world_global_state w) in
              (*  - we need to add the current rounds inflight messages to the message pool *)
              let: new_inflight_pool := initMessagePool  in
          
              let: old_inflight_pool := (world_inflight_pool w) in
              (* this will pop off the oldest message list, and insert the old inflight pool *)
              let: (messages_to_be_delivered, new_message_pool) := 
                      update_message_pool_queue (world_message_pool w) (old_inflight_pool) in
              (*  - we need to deliver messages older than delta rounds *)
              let: new_state := deliver_messages messages_to_be_delivered updated_state in
              let: w' :=  
                mkWorld 
                  new_state 
                  (world_transaction_pool w) 
                  new_inflight_pool
                  new_message_pool
                  (world_hash w)
                  (world_block_history w)
                  (world_chain_history w) in
                    world_step w' t
            else 
              (* To recieve a round ended when the round has not ended is an invalid result*)
              None
          | HonestTransactionGen (transaction , addr) => 
          (* that the address is a valid uncorrupted one *)
          let: state := world_global_state w in
           let: actors := global_local_states state in 
           let: (actor, is_corrupt) := tnth actors addr in 
           if is_corrupt 
            then
              (* recieving an honest transaction gen for a node that has been corrupted is an invalid result *)
              None
            else
              (* that the transaction is valid with respect to the chain of the actor  *)
              let: transactions := BlockChain_unwrap (honest_current_chain actor) in
                if Transaction_valid transaction transactions
                  then
                    let: new_transaction_pool := fixlist_insert (world_transaction_pool w) (BroadcastTransaction transaction) in
                    let: w' := 
                      mkWorld
                        state 
                        new_transaction_pool
                        (world_inflight_pool w)
                        (world_message_pool w)
                        (world_hash w)
                        (world_block_history w)
                        (world_chain_history w) in
                      world_step w' t
                  else 
                    (* To recieve an honest transaction gen with an invalid transaction is an invalid result*)
                    None

          | TransactionDrop (to_drop) => 
           (* assert that random is of form TransactionDrop
           and index is actually an index into the transaction pool 
           then remove that entry*)
           let: transaction_pool := world_transaction_pool w in
           let: n := (nat_of_ord to_drop) in
           let: maybe_transaction := fixlist_get_nth transaction_pool n in
           if maybe_transaction is Some(tx) then
            let: new_transaction_pool := fixlist_remove (world_transaction_pool w) n in
            let: w' := 
              mkWorld
                (world_global_state w)
                new_transaction_pool
                (world_inflight_pool w)
                (world_message_pool w)
                (world_hash w)
                (world_block_history w)
                (world_chain_history w) in
                  world_step w' t
          else 
            (* To recieve a transaction drop index for an empty index is an invalid result*)
            None
          | HonestMintBlock  => None
          | AdvMintBlock   => None
          | AdvCorrupt addr => None
          | AdvBroadcast (addresses) => None
          | AdvTransactionGen ((addresses)) => None
          | AdversaryEnd  => None
        end
      end.
