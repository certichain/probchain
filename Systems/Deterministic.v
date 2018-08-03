From Probchain
Require Import Comp Notationv1 BlockChain Protocol OracleState BlockMap InvMisc Parameters FixedList FixedMap.
(* Note: if coq complains about inconsistent assumptions over ...
  touch Probability/Comp.v, and run make*)



From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype fintype finfun choice ssrfun seq path.

From mathcomp.ssreflect
Require Import tuple.



Set Implicit Arguments.

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
       : Comp [finType of (option  (LocalState * option Message * OracleState * option Block * option BlockChain))] :=
      (* Bitcoin backbone - Algorithm 4 - Line 5 *)
      (* first, find the longest valid chain *)
      let: best_chain := honest_max_valid state oracle_state in
      (* Retrieve the link to the previous block in the chain *)
      if retrieve_head_link best_chain oracle_state is Some(value)
        then
          let: transaction_pool := honest_local_transaction_pool state in
          (* Find a set of transactions to include in the new block *)
          let: (selected_transactions, remaining) := find_maximal_valid_subset transaction_pool best_chain in
          (* Calculate the hash of the block *)
          (hash_result <-$ hash (nonce, value, selected_transactions) oracle_state;
          result <- 
              let: (new_oracle_state, hash) := hash_result in
              (if hash < T_Hashing_Difficulty then
                let: new_block := Bl nonce value selected_transactions in
                            let: new_chain := fixlist_insert best_chain new_block in
                            let: new_state :=
                                  mkLclSt 
                          (*  Drop the transaction pool and message pool after activation *)
                                    new_chain
                                    (* remaining *)
                                    (fixlist_empty Transaction Honest_TransactionPool_size) 
                                    (* (fixlist_rem (honest_local_message_pool state) best_chain) *)
                                    (fixlist_empty [eqType of BlockChain] Honest_MessagePool_size)
                                    in 
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
                          (*  Drop the transaction pool and message pool after activation *)
                          (* (honest_local_transaction_pool state) *)
                          (fixlist_empty Transaction Honest_TransactionPool_size) 
                          (* (honest_local_message_pool state) *)
                          (fixlist_empty [eqType of BlockChain] Honest_MessagePool_size)
                          in
                  (new_state, None, new_oracle_state, None, None)
                else 
                  (* Otherwise we need to move the best chain from the message pool to current*)
                  let: new_state := 
                        mkLclSt 
                          best_chain 
                          (*  Drop the transaction pool and message pool after activation *)
                          (* (honest_local_transaction_pool state) *)
                          (fixlist_empty Transaction Honest_TransactionPool_size) 
                          (* (fixlist_rem (honest_local_message_pool state) best_chain) *)
                          (fixlist_empty [eqType of BlockChain] Honest_MessagePool_size)
                          in
                  (new_state, Some(BroadcastMsg best_chain), new_oracle_state, None, None));
                  ret Some(result))
      (* this is an invalid state - head should always return a value *)
      else (ret None).



Definition adversary_attempt_hash 
    (adversary : Adversary adversary_internal_state) 
    (inflight_messages : MessagePool) 
    (hash_state : Hashed * OracleState) : Comp [finType of (Adversary adversary_internal_state * OracleState * option Block)] :=
  let: (new_hash, oracle_state) := hash_state in
  (* Adversary can generate the block however they want *)
  let: (adversary_partial, (nonce, hashed, transactions)) := (adversary_generate_block adversary) (adversary_state adversary) inflight_messages in
    (hash_result <-$ hash (nonce, hashed, transactions) oracle_state;
    result <- 
      let (new_oracle_state, result) := hash_result in
      let: adversary_new_state := (adversary_provide_block_hash_result adversary) adversary_partial (nonce, hashed, transactions) result in
        if result < T_Hashing_Difficulty 
          then 
            let: block := Bl nonce hashed transactions in
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
          ret (result)).



 Definition option_insert (A : eqType) (m: nat) (list : fixlist A m) (value: option A) : fixlist A m :=
  match value with
    | Some v =>  fixlist_insert list v
    | None => list
    end.


Definition retrieve_actor (list : n_max_actors.-tuple [eqType of ([eqType of LocalState] * [eqType of bool])])  (addr : Addr) : option (LocalState * bool).
  case addr eqn: H.
  case (m < n_max_actors) eqn: H'.
  exact (Some (tnth list (Ordinal H'))).
  exact None.
Defined.

Print retrieve_actor.



Fixpoint world_step (w : World) (s : seq RndGen) : Comp [finType of (option World)] :=
    match s with
      (* world_step uses the scheduler as it's decreasing argument *)
      | [::] => ret (Some w)
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
              (ret None)
          | HonestTransactionGen (transaction , addr) => 
          (* that the address is a valid uncorrupted one *)
          let: state := world_global_state w in
          let: actors := global_local_states state in 
          let: (actor, is_corrupt) := tnth actors addr in 
           if is_corrupt 
            then
              (* recieving an honest transaction gen for a node that has been corrupted is an invalid result *)
              (ret None)
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
                    (ret None)

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
            (ret None)
          | HonestMintBlock  => 
           (* that the currently active is an uncorrupted node *)
           if honest_activation (world_global_state w) is Some(real_addr) then
            let: state := world_global_state w in
            let: actors := global_local_states state in 
            let: addr := global_currently_active state in
            let: adversary := global_adversary state in
            let: round := global_current_round state in
            let: maybe_actor_pair := retrieve_actor actors addr in
            if maybe_actor_pair is Some(pr) then
              let: (dated_actor, is_corrupt) := pr in 
              (* Update transactions of activated node - we only read transactions upon minting *)
              let: actor := update_transaction_pool real_addr dated_actor (world_transaction_pool w) in
              (* broadcast if successful - else increment proof of work *)
              (* an actor attempts a hash with a random value *)
              nonce <-$ gen_random;
              maybe_attempt_result <-$  honest_attempt_hash (world_hash w) nonce actor; 
              result <-$ (if maybe_attempt_result is Some(attempt_result) then
                  w' <- 
                    let: (updated_actor, new_message, new_oracle, new_block, new_chain) := attempt_result in 
                    let: new_actors := set_tnth actors (updated_actor, is_corrupt) addr in 
                    (* then increment the currently active and perform bookkeeping *) 
                    let: new_state := mkGlobalState 
                        new_actors
                        adversary
                        addr
                        round in
                    let: updated_state := update_round new_state in
                      mkWorld
                        updated_state 
                        (world_transaction_pool w)
                        (option_insert (world_inflight_pool w) new_message )
                        (world_message_pool w)
                        new_oracle
                        (BlockMap_put_honest_on_success new_block round (world_block_history w))
                        (option_insert (world_chain_history w) new_chain) ;
                        nw <-$ (world_step w' t);
                        ret nw
                  else
                    ret None);
                  ret result
                else 
                  (ret None)

          else
            (* recieving an honest mint block when the currently active node is corrupted is an invalid result*)
            (ret None)
          | AdvMintBlock   => 
            (* Note: No guarantees of validity here *)
            let: state := world_global_state w in
            let: actors := global_local_states state in 
            let: addr := global_currently_active state in
            let: adversary := global_adversary state in
            let: round := global_current_round state in
 
            let: adv_state := (adversary_state adversary) in
            let: (new_adv_state, tx, recipients) := (adversary_send_transaction adversary) adv_state in
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
            let: new_state := mkGlobalState actors new_adversary addr round in
            let: new_transaction_pool := fixlist_insert (world_transaction_pool w) (MulticastTransaction (tx, recipients)) in
            let: w' := 
              mkWorld
                new_state
                new_transaction_pool
                (world_inflight_pool w)
                (world_message_pool w)
                (world_hash w)
                (world_block_history w)
                (world_chain_history w) in
                world_step w' t

          | AdvTransactionGen  => 
           (* Note: No guarantees of validity here *)
           let: state := world_global_state w in
           let: actors := global_local_states state in 
           let: addr := global_currently_active state in
           let: adversary := global_adversary state in
           let: round := global_current_round state in
 
           let: adv_state := (adversary_state adversary) in
           let: (new_adv_state, tx, recipients) := (adversary_send_transaction adversary) adv_state in
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
            let: new_state := mkGlobalState actors new_adversary addr round in
            let: new_transaction_pool := fixlist_insert (world_transaction_pool w) (MulticastTransaction (tx, recipients)) in
           let: w' := 
            mkWorld
              new_state
              new_transaction_pool
              (world_inflight_pool w)
              (world_message_pool w)
              (world_hash w)
              (world_block_history w)
              (world_chain_history w) in

                world_step w' t

          | AdvCorrupt addr => 
          (* That the current active node is a corrupted one *)
          if adversary_activation (world_global_state w) then
            (* that the index is valid, and to a uncorrupt node *)
            let: state := world_global_state w in
            let: actors := global_local_states state in 
            let: addr := global_currently_active state in
            let: adversary := global_adversary state in
            let: round := global_current_round state in
            if is_uncorrputed_actor actors addr is Some((real_addr, actor)) then
              if no_corrupted_players (world_global_state w) < t_max_corrupted then
                let: new_actors := set_tnth actors (actor, true) real_addr  in 
                let: new_state := mkGlobalState new_actors adversary addr round in
                let: w' := 
                  mkWorld
                    new_state
                    (world_transaction_pool w)
                    (world_inflight_pool w)
                    (world_message_pool w)
                    (world_hash w)
                    (world_block_history w)
                    (world_chain_history w) in
                      world_step w' t
              else
              (* It is an invalid schedule to have advcorrupt when the adversary isnt' active*)
                (ret None)

            else 
              (* It is an invalid schedule to have advcorrupt when the adversary isnt' active*)
              (ret None)
            else
            (* It is an invalid schedule to have advcorrupt when the adversary isnt' active*)
              (ret None)

          | AdvBroadcast (addresses) => 
            (* that the currently active node is a corrupted one  *)
            if adversary_activation (world_global_state w) then
              (* that the index is valid *)
              let: state := world_global_state w in
              let: actors := global_local_states state in 
              let: addr := global_currently_active state in
              let: adversary := global_adversary state in
              let: round := global_current_round state in

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
              let: new_state := mkGlobalState actors new_adversary addr round in
              let w' := 
                mkWorld
                  new_state
                  (world_transaction_pool w)
                  (fixlist_insert (world_inflight_pool w) (MulticastMsg  addresses chain))
                  (world_message_pool w)
                  (world_hash w)
                  (world_block_history w)
                  (world_chain_history w) in
                  world_step w' t 
            else
              (* It is an invalid schedule to have a adv broadcast when the adversary isn't active*)
              (ret None)
          | AdversaryEnd  => 
          if adversary_activation (world_global_state w)  then
            (* increment round *)
            let: updated_state := update_round (world_global_state w) in
                let: w' := 
                  mkWorld
                    (world_global_state w)
                    (world_transaction_pool w)
                    (world_inflight_pool w)
                    (world_message_pool w)
                    (world_hash w)
                    (world_block_history w)
                    (world_chain_history w) in
                  world_step w' t 

          else
            (* It is an invalid schedule to have an adversary end when the adversary is not active*)
            (ret None)

        end
      end.


