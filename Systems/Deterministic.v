From Probchain
Require Import Comp Notationv1 BlockChain Protocol OracleState BlockMap InvMisc Parameters FixedList FixedMap.
(* Note: if coq complains about inconsistent assumptions over ...
  touch Probability/Comp.v, and run make*)


From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype fintype choice ssrfun seq path.

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

          (* let: (new_oracle_state, hash) := hash random_value (value, selected_transactions, proof_of_work) oracle_state in
          if hash < T_Hashing_Difficulty then
            (* New block has been minted *)
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
              (new_state, Some(BroadcastMsg best_chain), new_oracle_state, None, None)
        else 
          if best_chain == (honest_current_chain state)
            then (state, None, oracle_state, None, None)
          else 
            let: new_state := 
                  mkLclSt 
                    best_chain 
                    (honest_local_transaction_pool state)
                    (fixlist_rem (honest_local_message_pool state) best_chain )
                    (honest_proof_of_work state) in
            (new_state, Some(BroadcastMsg best_chain), oracle_state, None, None)
    .
 *)
Definition adversary_attempt_hash 
    (adversary : Adversary adversary_internal_state) 
    (inflight_messages : MessagePool) 
    (hash_state : Hashed * OracleState) : (Adversary adversary_internal_state * OracleState * option Block) :=
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




About finType.

(* Fixpoint world_step (w : World) (s : seq RndGen) : option (Comp [finType of World]) := *)
    (* None. *)
