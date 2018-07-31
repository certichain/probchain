From Probchain
Require Import Comp Notationv1 BlockChain Protocol OracleState BlockMap InvMisc Parameters FixedList FixedMap.
(* Note: if coq complains about inconsistent assumptions over ...
  touch Probability/Comp.v, and run make*)


From mathcomp.ssreflect
Require Import ssreflect ssrnat ssrbool seq fintype eqtype.

Definition example2:=
    x <- 3;
    y <-$ [0 ... 3];
    ret y.
About example2.


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




About finType.

(* Fixpoint world_step (w : World) (s : seq RndGen) : option (Comp [finType of World]) := *)
    (* None. *)
