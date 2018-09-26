From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat seq ssrfun eqtype bigop fintype choice . 
From mathcomp.ssreflect
Require Import tuple.

Require Import Reals Fourier FunctionalExtensionality.
From infotheo
Require Import proba ssrR Reals_ext logb ssr_ext ssralg_ext bigop_ext Rbigop .

Require Import Nsatz.

Require Import Bvector.


From Probchain
Require Import ValidSchedule Deterministic Comp Notationv1 BlockChain Protocol OracleState BlockMap InvMisc Parameters FixedList FixedMap.

Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.ProofIrrelevance.
Require Import Coq.Program.Equality.

Set Implicit Arguments.

Definition hash_step (w w' : World) lclstt addr result blk_rcd hash_val hash_value (os : OracleState) :=
if (result < T_Hashing_Difficulty)%nat
   then
    let
    '(new_chain, _) :=
     fixlist_enqueue (Some {| block_nonce := hash_value; block_link := hash_val; block_records := blk_rcd |})
       (honest_max_valid (update_transaction_pool addr lclstt (world_transaction_pool w')) (world_hash w')) in
     ({|
      honest_current_chain := new_chain;
      honest_local_transaction_pool := fixlist_empty Transaction Honest_TransactionPool_size;
      honest_local_message_pool := fixlist_empty [eqType of BlockChain] Honest_MessagePool_size |},
     Some (BroadcastMsg new_chain), os,
     Some {| block_nonce := hash_value; block_link := hash_val; block_records := blk_rcd |}, 
     Some new_chain)
   else
    if
     honest_max_valid (update_transaction_pool addr lclstt (world_transaction_pool w')) (world_hash w') ==
     honest_current_chain (update_transaction_pool addr lclstt (world_transaction_pool w'))
    then
     ({|
      honest_current_chain := honest_current_chain
                                (update_transaction_pool addr lclstt (world_transaction_pool w'));
      honest_local_transaction_pool := fixlist_empty Transaction Honest_TransactionPool_size;
      honest_local_message_pool := fixlist_empty [eqType of BlockChain] Honest_MessagePool_size |}, None, os, None,
     None)
    else
     ({|
      honest_current_chain := honest_max_valid (update_transaction_pool addr lclstt (world_transaction_pool w'))
                                (world_hash w');
      honest_local_transaction_pool := fixlist_empty Transaction Honest_TransactionPool_size;
      honest_local_message_pool := fixlist_empty [eqType of BlockChain] Honest_MessagePool_size |},
     Some
       (BroadcastMsg
          (honest_max_valid (update_transaction_pool addr lclstt (world_transaction_pool w')) (world_hash w'))),
     os, None, None).

Definition honest_step_world  (w w' : World) lclstt iscrpt addr result blk_rcd hash_val hash_value (os : OracleState) :=
(let
   '(updated_actor, new_message, new_oracle, new_block, new_chain) :=
    hash_step w w' lclstt addr result blk_rcd hash_val hash_value os in
    {|
    world_global_state := (if (eq_op (nat_of_ord (global_currently_active (world_global_state w'))) n_max_actors.+1)%nat as b0
                            return
                              ((eq_op (nat_of_ord (global_currently_active (world_global_state w'))) n_max_actors.+1) = b0 ->
                               GlobalState)
                           then
                            fun _ : (eq_op (nat_of_ord (global_currently_active (world_global_state w'))) n_max_actors.+1) = true =>
                            {|
                            global_local_states := set_tnth (global_local_states (world_global_state w'))
                                                     (updated_actor, iscrpt)
                                                     (global_currently_active (world_global_state w'));
                            global_adversary := global_adversary (world_global_state w');
                            global_currently_active := global_currently_active (world_global_state w');
                            global_current_round := global_current_round (world_global_state w') |}
                           else
                            fun prf : (eq_op (nat_of_ord (global_currently_active (world_global_state w'))) n_max_actors.+1) = false
                            =>
                            ssr_suff ((nat_of_ord (global_currently_active (world_global_state w'))).+1 < n_max_actors + 2)%nat
                              (fun H' : ((global_currently_active (world_global_state w')).+1 < n_max_actors + 2)%nat
                               =>
                               {|
                               global_local_states := set_tnth (global_local_states (world_global_state w'))
                                                        (updated_actor, iscrpt)
                                                        (global_currently_active (world_global_state w'));
                               global_adversary := global_adversary (world_global_state w');
                               global_currently_active := Ordinal (n:=n_max_actors + 2)
                                                            (m:=(global_currently_active (world_global_state w')).+1)
                                                            H';
                               global_current_round := global_current_round (world_global_state w') |})
                              (round_in_range (global_currently_active (world_global_state w'))
                                 (introN eqP (elimTF eqP prf))))
                            (erefl (eq_op (nat_of_ord (global_currently_active (world_global_state w'))) n_max_actors.+1));
    world_transaction_pool := world_transaction_pool w';
    world_inflight_pool := option_insert (world_inflight_pool w') new_message;
    world_message_pool := world_message_pool w';
    world_hash := new_oracle;
    world_block_history := BlockMap_put_honest_on_success new_block (global_current_round (world_global_state w'))
                             (world_block_history w');
    world_chain_history := option_insert (world_chain_history w') new_chain;
    world_adversary_message_quota := world_adversary_message_quota w';
    world_adversary_transaction_quota := world_adversary_transaction_quota w';
    world_honest_transaction_quota := world_honest_transaction_quota w';
    world_adoption_history := record_actor_current_chain (honest_current_chain lclstt) new_chain
                                                         (global_current_round (world_global_state w')) addr (world_adoption_history w');

    world_message_trace := (world_message_trace w')
    |}).


Definition honest_mint_failed_no_update iscrpt addr lclstt os w gca := {|
    world_global_state := {|
                          global_local_states := set_tnth (global_local_states (world_global_state w))
                                                   ({|
                                                    honest_current_chain := honest_current_chain
                                                                              (update_transaction_pool addr lclstt
                                                                                 (world_transaction_pool w));
                                                    honest_local_transaction_pool := fixlist_empty Transaction
                                                                                      Honest_TransactionPool_size;
                                                    honest_local_message_pool := fixlist_empty
                                                                                   [eqType of BlockChain]
                                                                                   Honest_MessagePool_size |},
                                                   iscrpt) (global_currently_active (world_global_state w));
                          global_adversary := global_adversary (world_global_state w);
                          global_currently_active := gca;
                          global_current_round := global_current_round (world_global_state w )|};
    world_transaction_pool := world_transaction_pool w;
    world_inflight_pool := world_inflight_pool w;
    world_message_pool := world_message_pool w;
    world_hash := os;
    world_block_history := world_block_history w;
    world_chain_history := world_chain_history w;
    world_adversary_message_quota := world_adversary_message_quota w;
    world_adversary_transaction_quota := world_adversary_transaction_quota w;
    world_honest_transaction_quota := world_honest_transaction_quota w;
    world_adoption_history := fixlist_insert (world_adoption_history w)
                                             (honest_current_chain lclstt, global_current_round (world_global_state w), addr);
    world_message_trace := (world_message_trace w) |}.

Definition honest_mint_failed_update iscrpt addr lclstt os w gca := {|
    world_global_state := {|
                          global_local_states := set_tnth (global_local_states (world_global_state w))
                                                   ({|
                                                    honest_current_chain := honest_max_valid
                                                                              (update_transaction_pool addr lclstt
                                                                                 (world_transaction_pool w))
                                                                              (world_hash w);
                                                    honest_local_transaction_pool := fixlist_empty Transaction
                                                                                      Honest_TransactionPool_size;
                                                    honest_local_message_pool := fixlist_empty
                                                                                   [eqType of BlockChain]
                                                                                   Honest_MessagePool_size |},
                                                   iscrpt) (global_currently_active (world_global_state w));
                          global_adversary := global_adversary (world_global_state w);
                          global_currently_active := gca;
                          global_current_round := global_current_round (world_global_state w) |};
    world_transaction_pool := world_transaction_pool w;
    world_inflight_pool := fixlist_insert (world_inflight_pool w)
                             (BroadcastMsg
                                (honest_max_valid (update_transaction_pool addr lclstt (world_transaction_pool w))
                                   (world_hash w)));
    world_message_pool := world_message_pool w;
    world_hash := os;
    world_block_history := world_block_history w;
    world_chain_history := world_chain_history w;
    world_adversary_message_quota := world_adversary_message_quota w;
    world_adversary_transaction_quota := world_adversary_transaction_quota w;
    world_honest_transaction_quota := world_honest_transaction_quota w;
    world_adoption_history := fixlist_insert (world_adoption_history w)
                                             (honest_current_chain lclstt, global_current_round (world_global_state w), addr);
    world_message_trace := (world_message_trace w)|}.


Definition honest_mint_succeed_update iscrpt addr lclstt os blc_rcd hashed nonce gca w := (let
     '(updated_actor, new_message, new_oracle, new_block, new_chain) :=
      let
      '(new_chain, _) :=
       fixlist_enqueue (Some {| block_nonce := nonce; block_link := hashed; block_records := blc_rcd |})
         (honest_max_valid (update_transaction_pool addr lclstt (world_transaction_pool w)) (world_hash w)) in
       ({|
        honest_current_chain := new_chain;
        honest_local_transaction_pool := fixlist_empty Transaction Honest_TransactionPool_size;
        honest_local_message_pool := fixlist_empty [eqType of BlockChain] Honest_MessagePool_size |},
       Some (BroadcastMsg new_chain), os,
       Some {| block_nonce := nonce; block_link := hashed; block_records := blc_rcd |}, 
       Some new_chain) in
      {|
      world_global_state := {|
                            global_local_states := set_tnth (global_local_states (world_global_state w))
                                                     (updated_actor, iscrpt)
                                                     (global_currently_active (world_global_state w));
                            global_adversary := global_adversary (world_global_state w);
                            global_currently_active := gca;
                            global_current_round := global_current_round (world_global_state w) |};
      world_transaction_pool := world_transaction_pool w;
      world_inflight_pool := option_insert (world_inflight_pool w) new_message;
      world_message_pool := world_message_pool w;
      world_hash := new_oracle;
      world_block_history := BlockMap_put_honest_on_success new_block (global_current_round (world_global_state w))
                               (world_block_history w);
      world_chain_history := option_insert (world_chain_history w) new_chain;
      world_adversary_message_quota := world_adversary_message_quota w;
      world_adversary_transaction_quota := world_adversary_transaction_quota w;
      world_honest_transaction_quota := world_honest_transaction_quota w;
      world_adoption_history := record_actor_current_chain (honest_current_chain lclstt) new_chain
                                  (global_current_round (world_global_state w)) addr (world_adoption_history w);

    world_message_trace := (world_message_trace w)|}).




Definition transaction_gen_step w' tx  := {|
    world_global_state := world_global_state w';
    world_transaction_pool := fixlist_insert (world_transaction_pool w') (BroadcastTransaction tx);
    world_inflight_pool := world_inflight_pool w';
    world_message_pool := world_message_pool w';
    world_hash := world_hash w';
    world_block_history := world_block_history w';
    world_chain_history := world_chain_history w';
    world_adversary_message_quota := world_adversary_message_quota w';
    world_adversary_transaction_quota := world_adversary_transaction_quota w';
    world_honest_transaction_quota := mod_incr Honest_max_Transaction_sends valid_Honest_max_Transaction_sends
                                        (world_honest_transaction_quota w');
    world_adoption_history := world_adoption_history w';
    world_message_trace := (world_message_trace w')|}.


Definition transaction_drop_step w' rem_ind:= {|
    world_global_state := world_global_state w';
    world_transaction_pool := fixlist_remove (world_transaction_pool w') rem_ind;
    world_inflight_pool := world_inflight_pool w';
    world_message_pool := world_message_pool w';
    world_hash := world_hash w';
    world_block_history := world_block_history w';
    world_chain_history := world_chain_history w';
    world_adversary_message_quota := world_adversary_message_quota w';
    world_adversary_transaction_quota := world_adversary_transaction_quota w';
    world_honest_transaction_quota := world_honest_transaction_quota w';
    world_adoption_history := world_adoption_history w';
    world_message_trace := (world_message_trace w')|}.

Definition honest_mint_step iscrpt os hash_value hash_vl blc_rcd addr lclstt result w' :=
(let
     '(updated_actor, new_message, new_oracle, new_block, new_chain) :=
      if (result < T_Hashing_Difficulty)%nat
      then
       let
       '(new_chain, _) :=
        fixlist_enqueue (Some {| block_nonce := hash_value; block_link := hash_vl; block_records := blc_rcd |})
          (honest_max_valid (update_transaction_pool addr lclstt (world_transaction_pool w')) (world_hash w')) in
        ({|
         honest_current_chain := new_chain;
         honest_local_transaction_pool := fixlist_empty Transaction Honest_TransactionPool_size;
         honest_local_message_pool := fixlist_empty [eqType of BlockChain] Honest_MessagePool_size |},
        Some (BroadcastMsg new_chain), os,
        Some {| block_nonce := hash_value; block_link := hash_vl; block_records := blc_rcd |}, 
        Some new_chain)
      else
       if
        honest_max_valid (update_transaction_pool addr lclstt (world_transaction_pool w')) (world_hash w') ==
        honest_current_chain (update_transaction_pool addr lclstt (world_transaction_pool w'))
       then
        ({|
         honest_current_chain := honest_current_chain
                                   (update_transaction_pool addr lclstt (world_transaction_pool w'));
         honest_local_transaction_pool := fixlist_empty Transaction Honest_TransactionPool_size;
         honest_local_message_pool := fixlist_empty [eqType of BlockChain] Honest_MessagePool_size |}, None, os,
        None, None)
       else
        ({|
         honest_current_chain := honest_max_valid (update_transaction_pool addr lclstt (world_transaction_pool w'))
                                   (world_hash w');
         honest_local_transaction_pool := fixlist_empty Transaction Honest_TransactionPool_size;
         honest_local_message_pool := fixlist_empty [eqType of BlockChain] Honest_MessagePool_size |},
        Some
          (BroadcastMsg
             (honest_max_valid (update_transaction_pool addr lclstt (world_transaction_pool w')) (world_hash w'))),
        os, None, None) in
      {|
      world_global_state := (if eq_op (nat_of_ord (global_currently_active (world_global_state w'))) n_max_actors.+1 as b0
                              return
                                ((eq_op (nat_of_ord((global_currently_active (world_global_state w')))) n_max_actors.+1) = b0 ->
                                 GlobalState)
                             then
                              fun _ : (eq_op (nat_of_ord (global_currently_active (world_global_state w'))) n_max_actors.+1) = true
                              =>
                              {|
                              global_local_states := set_tnth (global_local_states (world_global_state w'))
                                                       (updated_actor, iscrpt)
                                                       (global_currently_active (world_global_state w'));
                              global_adversary := global_adversary (world_global_state w');
                              global_currently_active := global_currently_active (world_global_state w');
                              global_current_round := global_current_round (world_global_state w') |}
                             else
                              fun
                                prf : (eq_op (nat_of_ord(global_currently_active (world_global_state w'))) n_max_actors.+1) = false
                              =>
                              ssr_suff ((global_currently_active (world_global_state w')).+1 < n_max_actors + 2)%nat
                                (fun
                                   H' : ((global_currently_active (world_global_state w')).+1 < n_max_actors + 2)%nat
                                 =>
                                 {|
                                 global_local_states := set_tnth (global_local_states (world_global_state w'))
                                                          (updated_actor, iscrpt)
                                                          (global_currently_active (world_global_state w'));
                                 global_adversary := global_adversary (world_global_state w');
                                 global_currently_active := Ordinal (n:=n_max_actors + 2)
                                                              (m:=(global_currently_active (world_global_state w')).+1)
                                                              H';
                                 global_current_round := global_current_round (world_global_state w') |})
                                (round_in_range (global_currently_active (world_global_state w'))
                                   (introN eqP (elimTF eqP prf))))
                              (erefl (eq_op (nat_of_ord (global_currently_active (world_global_state w'))) n_max_actors.+1));
      world_transaction_pool := world_transaction_pool w';
      world_inflight_pool := option_insert (world_inflight_pool w') new_message;
      world_message_pool := world_message_pool w';
      world_hash := new_oracle;
      world_block_history := BlockMap_put_honest_on_success new_block
                               (global_current_round (world_global_state w')) (world_block_history w');
      world_chain_history := option_insert (world_chain_history w') new_chain;
      world_adversary_message_quota := world_adversary_message_quota w';
      world_adversary_transaction_quota := world_adversary_transaction_quota w';
      world_honest_transaction_quota := world_honest_transaction_quota w';
      world_adoption_history := record_actor_current_chain (honest_current_chain lclstt) new_chain
                                  (global_current_round (world_global_state w')) addr (world_adoption_history w'); 

    world_message_trace := (world_message_trace w')|}).


Definition update_adversary_state w':=
  finfun.FunFinfun.fun_of_fin
                 (finfun.FunFinfun.fun_of_fin
                    (adversary_generate_block
                       (update_adversary_transaction_pool (global_adversary (world_global_state w'))
                          (world_transaction_pool w')))
                    (adversary_state
                       (update_adversary_transaction_pool (global_adversary (world_global_state w'))
                          (world_transaction_pool w')))) (world_inflight_pool w').

Definition adversary_mint_player_step
                 (oracle_state : OracleState) (old_adv_state : adversary_internal_state)
                 (blc_rcd : BlockRecord) (nonce hash:  'I_Hash_value.+1) (hash_res: Hashed) w' :=
    (let
     '(new_adversary, new_oracle, new_block) :=
      if (hash_res < T_Hashing_Difficulty)%nat
      then
       ({|
        adversary_state := finfun.FunFinfun.fun_of_fin
                             (finfun.FunFinfun.fun_of_fin
                                (finfun.FunFinfun.fun_of_fin
                                   (adversary_provide_block_hash_result
                                      (update_adversary_transaction_pool (global_adversary (world_global_state w'))
                                         (world_transaction_pool w'))) old_adv_state) (nonce, hash, blc_rcd))
                             hash_res;
        adversary_state_change := adversary_state_change
                                    (update_adversary_transaction_pool (global_adversary (world_global_state w'))
                                       (world_transaction_pool w'));
        adversary_insert_transaction := adversary_insert_transaction
                                          (update_adversary_transaction_pool
                                             (global_adversary (world_global_state w'))
                                             (world_transaction_pool w'));
        adversary_insert_chain := adversary_insert_chain
                                    (update_adversary_transaction_pool (global_adversary (world_global_state w'))
                                       (world_transaction_pool w'));
        adversary_generate_block := adversary_generate_block
                                      (update_adversary_transaction_pool (global_adversary (world_global_state w'))
                                         (world_transaction_pool w'));
        adversary_provide_block_hash_result := adversary_provide_block_hash_result
                                                 (update_adversary_transaction_pool
                                                    (global_adversary (world_global_state w'))
                                                    (world_transaction_pool w'));
        adversary_send_chain := adversary_send_chain
                                  (update_adversary_transaction_pool (global_adversary (world_global_state w'))
                                     (world_transaction_pool w'));
        adversary_send_transaction := adversary_send_transaction
                                        (update_adversary_transaction_pool
                                           (global_adversary (world_global_state w')) (world_transaction_pool w'));
        adversary_last_hashed_round := adversary_last_hashed_round
                                         (update_adversary_transaction_pool
                                            (global_adversary (world_global_state w'))
                                            (world_transaction_pool w')) |}, oracle_state,
       Some {| block_nonce := nonce; block_link := hash; block_records := blc_rcd |})
      else
       ({|
        adversary_state := finfun.FunFinfun.fun_of_fin
                             (finfun.FunFinfun.fun_of_fin
                                (finfun.FunFinfun.fun_of_fin
                                   (adversary_provide_block_hash_result
                                      (update_adversary_transaction_pool (global_adversary (world_global_state w'))
                                         (world_transaction_pool w'))) old_adv_state) (nonce, hash, blc_rcd))
                             hash_res;
        adversary_state_change := adversary_state_change
                                    (update_adversary_transaction_pool (global_adversary (world_global_state w'))
                                       (world_transaction_pool w'));
        adversary_insert_transaction := adversary_insert_transaction
                                          (update_adversary_transaction_pool
                                             (global_adversary (world_global_state w'))
                                             (world_transaction_pool w'));
        adversary_insert_chain := adversary_insert_chain
                                    (update_adversary_transaction_pool (global_adversary (world_global_state w'))
                                       (world_transaction_pool w'));
        adversary_generate_block := adversary_generate_block
                                      (update_adversary_transaction_pool (global_adversary (world_global_state w'))
                                         (world_transaction_pool w'));
        adversary_provide_block_hash_result := adversary_provide_block_hash_result
                                                 (update_adversary_transaction_pool
                                                    (global_adversary (world_global_state w'))
                                                    (world_transaction_pool w'));
        adversary_send_chain := adversary_send_chain
                                  (update_adversary_transaction_pool (global_adversary (world_global_state w'))
                                     (world_transaction_pool w'));
        adversary_send_transaction := adversary_send_transaction
                                        (update_adversary_transaction_pool
                                           (global_adversary (world_global_state w')) (world_transaction_pool w'));
        adversary_last_hashed_round := adversary_last_hashed_round
                                         (update_adversary_transaction_pool
                                            (global_adversary (world_global_state w'))
                                            (world_transaction_pool w')) |}, oracle_state, None) in
      {|
      world_global_state := {|
                            global_local_states := global_local_states (world_global_state w');
                            global_adversary := if
                                                 isSome
                                                   (Addr_to_index (global_currently_active (world_global_state w')))
                                                then new_adversary
                                                else
                                                 update_adversary_round new_adversary
                                                   (global_current_round (world_global_state w'));
                            global_currently_active := global_currently_active (world_global_state w');
                            global_current_round := global_current_round (world_global_state w') |};
      world_transaction_pool := world_transaction_pool w';
      world_inflight_pool := world_inflight_pool w';
      world_message_pool := world_message_pool w';
      world_hash := new_oracle;
      world_block_history := BlockMap_put_adversarial_on_success new_block
                               (global_current_round (world_global_state w')) (world_block_history w');
      world_chain_history := world_chain_history w';
      world_adversary_message_quota := world_adversary_message_quota w';
      world_adversary_transaction_quota := world_adversary_transaction_quota w';
      world_honest_transaction_quota := world_honest_transaction_quota w';
      world_adoption_history := world_adoption_history w';
      world_message_trace := (world_message_trace w') |}).



Definition adversary_mint_global_step adv_state w' :=
  (let '(new_adversary, new_oracle, new_block) := adv_state in
      {|
      world_global_state := {|
                            global_local_states := global_local_states (world_global_state w');
                            global_adversary := new_adversary;
                            global_currently_active := global_currently_active (world_global_state w');
                            global_current_round := global_current_round (world_global_state w') |};
      world_transaction_pool := world_transaction_pool w';
      world_inflight_pool := world_inflight_pool w';
      world_message_pool := world_message_pool w';
      world_hash := new_oracle;
      world_block_history := BlockMap_put_adversarial_on_success new_block
                               (global_current_round (world_global_state w')) (world_block_history w');
      world_chain_history := world_chain_history w';
      world_adversary_message_quota := world_adversary_message_quota w';
      world_adversary_transaction_quota := world_adversary_transaction_quota w';
      world_honest_transaction_quota := world_honest_transaction_quota w';
      world_adoption_history := world_adoption_history w';
      world_message_trace := (world_message_trace w')
      |}).


Definition retrieve_address addr w' :=
  (if (addr < n_max_actors)%nat as b
         return ((addr < n_max_actors)%nat = b -> option ('I_n_max_actors * LocalState))
        then
         fun H : (addr < n_max_actors)%nat = true =>
         let (actor, is_corrupt) :=
           tnth (global_local_states (world_global_state w')) (Ordinal (n:=n_max_actors) (m:=addr) H) in
         (if is_corrupt as b return (is_corrupt = b -> option ('I_n_max_actors * LocalState))
          then fun _ : is_corrupt = true => None
          else fun _ : is_corrupt = false => Some (Ordinal (n:=n_max_actors) (m:=addr) H, actor))
           (erefl is_corrupt)
        else fun _ : (addr < n_max_actors)%nat = false => None) (erefl (addr < n_max_actors)%nat).


Definition adversary_corrupt_step  actr addr w' :=
{|
    world_global_state := {|
                          global_local_states := set_tnth (global_local_states (world_global_state w'))
                                                   (actr, true) addr;
                          global_adversary := global_adversary (world_global_state w');
                          global_currently_active := global_currently_active (world_global_state w');
                          global_current_round := global_current_round (world_global_state w') |};
    world_transaction_pool := world_transaction_pool w';
    world_inflight_pool := world_inflight_pool w';
    world_message_pool := world_message_pool w';
    world_hash := world_hash w';
    world_block_history := world_block_history w';
    world_chain_history := world_chain_history w';
    world_adversary_message_quota := world_adversary_message_quota w';
    world_adversary_transaction_quota := world_adversary_transaction_quota w';
    world_honest_transaction_quota := world_honest_transaction_quota w';
    world_adoption_history := world_adoption_history w';
      world_message_trace := (world_message_trace w') |}.


Definition broadcast_step nwadvst chain addrlist w' := {|
    world_global_state := {|
              global_local_states := global_local_states (world_global_state w');
              global_adversary := {|
                                  adversary_state := nwadvst;
                                  adversary_state_change := adversary_state_change
                                                              (global_adversary (world_global_state w'));
                                  adversary_insert_transaction := adversary_insert_transaction
                                                                    (global_adversary
                                                                        (world_global_state w'));
                                  adversary_insert_chain := adversary_insert_chain
                                                              (global_adversary (world_global_state w'));
                                  adversary_generate_block := adversary_generate_block
                                                                (global_adversary
                                                                    (world_global_state w'));
                                  adversary_provide_block_hash_result := adversary_provide_block_hash_result
                                                                          (global_adversary
                                                                          (world_global_state w'));
                                  adversary_send_chain := adversary_send_chain
                                                            (global_adversary (world_global_state w'));
                                  adversary_send_transaction := adversary_send_transaction
                                                                  (global_adversary
                                                                      (world_global_state w'));
                                  adversary_last_hashed_round := adversary_last_hashed_round
                                                                    (global_adversary
                                                                      (world_global_state w')) |};
              global_currently_active := global_currently_active (world_global_state w');
              global_current_round := global_current_round (world_global_state w') |};
    world_transaction_pool := world_transaction_pool w';
    world_inflight_pool := fixlist_insert (world_inflight_pool w') (MulticastMsg addrlist chain);
    world_message_pool := world_message_pool w';
    world_hash := world_hash w';
    world_block_history := world_block_history w';
    world_chain_history := world_chain_history w';
    world_adversary_message_quota := mod_incr Adversary_max_Message_sends valid_Adversary_max_Message_sends
                                       (world_adversary_message_quota w');
    world_adversary_transaction_quota := world_adversary_transaction_quota w';
    world_honest_transaction_quota := world_honest_transaction_quota w';
    world_adoption_history := world_adoption_history w';
      world_message_trace := (world_message_trace w') |}.

Definition adversary_transaction_step adv_state tx addrlist w' :=
{|
    world_global_state := {|
                          global_local_states := global_local_states (world_global_state w');
                          global_adversary := {|
                                              adversary_state := adv_state;
                                              adversary_state_change := adversary_state_change
                                                                          (global_adversary (world_global_state w'));
                                              adversary_insert_transaction := adversary_insert_transaction
                                                                                (global_adversary
                                                                                   (world_global_state w'));
                                              adversary_insert_chain := adversary_insert_chain
                                                                          (global_adversary (world_global_state w'));
                                              adversary_generate_block := adversary_generate_block
                                                                            (global_adversary
                                                                               (world_global_state w'));
                                              adversary_provide_block_hash_result := adversary_provide_block_hash_result
                                                                                      (global_adversary
                                                                                      (world_global_state w'));
                                              adversary_send_chain := adversary_send_chain
                                                                        (global_adversary (world_global_state w'));
                                              adversary_send_transaction := adversary_send_transaction
                                                                              (global_adversary
                                                                                 (world_global_state w'));
                                              adversary_last_hashed_round := adversary_last_hashed_round
                                                                               (global_adversary
                                                                                  (world_global_state w')) |};
                          global_currently_active := global_currently_active (world_global_state w');
                          global_current_round := global_current_round (world_global_state w') |};
    world_transaction_pool := fixlist_insert (world_transaction_pool w') (MulticastTransaction (tx, addrlist));
    world_inflight_pool := world_inflight_pool w';
    world_message_pool := world_message_pool w';
    world_hash := world_hash w';
    world_block_history := world_block_history w';
    world_chain_history := world_chain_history w';
    world_adversary_message_quota := world_adversary_message_quota w';
    world_adversary_transaction_quota := mod_incr Adversary_max_Transaction_sends
                                           valid_Adversary_max_Transaction_sends
                                           (world_adversary_transaction_quota w');
    world_honest_transaction_quota := world_honest_transaction_quota w';
    world_adoption_history := world_adoption_history w';
      world_message_trace := (world_message_trace w') |}.


Definition round_end_step msgs new_pool w' :=
{|
    world_global_state := deliver_messages msgs (next_round (world_global_state w'));
    world_transaction_pool := world_transaction_pool w';
    world_inflight_pool := initMessagePool;
    world_message_pool := new_pool;
    world_hash := world_hash w';
    world_block_history := world_block_history w';
    world_chain_history := world_chain_history w';
    world_adversary_message_quota := Ordinal (n:=Adversary_max_Message_sends) (m:=0)
                                       valid_Adversary_max_Message_sends;
    world_adversary_transaction_quota := Ordinal (n:=Adversary_max_Transaction_sends) (m:=0)
                                           valid_Adversary_max_Transaction_sends;
    world_honest_transaction_quota := Ordinal (n:=Honest_max_Transaction_sends) (m:=0)
                                        valid_Honest_max_Transaction_sends;
    world_adoption_history := world_adoption_history w' ;
    world_message_trace := (fixlist_insert (world_message_trace w') ((world_inflight_pool w'),  new_pool, msgs))
|}.


Definition adversary_end_step w' := {|
    world_global_state := update_round (world_global_state w');
    world_transaction_pool := world_transaction_pool w';
    world_inflight_pool := world_inflight_pool w';
    world_message_pool := world_message_pool w';
    world_hash := world_hash w';
    world_block_history := world_block_history w';
    world_chain_history := world_chain_history w';
    world_adversary_message_quota := world_adversary_message_quota w';
    world_adversary_transaction_quota := world_adversary_transaction_quota w';
    world_honest_transaction_quota := world_honest_transaction_quota w';
    world_adoption_history := world_adoption_history w' ;
    world_message_trace := (world_message_trace w') |}.

Lemma actor_has_chain_length_round_end w' l new_pool msgs o_addr : forall (prf: ([[w'.state].#round].+1 < N_rounds)%nat),
  actor_n_has_chain_length_ge_at_round w' l o_addr [[w'.state].#round] -> 
  actor_n_has_chain_length_ge_at_round (round_end_step msgs new_pool w') l o_addr
    (Ordinal prf).
Proof.
  move=> prf.
  rewrite /round_end_step !actor_n_has_chain_length_ge_at_round_internalP //=.
  rewrite /actor_n_has_chain_length_ge_at_round_internal//= => /orP [ | Hl0]; last first.
    by apply/orP; right.
    move=> /hasP [[[chain round ] addr] xin /andP [Hlen /andP [Hrnd Haddr]]];
    apply/orP; left; apply /hasP.
  exists (chain,round,addr) => //=.
  apply/andP; split=> //=;apply/andP; split=> //=.
  by move: Hrnd; rewrite -ltnS => /(ltn_addr 1); rewrite addn1 ltnS . 
Qed. 


