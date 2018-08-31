
(* Implementation of Bitcoin Protocol *)
(* Does not compile yet - as probability issues have not been resolved. *)



From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype fintype choice ssrfun seq path finfun.


From mathcomp.ssreflect
Require Import tuple.


From Probchain
Require Import BlockChain AddressList OracleState BlockMap InvMisc Parameters FixedList FixedMap.

Set Implicit Arguments.

Parameter adversary_internal_state : finType.
Parameter adversary_internal_initial_state : adversary_internal_state.
Parameter adversary_internal_state_change : {ffun adversary_internal_state -> adversary_internal_state}.
Parameter adversary_internal_insert_transaction: {ffun adversary_internal_state -> {ffun Transaction -> adversary_internal_state}}.
Parameter adversary_internal_insert_chain: {ffun adversary_internal_state -> {ffun BlockChain -> adversary_internal_state}}.
Parameter adversary_internal_generate_block: {ffun adversary_internal_state -> {ffun MessagePool -> (adversary_internal_state * (Nonce * Hashed * BlockRecord))}}.
Parameter adversary_internal_provide_block_hash_result: {ffun adversary_internal_state -> {ffun (Nonce * Hashed * BlockRecord) -> {ffun Hashed -> adversary_internal_state}}}.
Parameter adversary_internal_send_chain: {ffun adversary_internal_state -> (adversary_internal_state * BlockChain)}.
Parameter adversary_internal_send_transaction: {ffun adversary_internal_state -> (adversary_internal_state * Transaction * AddressList)}.



  
Definition verify_hash (blk : Block) (oracle : OracleState) : option Hashed := 
   oraclestate_find (block_nonce blk, block_link blk, block_records blk) oracle.

(*
  An adversary's state consists of
  1. Adversary's hidden state - can not be introspected
  2. Adversary's state change transition
  3. all transactions it has been delivered.
  4. All chains it has ever seen
  5. an extra parameter to persist proof of work calculations between rounds. 
  6. the last round it attempted a hash - it can only attempt hashing 
     if this value is less than the current round*)
   (* Inner adversary's state, whose type cannot be introspected *)
Record Adversary (T : finType) := mkAdvrs {

  adversary_state : T;
  adversary_state_change: {ffun T -> T}; (* Changing the state -- an operation provided by an adversary *) 
  adversary_insert_transaction: {ffun T -> {ffun Transaction -> T}};
  adversary_insert_chain: {ffun T -> {ffun BlockChain -> T}};

  (* Required to allow adversary limited queries to the oracle*)
  (* the adversary can propose a block to be hashed*)
  adversary_generate_block: {ffun T -> {ffun MessagePool -> (T * (Nonce * Hashed * BlockRecord))}};

  (* the result of the hash is returned to the adversary through this method - is the block necassary? *)
  (* it has to be structured this way, as we can not allow the adversary access to the oracle directly*)
  adversary_provide_block_hash_result: {ffun T -> {ffun (Nonce * Hashed * BlockRecord) -> {ffun Hashed -> T}}};

  (* Required to allow the adversary to broadcast chains *)
  (* I'm not sure how assertions about the blockchain being unable to randomly guess valid blockchains will be made*)
  adversary_send_chain: {ffun T -> (T * BlockChain)};
  adversary_send_transaction: {ffun T -> (T * Transaction * AddressList)};

  (* adversary_local_transaction_pool: seq Transaction; *)
  (* adversary_local_message_pool: seq BlockChain; *)

  (* Additional info *)
  adversary_last_hashed_round: ordinal N_rounds;
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
    (Ordinal valid_N_rounds).

Definition Adversary_prod  (a : Adversary adversary_internal_state) :=
  (adversary_state a,
  adversary_state_change a,
  adversary_insert_transaction  a,
  adversary_insert_chain  a,
  adversary_generate_block  a,
  adversary_provide_block_hash_result  a,
  adversary_send_chain a,
  adversary_send_transaction a,
  adversary_last_hashed_round a).


Definition prod_Adversary (pair : 
  (adversary_internal_state  * 
  {ffun adversary_internal_state  -> adversary_internal_state } * 
  {ffun adversary_internal_state  -> {ffun Transaction -> adversary_internal_state }} * 
  {ffun adversary_internal_state  -> {ffun BlockChain -> adversary_internal_state }} * 
  {ffun adversary_internal_state  -> {ffun MessagePool -> adversary_internal_state  * (Nonce * Hashed * BlockRecord)}} * 
  {ffun adversary_internal_state  -> {ffun Nonce * Hashed * BlockRecord -> {ffun Hashed -> adversary_internal_state }}} * 
  {ffun adversary_internal_state  -> adversary_internal_state  * BlockChain} * 
  {ffun adversary_internal_state   -> (adversary_internal_state   * Transaction * AddressList)} * 
  ordinal N_rounds
  )) := 
  let: (adversary_state ,
    adversary_state_change ,
    adversary_insert_transaction  ,
    adversary_insert_chain  ,
    adversary_generate_block  ,
    adversary_provide_block_hash_result  ,
    adversary_send_chain ,
    adversary_send_transaction ,
    adversary_last_hashed_round) := pair in
    mkAdvrs 
      adversary_state 
      adversary_state_change 
      adversary_insert_transaction  
      adversary_insert_chain  
      adversary_generate_block  
      adversary_provide_block_hash_result  
      adversary_send_chain 
      adversary_send_transaction 
      adversary_last_hashed_round.



Lemma adversary_cancel : cancel Adversary_prod prod_Adversary .
Proof.
  by case.
Qed.

Definition adversary_eqMixin :=
  CanEqMixin adversary_cancel.
Canonical adversary_eqType :=
  Eval hnf in EqType (Adversary adversary_internal_state) adversary_eqMixin.

Definition adversary_choiceMixin :=
  CanChoiceMixin adversary_cancel.
Canonical adversary_choiceType :=
  Eval hnf in ChoiceType (Adversary adversary_internal_state) adversary_choiceMixin.

Definition adversary_countMixin :=
  CanCountMixin adversary_cancel.
Canonical adversary_countType :=
  Eval hnf in CountType (Adversary adversary_internal_state) adversary_countMixin.
Definition adversary_finMixin :=
  CanFinMixin adversary_cancel.
Canonical adversary_finType :=
  Eval hnf in FinType (Adversary adversary_internal_state) adversary_finMixin.


Canonical adversary_of_eqType := Eval hnf in [eqType of (Adversary adversary_internal_state)].
Canonical adversary_of_choiceType := Eval hnf in [choiceType of (Adversary adversary_internal_state)].
Canonical adversary_of_countType := Eval hnf in [countType of (Adversary adversary_internal_state)].
Canonical adversary_of_finType := Eval hnf in [finType of (Adversary adversary_internal_state)].




Definition local_TransactionPool := fixlist Transaction Honest_TransactionPool_size.




(* A node's local state consists of 
    1. it's currently held chain
    2. all transactions it has been delivered 
    3. all chains that it has been sent since it's last activation
    4. an extra parameter to persist proof of work calculations between rounds. *)
Record LocalState := mkLclSt {
  honest_current_chain: BlockChain;
  honest_local_transaction_pool: local_TransactionPool; honest_local_message_pool: fixlist [eqType of BlockChain] Honest_MessagePool_size ;
}.

Definition initLocalState := mkLclSt initBlockChain (fixlist_empty Transaction Honest_TransactionPool_size) (fixlist_empty [eqType of BlockChain] Honest_MessagePool_size) .

Definition LocalState_prod (ls : LocalState) :=
  (honest_current_chain ls,
  honest_local_transaction_pool ls,
  honest_local_message_pool ls).

Definition prod_LocalState pair :=
  let: (honest_current_chain,
  honest_local_transaction_pool,
  honest_local_message_pool) := pair in 
  mkLclSt
    honest_current_chain
    honest_local_transaction_pool
    honest_local_message_pool.

    
Lemma localstate_cancel : cancel LocalState_prod prod_LocalState .
Proof.
  by case.
Qed.

Definition localstate_eqMixin :=
  CanEqMixin localstate_cancel.
Canonical localstate_eqType :=
  Eval hnf in EqType (LocalState) localstate_eqMixin.

Definition localstate_choiceMixin :=
  CanChoiceMixin localstate_cancel.
Canonical localstate_choiceType :=
  Eval hnf in ChoiceType (LocalState) localstate_choiceMixin.

Definition localstate_countMixin :=
  CanCountMixin localstate_cancel.
Canonical localstate_countType :=
  Eval hnf in CountType (LocalState) localstate_countMixin.
Definition localstate_finMixin :=
  CanFinMixin localstate_cancel.
Canonical localstate_finType :=
  Eval hnf in FinType (LocalState) localstate_finMixin.


Canonical local_state_of_eqType := Eval hnf in [eqType of LocalState].
Canonical local_state_of_choiceType := Eval hnf in [choiceType of LocalState].
Canonical local_state_of_countType := Eval hnf in [countType of LocalState].
Canonical local_state_of_finType := Eval hnf in [finType of LocalState].



(* GlobalState consists of 
      1. A sequence of LocalStates, and a boolean representing whether the state is corrupted
      2. An address representing the currently executing entity - when addr == length of local states + 1,
         the round is complete
      3. A number representing the current round
*)
Record GlobalState := mkGlobalState {
  global_local_states: n_max_actors.-tuple [eqType of ([eqType of LocalState] * [eqType of bool])]  ;
  global_adversary: Adversary adversary_internal_state ;
  global_currently_active: Addr;
  global_current_round: (ordinal N_rounds);
}.

Definition initLocalStates := 
        Tuple 
          (size_ncons_nil (initLocalState, false) n_max_actors ).



Definition initGlobalState : GlobalState := mkGlobalState
  initLocalStates
  initAdversary
  (Ordinal (ltn_addr _ valid_n_max_actors))
  (Ordinal valid_N_rounds).

Definition GlobalState_prod (g : GlobalState) :=
  (global_local_states g,
  global_adversary g,
  global_currently_active g,
  global_current_round g).


Definition prod_GlobalState pair :=
  let: ( local_states, adversary, 
        currently_active, current_round) := pair in
        mkGlobalState
          local_states
          adversary
          currently_active
          current_round.
        

Lemma globalstate_cancel : cancel GlobalState_prod prod_GlobalState .
Proof.
  by case.
Qed.

Definition globalstate_eqMixin :=
  CanEqMixin globalstate_cancel.
Canonical globalstate_eqType :=
  Eval hnf in EqType (GlobalState) globalstate_eqMixin.

Definition globalstate_choiceMixin :=
  CanChoiceMixin globalstate_cancel.
Canonical globalstate_choiceType :=
  Eval hnf in ChoiceType (GlobalState) globalstate_choiceMixin.

Definition globalstate_countMixin :=
  CanCountMixin globalstate_cancel.
Canonical globalstate_countType :=
  Eval hnf in CountType (GlobalState) globalstate_countMixin.
Definition globalstate_finMixin :=
  CanFinMixin globalstate_cancel.
Canonical globalstate_finType :=
  Eval hnf in FinType (GlobalState) globalstate_finMixin.


Canonical global_state_of_eqType := Eval hnf in [eqType of GlobalState].
Canonical global_state_of_choiceType := Eval hnf in [choiceType of GlobalState].
Canonical global_state_of_countType := Eval hnf in [countType of GlobalState].
Canonical global_state_of_finType := Eval hnf in [finType of GlobalState].




Record World := mkWorld {
  world_global_state: GlobalState; 
  (* the transaction pools contains all sent transactions *)
  world_transaction_pool: TransactionPool; 
  (* the inflight pool contains all messages sent in the round *)
  world_inflight_pool: MessagePool;
  (* the world message pool is a queue of messages sent in the past round - once
  the length exceeds delta, the last entry is removed, and all messages delivered *)
  (* thus this achieves the simulation of a delta delay *)
  world_message_pool: fixlist [eqType of MessagePool] delta;
  (* represents the shared oracle state *)
  world_hash: OracleState;
  (* Contains every block seen *)
  world_block_history: BlockMap;
  (* Contains every chain ever seen *)
  world_chain_history: fixlist [eqType of BlockChain ] ChainHistory_size;
  (* Contains the number of messages sent by the adversary for the current round *)
  world_adversary_message_quota: (ordinal Adversary_max_Message_sends);
  (* Contains the number of transactions sent by the adversary for the current round *)
  world_adversary_transaction_quota: (ordinal Adversary_max_Transaction_sends);
  (* Contains the number of transactions sent by honest players *)
  world_honest_transaction_quota: (ordinal Honest_max_Transaction_sends);

  (* Contains a listing of the held chain at each round for each actor *)
  world_adoption_history: fixlist [eqType of (BlockChain * ordinal N_rounds * 'I_n_max_actors)] (n_max_actors * N_rounds);
}.



Definition initWorldMessagePool := (fixlist_empty [eqType of MessagePool] delta).
Definition initWorldChainHistory := (fixlist_empty [eqType of BlockChain] ChainHistory_size).
Definition initWorldAdoptionHistory := (fixlist_empty [eqType of (BlockChain * ordinal N_rounds * 'I_n_max_actors)] (n_max_actors * N_rounds)).

Definition initWorld := 
    mkWorld   
      initGlobalState 
      initTransactionPool 
      initMessagePool  
      initWorldMessagePool 
      oraclestate_new 
      BlockMap_new 
      initWorldChainHistory
       (Ordinal valid_Adversary_max_Message_sends)
       (Ordinal valid_Adversary_max_Transaction_sends)
       (Ordinal valid_Honest_max_Transaction_sends)
       initWorldAdoptionHistory.

Definition World_prod w :=
  (world_global_state w,
  world_transaction_pool w,
  world_inflight_pool w,
  world_message_pool w,
  world_hash w,
  world_block_history w,
  world_chain_history w,
  world_adversary_message_quota w,
  world_adversary_transaction_quota w,
  world_honest_transaction_quota w,
  world_adoption_history w).


Definition prod_World pair :=
  let: (world_global_state,
  world_transaction_pool,
  world_inflight_pool,
  world_message_pool,
  world_hash,
  world_block_history,
  world_chain_history,
  world_adversary_message_quota,
  world_adversary_transaction_quota,
  world_honest_transaction_quota,
  world_adoption_history) := pair in
    mkWorld
      world_global_state
      world_transaction_pool
      world_inflight_pool
      world_message_pool
      world_hash
      world_block_history
      world_chain_history
      world_adversary_message_quota
      world_adversary_transaction_quota
      world_honest_transaction_quota
      world_adoption_history.



Lemma world_cancel : cancel World_prod prod_World .
Proof.
  by case.
Qed.

Definition world_eqMixin :=
  CanEqMixin world_cancel.
Canonical world_eqType :=
  Eval hnf in EqType (World) world_eqMixin.

Definition world_choiceMixin :=
  CanChoiceMixin world_cancel.
Canonical world_choiceType :=
  Eval hnf in ChoiceType (World) world_choiceMixin.

Definition world_countMixin :=
  CanCountMixin world_cancel.
Canonical world_countType :=
  Eval hnf in CountType (World) world_countMixin.
Definition world_finMixin :=
  CanFinMixin world_cancel.
Canonical world_finType :=
  Eval hnf in FinType (World) world_finMixin.


Canonical world_of_eqType := Eval hnf in [eqType of World].
Canonical world_of_choiceType := Eval hnf in [choiceType of World].
Canonical world_of_countType := Eval hnf in [countType of World].
Canonical world_of_finType := Eval hnf in [finType of World].




(* A round is complete if the currently_active index is one greater than the length of the actors array *)
Definition round_ended (w: World) :=
 nat_of_ord (global_currently_active (world_global_state w)) == n_max_actors + 1. 

Definition world_current_addr (w : World) :=
  global_currently_active (world_global_state w).

Definition world_adversary (w : World) :=
  global_adversary (world_global_state w).

Definition world_actors (w : World) :=
  global_local_states (world_global_state w).

Definition world_round_no (w : World) :=
  nat_of_ord (global_current_round (world_global_state w)).

Definition no_corrupted_players (state: GlobalState) :=
    let: actors := global_local_states state in 
      length (filter (fun actor => actor.2) actors).



(* A given world step is an honest activation if the current address
   is to a node which has not been corrupted *)
Definition honest_activation (state: GlobalState) : option 'I_n_max_actors :=
    match state with
    | {|
      global_local_states := actors;
      global_currently_active := active
    |} =>
        (* if the index is valid *)
        (if (active < n_max_actors)%N as b return ((active < n_max_actors)%N = b -> option 'I_n_max_actors)
          then
            fun H : (active < n_max_actors)%N = true =>
              (* if the actor is corrupted *)
              if 
                (tnth actors (Ordinal (n:=n_max_actors) (m:=active) H)).2
              (* it is not an honest activation *)
              then None
              (* otherwise return an index into the list *)
              else Some (Ordinal (n:=n_max_actors) (m:=active) H)
        (* if the index is invalid, return None as well *)
        else fun _ : (active < n_max_actors)%N = false => None) (erefl (active < n_max_actors)%N)
    end. 



(* A given world step is an adversarial activation if the current address
   is to a node which has been corrupted, or the current address is equal to
   the length of the list 
   this is based on the fact that the bitcoin paper states that in the round
   robin scheduling, once all nodes have activated, the adversary activates *)
Lemma adversary_activation (state: GlobalState): bool.
    case state => actors _ active _.
    case (active < n_max_actors) eqn: H.
      case (tnth actors (Ordinal H)) => _ is_corrupted.
      exact is_corrupted.
    case (n_max_actors == active) eqn: H'.
      exact true.
    exact false.
Defined. 


Lemma round_in_range (active: Addr) : nat_of_ord active != n_max_actors.+1 -> active.+1 < n_max_actors + 2.
Proof.
  move=> H.
  case active eqn: Haddr.
  rewrite neq_ltn in H.
  move: H => /orP H.
  case H => [Hlt | Hgt].
  rewrite -ltnS in Hlt.
  rewrite -(addn1 n_max_actors) in Hlt.
  by rewrite -(addn1 (n_max_actors + _)) -addnA in Hlt.

  rewrite -ltnS in Hgt.
  inversion Hgt.
  rewrite -(addn1 m) in H1.
  rewrite -addn2 in H1.
  suff Hn a b : a < b -> b < a + 1 -> False.
  move: (Hn _ _ i H1) => //=.
  clear active m i Haddr H Hgt H1.
  move=> Ha_ltb Hb_lta.
  rewrite addnS addn0 ltnS in Hb_lta.
  move: (leq_ltn_trans Hb_lta Ha_ltb) => H.
  by rewrite ltnn in H.
Qed.

(* Implements the round robin - each actor activated once a round mechanism 
   Once the last actor, and then the adversary has activated, the function does
   not do anything else *)
About ssr_suff.
Locate "[ eta _ ]".

Definition update_round (state : GlobalState) : GlobalState :=
  (* 
    the following should be equivalent to this
    definition below:

    (most of the work comes from proving that, 
    if nat_of_ord active != n_max_actors + 1
    then active.+1 is in ordinal (n_max_actors + 2))

  let: actors := global_local_states state in 
  let: active := global_currently_active state in
  let: adversary := global_adversary state in
  let: round := global_current_round state in
  if ((nat_of_ord active) == (fixlist_length actors).+1) 
  then state
  else mkGlobalState actors adversary active.+1 round. *)

match state with
| {| global_local_states := actors; global_adversary := adversary; global_currently_active :=
  active; global_current_round := round |} =>
    let b := nat_of_ord active == n_max_actors.+1 in
    let H : (nat_of_ord active == n_max_actors.+1) = b := erefl b in
    (if b as b0 return ((nat_of_ord active == n_max_actors.+1) = b0 -> GlobalState)
     then fun prf : (nat_of_ord active == n_max_actors.+1) = true => state
     else fun prf : (nat_of_ord active == n_max_actors.+1) = false =>
           (fun H1 : nat_of_ord active != n_max_actors.+1 =>
            ssr_suff (active.+1 < n_max_actors + 2)
              (fun H' : active.+1 < n_max_actors + 2 =>
                {|
                    global_local_states := actors;
                    global_adversary := adversary;
                    global_currently_active := Ordinal (n:=n_max_actors + 2) (m:=active.+1) H';
                    global_current_round := round
                |}
              ) (round_in_range active H1)
           ) (introN eqP (elimTF eqP prf))) H
end .

Print update_round.

Definition next_round  (state : GlobalState) : GlobalState .
  (* 
    Once again: here is the definition of the function,
    := let: ((actors, adversary), active, round) := state in 
      if (eqn active n_max_actors.+1) 
      then ((actors, adversary), 0, round.+1)
      else state. *)
      case state => actors adversary active round.
      case ((nat_of_ord active) == (n_max_actors).+1)  eqn:H.
        (* we can only update if the current round is less than the maximum rounds*)
        case ((global_current_round state).+1 < N_rounds) eqn: Hact.
          exact (mkGlobalState actors adversary (Ordinal (ltn_addr _ valid_n_max_actors)) (Ordinal Hact)).
        (* if it isn't less than the maximum rounds, just return the state *)
        exact (state).
      (* if next round is called on a state, that has not finished execution, it does nothing*)
      exact (state).
Defined.



(* insert the corresponding message into the recipient's message pool *)
Definition insert_message 
  (addr: 'I_n_max_actors) 
  (bc: BlockChain) 
  (state: GlobalState) : GlobalState := 
    let: actors := global_local_states state in
    let: adversary := global_adversary state in
    let: active := global_currently_active state in
    let: round := global_current_round state in
    let: default := (initLocalState, false) in
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
      (mkGlobalState actors new_adversary active round)
  else
    let: current_chain := honest_current_chain actor in
    let: local_transaction_pool := honest_local_transaction_pool actor in
    (* Check whether the blockchain is already in the pool *)
    let: message_pool := (honest_local_message_pool actor) in
    if fixlist_contains bc message_pool then
      state
    else
      let: new_message_pool := fixlist_insert message_pool bc in
      let: new_actor := mkLclSt current_chain local_transaction_pool new_message_pool in
      let: new_actors := set_tnth actors (new_actor, corrupted) addr in
      (mkGlobalState new_actors adversary active round)
  .


Definition insert_multicast_message 
  (addresses: AddressList) 
  (bc: BlockChain) 
  (initial_state: GlobalState) : GlobalState := 
      foldr
        (fun addr state => insert_message addr bc state)
        initial_state
        (AddressList_unwrap addresses).
 

        About foldr.

(* insert the corresponding message into every actor's message pool *)
Definition broadcast_message (bc : BlockChain) (initial_state: GlobalState) : GlobalState :=
  foldr
    (fun index state => 
      let: actors := global_local_states state in
      let: adversary := global_adversary state in
      let: active := global_currently_active state in
      let: round := global_current_round state in
      let: (actor, is_corrupt) := (tnth actors index) in
      if is_corrupt then
        state
      else
        insert_message index bc state)
    initial_state
    (ord_enum  n_max_actors).
    



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


Definition update_message_pool_queue (message_list_queue: fixlist [eqType of MessagePool] delta) (new_message_list : MessagePool) : (seq Message * (fixlist [eqType of MessagePool] delta)) :=
  let: (new_message_list, oldest_message_list) := @fixlist_enqueue _ _ (Some new_message_list) message_list_queue in
  match oldest_message_list with
    | None => ([::], new_message_list)
    | Some message_list => (fixlist_unwrap message_list, new_message_list)
  end.


Definition update_adversary_round (adversary : Adversary adversary_internal_state) (round : 'I_N_rounds) : Adversary adversary_internal_state :=
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




    

Definition validate_blockchain_links (bc : BlockChain) (oracle_state : OracleState) : bool :=
  match fixlist_unwrap bc with
    | [::] => true (* Vacuously true *)
    | h :: t =>
        let: (_, result) := 
        foldr
          (fun pred_block last_pair  => 
            let: (block, has_failed) := last_pair in
            (* if the foldr has alreday seen a failure*)
            if has_failed
              (* then just propagate the accumulator, no changes needed*)
              then (pred_block, has_failed)
              else
              (* otherwise, check that the link of the current block is equal to
                that of the current_blocks hash *)
                match verify_hash pred_block oracle_state with
                  | None => (pred_block, true)
                  | Some(hash_value) => 
                      if (block_link block == hash_value)  && (hash_value < T_Hashing_Difficulty) 
                        then (pred_block, false)
                        else (pred_block, true)
                end
          )
          (h, false)  
          t
          in 
          ~~ result
  end.

Definition validate_blockchain (bc : BlockChain) (oracle_state: OracleState) : bool :=
  (* a blockchain is valid if the links are well formed *)
  validate_blockchain_links bc oracle_state && 
  (* and all transactions are valid *)
  validate_transactions (BlockChain_unwrap bc).
  
(* finds the longest valid chain for a node *)
Definition honest_max_valid (state: LocalState) (oracle_state: OracleState) : BlockChain :=
  foldr 
  (fun (new_chain best_chain : BlockChain) => 
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
  (fixlist_unwrap (honest_local_message_pool state)).


(* Bitcoin Backbone Paper - Pg.29
  Parses v as a sequence of transactions and returns the largest subsequence that is valid
  with respect to the chain, and whoose transactions are not included in xc

  the following function, when given an honest node's transaction pool and chain, 
  may return a blockrecord (list containing x < MAX_BLOCK_LENGTH) and the transaction pool with
  the corresponding values removed
*)
Definition find_maximal_valid_subset  (transactions : local_TransactionPool) (blk: BlockChain) : (BlockRecord * local_TransactionPool) :=
(* naive approach - iterate through transactions and only include those that are valid 
   specifically it's naive because it assumes that all transactions are delivered in order
    (i.e if invalid, reordering the sequence won't change whether it's valid or not)
   but I believe this is a correct assumption as transactions are delivered immediately *)
   let chain_transactions := BlockChain_unwrap blk in
   foldr
      (fun index prev_pair => 
            let: (already_included, remaining) := prev_pair in
            let: o_transaction := fixlist_get_nth remaining index in
            if fixlist_length already_included == Transactions_per_block 
              (* if the block record is full, just skip to the end*)
              then (already_included, remaining) 
              (* if it isn't full, *)
              else match o_transaction with
                | None =>  (already_included, remaining)
                (* and the nth field is present*)
                | Some transaction =>
                  if Transaction_valid transaction ((fixlist_unwrap already_included) ++ chain_transactions)
                    (* and the transaction is valid*)
                    (* insert it into the blockrecord *)
                    then (fixlist_insert already_included transaction, fixlist_remove remaining index )
                    (* otherwise don't*)
                    else (already_included, remaining)
                end)
      (initBlockRecord, transactions)
      (iota 0 TransactionPool_length).


Definition retrieve_head_link (b : BlockChain) (oracle_state : OracleState) : option Hashed :=
  match fixlist_unwrap b with
    | [::] => Some (Ordinal (ltn0Sn _))
    | h :: t => verify_hash h oracle_state
  end.


    

Definition update_transaction_pool (addr : 'I_n_max_actors) (initial_state : LocalState) (transaction_pool: TransactionPool) : LocalState :=
  foldr
  (fun (txMsg : TransactionMessage) state => 
      match txMsg with
        | BroadcastTransaction tx => 
             if tx \in fixlist_unwrap (honest_local_transaction_pool state) 
              then state
              else 
                mkLclSt 
                  (honest_current_chain state)
                  (fixlist_insert (honest_local_transaction_pool state) tx)
                  (honest_local_message_pool state)
        | MulticastTransaction (tx, recipients) =>
          if addr \in (AddressList_unwrap recipients)
            then if tx \in fixlist_unwrap (honest_local_transaction_pool state) 
              then state
              else 
                mkLclSt 
                  (honest_current_chain state)
                  (fixlist_insert (honest_local_transaction_pool state) tx)
                  (honest_local_message_pool state)
            else state
      end)
  initial_state
  (fixlist_unwrap transaction_pool).

Definition update_adversary_transaction_pool  (initial_adv: Adversary adversary_internal_state) (transaction_pool: TransactionPool) : Adversary adversary_internal_state:=
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
      (fixlist_unwrap transaction_pool).



(* Implementation of the bitcoin backbone protocol *)




(* Fixpoint reachable_internal (w w' : World) (schedule : seq RndGen) : Prop :=
  match schedule with
    | [::] => w = w'
    | h :: t' => exists (y : World), world_step w y h /\ reachable_internal y w' t'
    end.

(* Clone of function from toychain *)
Definition reachable (w w' : World) : Prop :=
  exists (schedule : seq RndGen), reachable_internal w w' schedule.
 *)
Definition adversarial_minority (w : World) :=
  no_corrupted_players (world_global_state w) <= t_max_corrupted.
 

Lemma nth_set_nth_ident (A : Type) (P : pred A) (ls : seq A) (a a' : A) (n : nat) :
  ~~ P a -> ~~ P (nth a ls n) -> ~~ P a' -> length (filter P (set_nth a ls n a')) = length (filter P ls).
Proof.
  elim: ls n => [n H0 H1 H2| a'' ls n n'] //=.
  rewrite /filter.

  case n => [//=|n0//=]; rewrite ifN.
    by [].
    by [].

  by induction n0 => //=; rewrite ifN.
    by [].

  induction n' => //= H0 H1 H2.
  by rewrite ifN; [rewrite ifN| by []] .
  case_eq (P a'') => H //=.
  by rewrite n.
  by rewrite n.
Qed.

Lemma nth_set_nth_ident_general (A : Type) (P : pred A) (ls : seq A) (a a' : A) (n : nat) :
    n < length ls ->
    P (nth a ls n) == P a' -> 
      length (filter P (set_nth a ls n a')) = length (filter P ls).
Proof.
 
  elim: ls n => [n H0 | a'' ls n n'] //=.

  move=> H0 /eqP H.
  case_eq (P a'') =>  //=.
  move: H H0.
  case_eq n' => //=.
  move=> n0 H H1 H2.
  rewrite ifT.
    by [].
    by rewrite -H H2.
    move=> n0 n0eq H H1 H2.
    rewrite ifT.
    rewrite -(n n0) => //=.
      by rewrite H.
      by [].
  move=> H1.
  move: H.
  case_eq n' => //=.
  move=> H2 H.
  rewrite ifF.
    by [].
    by rewrite -H.
  move=> n0 H2 H.
  rewrite ifN.
  rewrite n => //=.
  by rewrite H2 in H0.
  by rewrite H.
  by rewrite H1.
Qed.

Lemma nth_set_nth_incr (A : Type) (P : pred A) (ls : seq A) (a a' : A) (n : nat) :
    n < length ls ->
    P a' ->
    ~~ P (nth a ls n)  -> 
      length (filter P (set_nth a ls n a')) = (length (filter P ls)).+1.
Proof.
  elim: ls n => [n H0 | a'' ls H n' ltnN Pa nPcons] //=.
  move: nPcons.
  case_eq n' => //= n0.
  move=> H1.
  rewrite ifT .
  by rewrite ifN. 
  by [].
  move=> n_eq.
  move=> H1.
  case_eq (P a'') => //= Pa''.
  rewrite H.
  by [].
  rewrite n_eq in ltnN.
  move: ltnN => //=.
  by [].
  by [].
  rewrite H.
  by [].
  rewrite n_eq in ltnN.
  move: ltnN => //=.
  by [].
  by [].
Qed.
(* 
Lemma maintain_corrupt_insert_message (state : GlobalState) (a : Addr) (bc : BlockChain) :
  no_corrupted_players (insert_message a bc state) = no_corrupted_players state.
Proof.
  rewrite /insert_message /no_corrupted_players.
  destruct state => //=.
  destruct p.
  destruct p.
  
  destruct (nth _)  as [actor corrupted]   eqn:H'. 
  
  case_eq  corrupted => //=.
  destruct (_ \in _) => //=.
  move=>H.
  rewrite nth_set_nth_ident.
    by [].
    by [].
    by rewrite H' H.
  by [].
Qed. *)

Lemma foldr_rec (A B : Type) (P : B -> Set) (f : A -> B -> B)  (b0 : B) (ls : seq A) :
  P b0 -> (forall a b, P b -> P (f a b)) -> P (foldr f b0 ls).
Proof.
  move=> P_b0 IHn.
  induction ls => [//|//=].
  by apply IHn.
Qed.


(* Lemma maintain_corrupt_deliver_messages (w : World) (l : seq Message) :
      no_corrupted_players (deliver_messages l (next_round (world_global_state w))) = no_corrupted_players (world_global_state w).
Proof.
  elim w => //= state _ _ _ _ _ _.
  rewrite /next_round.
  destruct state;  do 2 destruct p => //=.
  rewrite /deliver_messages. 
  apply  foldr_rec.
  case (eqn _ _) => //=.
  move=> msg state H1.
  destruct msg.
  rewrite /insert_multicast_message .
  apply foldr_rec.
    by [].
    move=> a_1 state_0 H2.
    by rewrite maintain_corrupt_insert_message.
    by rewrite /broadcast_message.
Qed.



(* Trivial lemma to ensure that steps work *)
Lemma adversarial_minority_induction  (w w' : World) (q : RndGen) :
   world_step w w' q -> adversarial_minority w -> adversarial_minority w'.
Proof.

  (* TODO(kiran): Complete this proof*)
  move=> S.
  rewrite /adversarial_minority .

  destruct S.
    - destruct (update_message_pool_queue _ _) => H1.
      rewrite H0 => //=.
      suff H2: no_corrupted_players (deliver_messages l (next_round (world_global_state w))) = no_corrupted_players (world_global_state w).
      by rewrite H2.
      by rewrite maintain_corrupt_deliver_messages. 

    - rewrite H1 =>//=.

    - rewrite H3 => //=.
      move: H1 H0.
      destruct w => //=.
      destruct world_global_state0.
      destruct p => //=.
      destruct p => //=.
      destruct (nth _) as [dated_actor corrupt] eqn:H'.
      destruct (retrieve_head_link _).
      destruct (find_maximal_valid_subset) .
      destruct (hash _) .
      case (_ < _).
      case (eqn _ _).
      move=> H1 H2.
      rewrite H1 => //=.
      destruct H2.
      rewrite nth_set_nth_ident => //=.
        by rewrite H'.
        case (honest_max_valid _).
        move=>  -> //=.
        move=> [ltlen not_corrupt].
        rewrite nth_set_nth_ident => //=.
        by rewrite H'.
        move=> new_bl blocks w'_def [ltlen not_corrupt] //=.
        rewrite w'_def => //=.
        rewrite nth_set_nth_ident => //=.
          by rewrite H'.
          move=> w'_def [ltlne not_corrupt].
          move: w'_def.
          destruct (_ == _).
          destruct (eqn _ _) => -> //=.
          rewrite nth_set_nth_ident => //=.
          by rewrite H'.
          rewrite nth_set_nth_ident => //=.
          by rewrite H'.
          destruct (eqn _ _) => -> //=.
          rewrite nth_set_nth_ident => //=.
          by rewrite H'.
          rewrite nth_set_nth_ident => //=.
          by rewrite H'.
          move=> w'_defn [ltlen not_corrupt].
          move: w'_defn.
          destruct (_ == _).
          destruct (eqn _ _) =>  -> //=.
          rewrite nth_set_nth_ident => //=.
          by rewrite H'.
          rewrite nth_set_nth_ident => //=.
          by rewrite H'.
          destruct (eqn _ _) =>  -> //=.
          rewrite nth_set_nth_ident => //=.
          by rewrite H'.
          rewrite nth_set_nth_ident => //=.
          by rewrite H'.

    - destruct (world_global_state _).
      destruct p.
      destruct p.
      destruct (adversary_send_transaction _).
      rewrite H0 => //=.

    - destruct (world_global_state _).
      destruct p.
      destruct p.
      destruct (adversary_attempt_hash _).
      destruct p.
      rewrite H2 => //=.
      case (eqn _ _) => //=.
      
    - case: (world_global_state _) H0 H1=>[[[a b]]] c d H0.
      by case: (adversary_send_chain b _)=>??->.
Qed. *)





(* Lemma adversarial_minority_induction  (w w' : World) (q : RndGen) :
   world_step w w' q -> adversarial_minority w -> adversarial_minority w'. *)
 


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
        let: (is_corrupt, hash_round) := block_pair in  
      (hash_round  == r) && (~~ is_corrupt))
      (BlockMap_records (world_block_history w))) > 0.


Definition unsuccessful_round (w : World) (r : nat) :=
  length
    (filter
      (fun block_pair =>
        let: (is_corrupt, hash_round) := block_pair in  
      (hash_round  == r) && (~~ is_corrupt))
      (BlockMap_records (world_block_history w))) == 0.



Definition uniquely_successful_round (w : World) (r : nat) :=
  length
    (filter
      (fun block_pair =>
        let: (is_corrupt, hash_round) := block_pair in  
      (hash_round  == r) && (~~ is_corrupt))
      (BlockMap_records (world_block_history w))) == 1.



Definition bounded_successful_round (w : World) (r : nat) :=
  (* (forallb (r' : nat), (r' < r) && (r' >= r - delta) -> unsuccessful_round w r') &&   *)
  (all (fun r' => unsuccessful_round w r') (itoj (r - delta + 1) (r))) &&  
    successful_round w r.


Definition bounded_uniquely_successful_round (w : World) (r : nat) :=
  (* (forall (r' : nat), ((r' <= r + delta) && (r' >= r - delta) && (r' != r)) -> unsuccessful_round w r') /\ *)
  (all (fun r' => (unsuccessful_round w r') || (r' == r)) (itoj (r - delta + 1) (r + delta))) &&
    (uniquely_successful_round w r).


Definition adversarial_block_count (w : World) (r : nat) :=
  length (filter
      (fun block_pair =>
        let: (is_corrupt, hash_round) := block_pair in  
      (hash_round  == r) && is_corrupt)
      (BlockMap_records (world_block_history w))).

Definition nth_block_is_honest (c : BlockChain) (n : nat) (w : World) :=
  match (fixlist_get_nth c n) with
    | Some value => ~~ block_is_adversarial value w
    | None => false
  end.


Definition nth_block_hashed_in_a_uniquely_successful_round (w : World) (chain : BlockChain) (n : nat) :=
      let: o_block := (fixlist_get_nth chain n) in
      match o_block with
        | None => None 
        | Some block => 
          let: round := block_hash_round block w in
          Some(bounded_uniquely_successful_round w round)
        end.
    
Definition nth_block_is_adversarial (w : World) (chain : BlockChain) (n : nat) :=
      let: o_block := (fixlist_get_nth chain n) in
      match o_block with
        | None => None
        | Some block => block_is_adversarial block w
        end.
 

Definition nth_block_equals (w : World) (chain : BlockChain) (n : nat) (block : option Block) :=
      let: o_block := (fixlist_get_nth chain n) in
      o_block == block.
      
Definition nth_block (w : World) (chain : BlockChain) (n : nat) :=
  (fixlist_get_nth chain n).

Lemma unique_round (w : World) (n : nat) (chain : BlockChain) :
    chain \in (fixlist_unwrap (world_chain_history w)) -> length chain > n -> nth_block_is_honest chain n w  -> nth_block_hashed_in_a_uniquely_successful_round w chain n ->
    (forall (other_chain : BlockChain), 
    other_chain \in (fixlist_unwrap (world_chain_history w)) -> 
    length other_chain > n -> 
    nth_block_is_adversarial w other_chain n  \/ nth_block_equals w other_chain n (nth_block w chain n)).
Admitted.



Definition actor_n_chain_length (w : World) (n : 'I_n_max_actors) : nat :=
  let: (actor, is_corrupted) := tnth (global_local_states (world_global_state w)) n in
  length (honest_current_chain actor) .

Definition world_round (w : World) : nat := 
  let: state := world_global_state w in
  global_current_round state.

Definition actor_n_is_corrupt (w:World) (n:'I_n_max_actors) : bool :=
  let: (actor, is_corrupted) := tnth  (global_local_states (world_global_state w)) n in
  is_corrupted.
Definition actor_n_is_honest (w: World) (n: nat) : bool.
  case (n < n_max_actors) eqn:H.
  exact (~~(actor_n_is_corrupt w (Ordinal H))).
  exact false.
Defined.

Definition is_uncorrputed_actor (actors: n_max_actors.-tuple [eqType of ([eqType of LocalState] * [eqType of bool])]) (addr: Addr) : option ('I_n_max_actors* LocalState).
  case addr eqn:Haddr.
    case (m < n_max_actors) eqn: H.
      case (tnth actors (Ordinal H)) => actor is_corrupt.
        case is_corrupt eqn: H'.
          (* if the actor is corrupt *)
          exact None.
        (* if the actor is not corrupt *)
        exact (Some (Ordinal H, actor)).
      (* if the address is not valid *)
      exact None.
Defined.




(* Lemma chain_growth (w : World) (round : nat) (l : nat) :
  (world_round w) = round ->
  (exists 
  (n : 'I_n_max_actors), 


  (actor_n_chain_length w n = l) /\ 

  ~~ (actor_n_is_corrupt w n)) 
  ->
  
  (forall (future_w : World), 
    ((world_round future_w) >= round + delta - 1) ->
    (forall (n : 'I_n_max_actors), ~~ (actor_n_is_corrupt w n) ->
      actor_n_chain_length w n >= l + no_successful_rounds w round ((world_round future_w) - 1))).

Proof.
Admitted.
 *)

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

(* Definition common_prefix_property (current_w : World) (k r1 r2 : nat) (a1 a2 : 'I_n_max_actors) (c1 c2 : BlockChain) :=
  (* current w is valid *)
  (world_round_no current_w) >= r2 ->
  r1 <= r2 ->
  (a1 < n_max_actors) -> (a2 < n_max_actors) ->
  ~~ (actor_n_is_corrupt current_w a1) -> ~~ (actor_n_is_corrupt current_w a1) ->
  (* players a1 a2 adopting the chains at rounds r1, r2 *)
  (exists (w' wr1 : World), 
  (* reachable initWorld w' -> reachable w' wr1 -> reachable wr1 current_w ->   *)
    adopt_at_round w' wr1 c1 (widen_ord (leq_addr _ _) a1) r1) ->
  (exists (w'' wr2 : World), 
  (* reachable initWorld w'' -> reachable w'' wr2 -> reachable wr2 current_w ->   *)
    adopt_at_round w'' wr2 c2 (widen_ord (leq_addr _ _) a2) r2) ->
  (* then pruning k blocks from the head of c1 is a subsequence of c2*)
  prefix (drop k c1) c2.
 *)

Definition chain_quality_property (w : World) (l u : nat) (agent : 'I_n_max_actors) := 
  (* states that... *)
    let: (actor, is_corrupt) := tnth (world_actors w) agent in
    let: current_chain := honest_current_chain actor in
       (* the current actor is not corrupt *)
      (~~ is_corrupt) &&
       (* the length of the actors chain is longer than length *)
      (fixlist_length current_chain > l) &&
      (* all consecutive sequences of length l, have fewer than u adversarial blocks*)
      (all_consecutive_sequences current_chain l (fun blocks => 
        length (filter (fun block => match block_is_adversarial block w with 
          | Some (is_adv) => is_adv
          | None => false
          end) (flatten (map (fun x => match x with Some x' => [:: x'] | None => [::] end) blocks)))  <= u)).




Definition no_adversarial_blocks' (w: World) (from to : nat) : nat:= 
  foldr (fun round acc => acc + adversarial_block_count w round) 0 (itoj from to).

Definition no_adversarial_blocks (w: World) (from to : nat) : 'I_(N_rounds * n_max_actors). 
  case ((no_adversarial_blocks' w from to) < (N_rounds * n_max_actors)) eqn: H.
  exact (Ordinal H).
  exact (Ordinal valid_N_rounds_mul_n_max_actors).
Defined.

Definition no_successful_rounds' (w : World) (from : nat) (to : nat) : nat :=
  length(filter
    (fun round => successful_round w round)
    (itoj from to)).


Definition no_successful_rounds (w: World) (from to : nat) : 'I_N_rounds. 
  case ((no_successful_rounds' w from to) < N_rounds) eqn: H.
  exact (Ordinal H).
  exact (Ordinal valid_N_rounds).
Defined.


Definition no_bounded_successful_rounds' (w : World) (from : nat) (to : nat) : nat :=
  length(filter
    (fun round => bounded_successful_round w round)
    (itoj from to)).

Definition no_bounded_successful_rounds (w: World) (from to : nat) : 'I_N_rounds. 
  case ((no_bounded_successful_rounds' w from to) < N_rounds ) eqn: H.
  exact (Ordinal H).
  exact (Ordinal valid_N_rounds).
Defined.




Definition no_bounded_uniquely_successful_rounds' (w : World) (from : nat) (to : nat) : nat :=
  length(filter
    (fun round => bounded_uniquely_successful_round w round)
    (itoj from to)).

Definition no_bounded_uniquely_successful_rounds (w: World) (from to : nat) : 'I_N_rounds. 
  case ((no_bounded_successful_rounds' w from to) < N_rounds) eqn: H.
  exact (Ordinal H).
  exact (Ordinal valid_N_rounds).
Defined.




Definition all_chains_after_round_have_length_ge (w : World) (s v : nat) :=
          (all
                        (fun pr =>
                            let: (rec_chain, rec_round, rec_actr) := pr in
                            (* documented after s *)
                            if ((nat_of_ord rec_round) > s) then
                                (* has a length of at least *)
                                (fixlist_length rec_chain >= v)
                            else 
                            true)
                        (fixlist_unwrap (world_adoption_history w))) .

Definition insertion_occurred (w : World) (from to : nat)  : bool :=
  has 
    (fun pr1 =>
      let: (b1, ( is_adv, r1))  := pr1 in
      has 
      (fun pr2 => 
        let: (b2, ( is_adv, r2))  := pr2 in
        has
        (fun pr3 =>
          let: (b3, ( is_adv, r3))  := pr3 in
          (* given three blocks, such that *)
          [&&
            (* root -> .. -> [b1] -> [b2] -> .... -> head*) (* block 1 was hashed first *) (r1 < r2), 
            (* block 2 was hashed second *)
            (* block 3 was hashed last *)
            (r2 < r3), 

            (* such that r1, r2, r3 are all in the range[from..to]*)
            (r1 \in (itoj from to)),
            (r2 \in (itoj from to)),
            (r3 \in (itoj from to)),
            
            (* block 1 connects to block 2 *)
             (if verify_hash b1 (world_hash w) is Some(hash_b1) then
              (block_link b2 == hash_b1)
             else false),

            (* but block 1 also connects to block 3 *)
             (if verify_hash b1 (world_hash w) is Some(hash_b1) then
              (block_link b3 == hash_b1)
             else false) &

            (* and block 3 connects to block 2 *)
             (if verify_hash b3 (world_hash w) is Some(hash_b3) then
              (block_link b2 == hash_b3)
             else false)
          ]
        
        )
        (BlockMap_pairs (world_block_history w))
      )
        (BlockMap_pairs (world_block_history w))
    )
    (BlockMap_pairs (world_block_history w)).


(* if the same block is made multiple times *)
Definition copy_occurred (w : World) (from to : nat) :=
  ~~ (uniq (map (fun pr => 
          let: (bl, (is_adv, round))  := pr in
          bl)
  (filter (fun pr => 
          let: (bl, (is_adv, round))  := pr in
          round \in (itoj from to))
    (BlockMap_pairs (world_block_history w))))).

(* TODO: Bitcoin backbone proof uses more strict formulation of these 
  stating not that nodes are hashed in different rounds, but rather in terms
  of their position in chains
*)
Definition prediction_occurred (w : World) (from to : nat)  : bool :=
  has 
    (fun pr1 =>
      let: (b1, ( is_adv, r1))  := pr1 in
      has 
      (fun pr2 => 
        let: (b2, ( is_adv, r2))  := pr2 in
         (* given two blocks, such that *)
          [&&
            (* root -> .. -> [b1] -> [b2] -> .... -> head*)
            (* block 1 was hashed first *)
            (* block 2 was hashed second *)
            (r1 < r2), 
            (* such that r1, r2 are all in the range[from..to]*)
            (r1 \in (itoj from to)),
            (r2 \in (itoj from to)) &
            
            (* but block 2 connects to block 1 *)
             (if verify_hash b2 (world_hash w) is Some(hash_b2) then
              (block_link b1 == hash_b2)
             else false)
          ]
        
        )
        (BlockMap_pairs (world_block_history w))
    )
    (BlockMap_pairs (world_block_history w)).
