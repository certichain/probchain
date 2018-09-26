
(* Implementation of Bitcoin Protocol *)
(* Does not compile yet - as probability issues have not been resolved. *)



From mathcomp.ssreflect Require Import
     ssreflect ssrbool ssrnat eqtype fintype choice ssrfun seq path finfun.


From mathcomp.ssreflect
Require Import tuple.

Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.ProofIrrelevance.
Require Import Coq.Program.Equality.



From Probchain Require Import
     BlockChain AddressList OracleState
     BlockMap InvMisc Parameters FixedList FixedMap.

Set Implicit Arguments.

Parameter adversary_internal_state : finType.
Parameter adversary_internal_initial_state : adversary_internal_state.
Parameter adversary_internal_state_change :
  {ffun adversary_internal_state -> adversary_internal_state}.
Parameter adversary_internal_insert_transaction:
  {ffun adversary_internal_state ->
   {ffun Transaction -> adversary_internal_state}}.
Parameter adversary_internal_insert_chain:
  {ffun adversary_internal_state ->
   {ffun BlockChain -> adversary_internal_state}}.
Parameter adversary_internal_generate_block:
  {ffun adversary_internal_state ->
   {ffun MessagePool ->
    (adversary_internal_state * (Nonce * Hashed * BlockRecord))}}.
Parameter adversary_internal_provide_block_hash_result:
  {ffun adversary_internal_state ->
   {ffun (Nonce * Hashed * BlockRecord) ->
    {ffun Hashed -> adversary_internal_state}}}.
Parameter adversary_internal_send_chain:
  {ffun adversary_internal_state -> (adversary_internal_state * BlockChain)}.
Parameter adversary_internal_send_transaction:
  {ffun adversary_internal_state ->
   (adversary_internal_state * Transaction * AddressList)}.



Definition to_addr (value : 'I_n_max_actors) : Addr :=
  ((widen_ord (m:=n_max_actors + 2))^~ value) (leq_addr 2 n_max_actors).

 
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
(* Changing the state -- an operation provided by an adversary *) 
  adversary_state_change: {ffun T -> T}; 

  adversary_insert_transaction: {ffun T -> {ffun Transaction -> T}};
  adversary_insert_chain: {ffun T -> {ffun BlockChain -> T}};

  (* Required to allow adversary limited queries to the oracle*)
  (* the adversary can propose a block to be hashed*)
  adversary_generate_block:
    {ffun T -> {ffun MessagePool -> (T * (Nonce * Hashed * BlockRecord))}};

  (* the result of the hash is returned to the adversary through this method -
     is the block necassary? *)
  (* it has to be structured this way, as we can not allow the adversary
     access to the oracle directly*)
  adversary_provide_block_hash_result:
    {ffun T -> {ffun (Nonce * Hashed * BlockRecord) -> {ffun Hashed -> T}}};

  (* Required to allow the adversary to broadcast chains *)
  (* I'm not sure how assertions about the blockchain being
     unable to randomly guess valid blockchains will be made*)
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
  {ffun adversary_internal_state  ->
   {ffun Transaction -> adversary_internal_state }} *
  {ffun adversary_internal_state  ->
   {ffun BlockChain -> adversary_internal_state }} *
  {ffun adversary_internal_state  ->
   {ffun MessagePool ->
    adversary_internal_state  * (Nonce * Hashed * BlockRecord)}} *
  {ffun adversary_internal_state  ->
   {ffun Nonce * Hashed * BlockRecord ->
    {ffun Hashed -> adversary_internal_state }}} *
  {ffun adversary_internal_state  -> adversary_internal_state  * BlockChain} * 
  {ffun adversary_internal_state   ->
   (adversary_internal_state   * Transaction * AddressList)} *
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
  Eval hnf in
    ChoiceType (Adversary adversary_internal_state) adversary_choiceMixin.

Definition adversary_countMixin :=
  CanCountMixin adversary_cancel.
Canonical adversary_countType :=
  Eval hnf in
    CountType (Adversary adversary_internal_state) adversary_countMixin.

Definition adversary_finMixin :=
  CanFinMixin adversary_cancel.
Canonical adversary_finType :=
  Eval hnf in FinType (Adversary adversary_internal_state) adversary_finMixin.


Canonical adversary_of_eqType :=
  Eval hnf in [eqType of (Adversary adversary_internal_state)].
Canonical adversary_of_choiceType :=
  Eval hnf in [choiceType of (Adversary adversary_internal_state)].
Canonical adversary_of_countType :=
  Eval hnf in [countType of (Adversary adversary_internal_state)].
Canonical adversary_of_finType :=
  Eval hnf in [finType of (Adversary adversary_internal_state)].




Definition local_TransactionPool :=
  fixlist Transaction Honest_TransactionPool_size.




(* A node's local state consists of 
    1. it's currently held chain
    2. all transactions it has been delivered 
    3. all chains that it has been sent since it's last activation
    4. an extra parameter to persist proof of work calculations
       between rounds. *)
Record LocalState := mkLclSt {
  honest_current_chain: BlockChain;
  honest_local_transaction_pool: local_TransactionPool;
  honest_local_message_pool:
    fixlist [eqType of BlockChain] Honest_MessagePool_size ;
}.

Definition initLocalState := mkLclSt
                               initBlockChain
                               (fixlist_empty
                                  Transaction Honest_TransactionPool_size)
                               (fixlist_empty
                                  [eqType of BlockChain] Honest_MessagePool_size).

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
      1. A sequence of LocalStates, and a boolean representing whether
         the state is corrupted
      2. An address representing the currently executing entity -
         when addr == length of local states + 1,
         the round is complete
      3. A number representing the current round
*)
Record GlobalState := mkGlobalState
{
  global_local_states: n_max_actors.-tuple
                                   [eqType of
                                           ([eqType of
                                                    LocalState] *
                                            [eqType of bool])];
  global_adversary: Adversary adversary_internal_state ;
  global_currently_active: Addr;
  global_current_round: (ordinal N_rounds);
}.



Notation "[ g '.actors]'" := (global_local_states g).
Notation "[ g '.adv]'" := (global_adversary g).
Notation "[ g '.#active]'" := (global_currently_active g).
Notation "[ g '.#round]'" := (global_current_round g).

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
     the length exceeds delta, the last entry is removed,
     and all messages delivered *)
  (* thus this achieves the simulation of a delta delay *)
  world_message_pool: fixlist [eqType of MessagePool] delta;
  (* represents the shared oracle state *)
  world_hash: OracleState;
  (* Contains every block seen *)
  world_block_history: BlockMap;
  (* Contains every chain ever seen *)
  world_chain_history: fixlist [eqType of BlockChain ] ChainHistory_size;
  (* Contains the number of messages sent by the
     adversary for the current round *)
  world_adversary_message_quota: (ordinal Adversary_max_Message_sends);
  (* Contains the number of transactions sent by the adversary
     for the current round *)
  world_adversary_transaction_quota: (ordinal Adversary_max_Transaction_sends);
  (* Contains the number of transactions sent by honest players *)
  world_honest_transaction_quota: (ordinal Honest_max_Transaction_sends);

  (* Contains a listing of the held chain at each round for each actor *)
  world_adoption_history:
    fixlist
      [eqType of (BlockChain * ordinal N_rounds * 'I_n_max_actors)]
      (n_max_actors * N_rounds);
}.


Notation "[ w '.state]'" := (world_global_state w).
Notation "[ w '.tx_pool]'" := (world_transaction_pool w).
Notation "[ w '.inflight]'" := (world_inflight_pool w).
Notation "[ w '.messages]'" := (world_message_pool w).
Notation "[ w '.oracle]'" := (world_hash w).
Notation "[ w '.blocks]'" := (world_block_history w).
Notation "[ w '.chains]'" := (world_chain_history w).
Notation "[ w '.#adv_msgs]'" := (world_adversary_message_quota w).
Notation "[ w '.#adv_tx]'" := (world_adversary_transaction_quota w).
Notation "[ w '.#hon_tx]'" := (world_honest_transaction_quota w).
Notation "[ w '.adopt_history]'" := (world_adoption_history w).



Definition initWorldMessagePool := (fixlist_empty [eqType of MessagePool] delta).
Definition initWorldChainHistory :=
  (fixlist_empty [eqType of BlockChain] ChainHistory_size).
Definition initWorldAdoptionHistory :=
  (fixlist_empty
     [eqType of (BlockChain * ordinal N_rounds * 'I_n_max_actors)]
     (n_max_actors * N_rounds)).

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




(* A round is complete if the currently_active index is one greater
  than the length of the actors array *)
Definition round_ended (w: World) :=
 (nat_of_ord (global_currently_active (world_global_state w)) == n_max_actors + 1) && 
  ((global_current_round (world_global_state w)) + 1 < N_rounds).

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
      (if (active < n_max_actors)%N as b
          return ((active < n_max_actors)%N = b -> option 'I_n_max_actors)
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
       else fun _ : (active < n_max_actors)%N = false => None)
        (erefl (active < n_max_actors)%N)
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


Lemma round_in_range (active: Addr) :
  nat_of_ord active != n_max_actors.+1 -> active.+1 < n_max_actors + 2.
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
| {| global_local_states := actors;
     global_adversary := adversary;
     global_currently_active :=
  active; global_current_round := round |} =>
    let b := nat_of_ord active == n_max_actors.+1 in
    let H : (nat_of_ord active == n_max_actors.+1) = b := erefl b in
    (if b as b0 return ((nat_of_ord active == n_max_actors.+1) = _ -> GlobalState)
     then fun prf : (nat_of_ord active == n_max_actors.+1) = _ => state
     else fun prf : (nat_of_ord active == n_max_actors.+1) = false =>
           (fun H1 : nat_of_ord active != n_max_actors.+1 =>
            ssr_suff (active.+1 < n_max_actors + 2)
              (fun H' : active.+1 < n_max_actors + 2 =>
                {|
                    global_local_states := actors;
                    global_adversary := adversary;
                    global_currently_active :=
                      Ordinal (n:=n_max_actors + 2) (m:=active.+1) H';
                    global_current_round := round
                |}
              ) (round_in_range active H1)
           ) (introN eqP (elimTF eqP prf))) H
end .


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
        exact
          (mkGlobalState actors adversary
                         (Ordinal (ltn_addr _ valid_n_max_actors))
                         (Ordinal Hact)).
        (* if it isn't less than the maximum rounds, just return the state *)
        exact (state).
      (* if next round is called on a state, that has not finished execution,
         it does nothing*)
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
      (mkGlobalState new_actors adversary active round) .


Definition insert_multicast_message 
  (addresses: AddressList) 
  (bc: BlockChain) 
  (initial_state: GlobalState) : GlobalState := 
      foldr
        (fun addr state => insert_message addr bc state)
        initial_state
        (AddressList_unwrap addresses).
 


(* insert the corresponding message into every actor's message pool *)
Definition broadcast_message
      (bc : BlockChain) (initial_state: GlobalState) : GlobalState :=
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


Definition update_message_pool_queue
           (message_list_queue:
              fixlist
                [eqType of MessagePool] delta)
           (new_message_list : MessagePool)
  : (seq Message * (fixlist [eqType of MessagePool] delta)) :=
  let: (new_message_list, oldest_message_list) :=
     @fixlist_enqueue _ _ (Some new_message_list) message_list_queue in
  match oldest_message_list with
    | None => ([::], new_message_list)
    | Some message_list => (fixlist_unwrap message_list, new_message_list)
  end.


Definition update_adversary_round
           (adversary : Adversary adversary_internal_state)
           (round : 'I_N_rounds) : Adversary adversary_internal_state :=
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




    

Definition validate_blockchain_links
           (bc : BlockChain) (oracle_state : OracleState) : bool :=
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
                    if
                      (block_link block == hash_value)
                        && (hash_value < T_Hashing_Difficulty)
                        then (pred_block, false)
                        else (pred_block, true)
                end
          )
          (h, false)  
          t
          in 
          ~~ result
  end.

Definition validate_blockchain
           (bc : BlockChain) (oracle_state: OracleState) : bool :=
  (* a blockchain is valid if the links are well formed *)
  validate_blockchain_links bc oracle_state && 
  (* and all transactions are valid *)
  validate_transactions (BlockChain_unwrap bc).
  
(* finds the longest valid chain for a node *)
Definition honest_max_valid
           (state: LocalState) (oracle_state: OracleState) : BlockChain :=
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
  Parses v as a sequence of transactions and returns the largest subsequence
  that is valid with respect to the chain, and whoose transactions are not
  included in xc

  the following function, when given an honest node's transaction pool and chain, 
  may return a blockrecord (list containing x < MAX_BLOCK_LENGTH) and the
  transaction pool with the corresponding values removed
*)
Definition find_maximal_valid_subset
           (transactions : local_TransactionPool)
           (blk: BlockChain) : (BlockRecord * local_TransactionPool) :=
(* naive approach - iterate through transactions and only include those that
   are valid specifically it's naive because it assumes that all transactions
   are delivered in order (i.e if invalid, reordering the sequence won't change
   whether it's valid or not) but I believe this is a correct assumption as
  transactions are delivered immediately *)
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
                  if Transaction_valid transaction
                                       ((fixlist_unwrap already_included)
                                          ++ chain_transactions)

                    (* and the transaction is valid*)
                    (* insert it into the blockrecord *)
                  then
                    (fixlist_insert
                       already_included transaction,
                     fixlist_remove remaining index )
                    (* otherwise don't*)
                    else (already_included, remaining)
                end)
      (initBlockRecord, transactions)
      (iota 0 TransactionPool_length).


Definition retrieve_head_link
           (b : BlockChain) (oracle_state : OracleState) : option Hashed :=
  match fixlist_unwrap b with
    | [::] => Some (Ordinal (ltn0Sn _))
    | h :: t => verify_hash h oracle_state
  end.


    

Definition update_transaction_pool
           (addr : 'I_n_max_actors)
           (initial_state : LocalState)
           (transaction_pool: TransactionPool) : LocalState :=
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

Definition update_adversary_transaction_pool
           (initial_adv: Adversary adversary_internal_state)
           (transaction_pool: TransactionPool)
  : Adversary adversary_internal_state:=
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


Definition successful_round_internal (bh : BlockMap) (r : nat) : bool :=
  length
    (filter
      (fun block_pair =>
        let: (is_corrupt, hash_round) := block_pair in  
      (hash_round  == r) && (~~ is_corrupt))
      (BlockMap_records bh)) > 0.

Definition successful_round (w : World) (r : nat) : bool :=
  length
    (filter
      (fun block_pair =>
        let: (is_corrupt, hash_round) := block_pair in  
      (hash_round  == r) && (~~ is_corrupt))
      (BlockMap_records (world_block_history w))) > 0.

Lemma successful_round_internalP (w : World) r :
  successful_round w r = successful_round_internal [w.blocks] r.
  by rewrite /successful_round/successful_round_internal.
Qed.


Lemma successful_round_rangeP w r : (r >= N_rounds) -> ~~ successful_round w r.
  move=> Hltn.
  rewrite /successful_round.
  move: (BlockMap_records_roundP (world_block_history w)) => /allP Hall.
  rewrite -eqn0Ngt -length_sizeP size_filter.
  apply/eqP; apply/has_countPn; apply/hasPn => r' Hrin.
  move: (Hall r' Hrin). clear Hall. clear Hrin.
  move: r' => [iscrpt or'] Hrlt; rewrite negb_and; apply/orP; left.
  apply/eqP => Hreq; move: Hltn Hrlt; rewrite Hreq => /leq_ltn_trans H /H.
  by rewrite ltnn.
Qed.



Definition unsuccessful_round_internal (bh : BlockMap) (r : nat) :=
  length
    (filter
      (fun block_pair =>
        let: (is_corrupt, hash_round) := block_pair in  
      (hash_round  == r) && (~~ is_corrupt))
      (BlockMap_records bh)) == 0.



Definition unsuccessful_round (w : World) (r : nat) :=
  length
    (filter
      (fun block_pair =>
        let: (is_corrupt, hash_round) := block_pair in  
      (hash_round  == r) && (~~ is_corrupt))
      (BlockMap_records (world_block_history w))) == 0.

Lemma unsuccessful_round_internalP (w : World) r :
  unsuccessful_round w r = unsuccessful_round_internal [w.blocks] r.
  by rewrite /unsuccessful_round/unsuccessful_round_internal.
Qed.





Lemma successful_roundP w r : successful_round w r = ~~ unsuccessful_round w r.
Proof.
  by rewrite /successful_round/unsuccessful_round lt0n//=.
Qed.

Lemma unsuccessful_roundP w r : unsuccessful_round w r = ~~ successful_round w r.
Proof.
  by rewrite /successful_round/unsuccessful_round eqn0Ngt.
Qed.




Definition uniquely_successful_round (w : World) (r : nat) :=
  length
    (filter
      (fun block_pair =>

        let: (is_corrupt, hash_round) := block_pair in  
      (hash_round  == r) && (~~ is_corrupt))
      (BlockMap_records (world_block_history w))) == 1.

Lemma uniquely_successful_roundP w r :
  uniquely_successful_round w r -> successful_round w r.
Proof.
    by rewrite
         /successful_round/successful_round_internal/uniquely_successful_round
    => /eqP ->.
Qed.


Definition bounded_successful_round_internal (bh : BlockMap) (r : nat) :=
  (all (fun r' => unsuccessful_round_internal bh r') (itoj (r + 1 - delta ) (r)))
    && successful_round_internal bh r.


Definition bounded_successful_round (w : World) (r : nat) :=
  (all (fun r' => unsuccessful_round w r') (itoj (r + 1 - delta ) (r)))
    && successful_round w r.

Lemma bounded_successful_round_internalP (w : World) (r : nat) :
  bounded_successful_round w r = bounded_successful_round_internal [w.blocks] r.
Proof.
  by rewrite/bounded_successful_round/bounded_successful_round_internal//=.
Qed.

Lemma bounded_successful_round_forall w r :
  bounded_successful_round w r -> forall r',
    ((r - delta).+1 <= r' < r) -> unsuccessful_round w r'.
Proof.
  case Heqn: (delta == 0).
    move/eqP: Heqn => ->.
    move=>Hbr r' /andP [].
    by move=>/ltn_trans H /H ; rewrite subn0 ltnn.
  move/negP/negP: Heqn.
  rewrite -lt0n => Hdelta.
  case  Heqnr: (r == 0).
    move/eqP: Heqnr => ->.
    rewrite sub0n.
    move=>Hbr r' /andP [].
    by move=>/ltn_trans H /H ; rewrite ltnn.
  move/negP/negP: Heqnr.
  rewrite -lt0n => Hr.

  rewrite /bounded_successful_round => /andP [].
  move=>/allP Hbs Hsc r' /andP [Hltr Hgtr].
  apply Hbs.
  rewrite /itoj.
  rewrite mem_iota.
  apply/andP; split.
  rewrite -ltnS.
  rewrite addn1.
  case Hltd: (delta <= r).
  by rewrite subSn //=.
  move/negP/negP: Hltd.
  rewrite -ltnNge.
  by rewrite -subn_eq0 => /eqP ->.
  rewrite subnKC //=.
  rewrite addn1.
  case Hltd: (delta <= r).
  rewrite subSn //=.
  by move: (ltn_trans Hltr Hgtr).
  move/negP/negP: Hltd.
  rewrite -ltnNge.
  by rewrite -subn_eq0 => /eqP ->.
Qed.

Lemma bounded_successful_round_rangeP w r :
  (r >= N_rounds) -> ~~ bounded_successful_round w r.
  move=> Hltn.
  rewrite /bounded_successful_round negb_and.
  by apply/orP; right; apply successful_round_rangeP.
Qed.




Lemma bounded_successful_round_exists w r :
  (exists r', ((r - delta).+1 <= r' < r) && successful_round w r') ->
  ~~ bounded_successful_round w r.
Proof.
  move=> [r' /andP [ /andP [Hltr Hgt] Hsuc]].
  rewrite /bounded_successful_round.
  rewrite negb_and ;apply/orP.
  left.
  apply /allPn.
  exists r'; last first.
  by rewrite -successful_roundP.
  rewrite /itoj.
  rewrite mem_iota.
  apply/andP; split.
  move: Hltr; rewrite addn1.
  case Hltd: (delta <= r).
  by rewrite subSn //=.
  by move/negP/negP: Hltd; rewrite -ltnNge; rewrite -subn_eq0 => /eqP ->.
  rewrite subnKC //=.
  rewrite addn1.
  case Hltd: (delta <= r).
  rewrite subSn //=.
  by move: (ltn_trans Hltr Hgt).
  move/negP/negP: Hltd.
  rewrite -ltnNge.
  by rewrite -subn_eq0 => /eqP ->.
Qed.




Lemma bounded_successful_round_lim_base w : bounded_successful_round w 0 -> forall r',
      (0 < r' < delta) -> ~~ bounded_successful_round w r'.
Proof.
  move=> /andP [_ Hsuc] r'.
  move=>/andP [Hgt0 Hltd].
  rewrite /bounded_successful_round.
  rewrite negb_and.
  apply/orP.
  left.
  apply /allPn.
  exists 0.
  rewrite mem_iota.
  apply/andP; split.
  rewrite addn1.
  rewrite -subn_eq0 in Hltd.
  by move/eqP: Hltd => -> //=.

  rewrite subnKC //=.
  rewrite addn1.
  rewrite -subn_eq0 in Hltd.
  by move/eqP: Hltd => -> //=.

  by rewrite -successful_roundP.
Qed.



 
Lemma bounded_successful_round_lim w r : 
  bounded_successful_round w r -> forall r',
    (r < r') && (r' < r + delta) -> ~~ bounded_successful_round w r'.
Proof.
  case Hrvld : (0 < r); last first.
  move/negP/negP: Hrvld.
  rewrite -eqn0Ngt => /eqP ->.
  rewrite add0n.
  by apply bounded_successful_round_lim_base.

  rewrite /bounded_successful_round => /andP [Half Hsucc].

  move=> r' /andP [Hlt Hgt].

  apply bounded_successful_round_exists.
  exists r.
  move: Hsucc Half Hlt Hgt.
  move=> Hsucc Halft Hlt Hgt.

  apply/andP; split; last first. by [].
  apply/andP; split; last first. by [].
    by apply ltn_subLR => //=.
Qed.




Definition bounded_uniquely_successful_round (w : World) (r : nat) :=
  (all (fun r' => (unsuccessful_round w r') || (r' == r))
       (itoj (r - delta + 1) (r + delta)))
    && (uniquely_successful_round w r).


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


Definition nth_block_hashed_in_a_uniquely_successful_round
           (w : World) (chain : BlockChain) (n : nat) :=
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
 

Definition nth_block_equals
           (w : World) (chain : BlockChain) (n : nat) (block : option Block) :=
      let: o_block := (fixlist_get_nth chain n) in
      o_block == block.
      
Definition nth_block (w : World) (chain : BlockChain) (n : nat) :=
  (fixlist_get_nth chain n).



Definition actor_n_chain_length (w : World) (n : 'I_n_max_actors) : nat :=
  let: (actor, is_corrupted) :=
     tnth (global_local_states (world_global_state w)) n in
  fixlist_length (honest_current_chain actor) .

Definition world_round (w : World) : nat := 
  let: state := world_global_state w in
  global_current_round state.


Definition actor_n_is_corrupt_internal_unwrap
           (actors : n_max_actors.-tuple
                                 [eqType of
                                         ([eqType of LocalState] *
                                          [eqType of bool])])
           (n: 'I_n_max_actors) : bool :=
  let: (actor, is_corrupted) := tnth  actors n in
  is_corrupted.

Definition actor_n_is_corrupt_internal
           (gs : GlobalState) (n: 'I_n_max_actors) : bool :=
  let: (actor, is_corrupted) := tnth  (global_local_states gs) n in
  is_corrupted.


Lemma actor_n_is_corrupt_unwrapP (gs:GlobalState) (n:'I_n_max_actors) :
  actor_n_is_corrupt_internal gs n =
  actor_n_is_corrupt_internal_unwrap [gs.actors] n.
Proof.
  by rewrite/actor_n_is_corrupt_internal//=.
Qed.


Definition actor_n_is_corrupt (w:World) (n:'I_n_max_actors) : bool :=
  let: (actor, is_corrupted) := tnth
                                  (global_local_states
                                     (world_global_state w)) n in
  is_corrupted.

Lemma actor_n_is_corrupt_internalP (w:World) (n:'I_n_max_actors) :
    actor_n_is_corrupt w n = actor_n_is_corrupt_internal [w.state] n.
Proof.
  by rewrite/actor_n_is_corrupt//=.
Qed.


Definition actor_n_is_honest_internal_unwrap
           (actors :
              n_max_actors.-tuple
                          [eqType of ([eqType of LocalState] * [eqType of bool])])
           (n: nat) : bool :=
  let b := n < n_max_actors in
  let H : (n < n_max_actors) = b := erefl b in
    (if b as b0 return ((n < n_max_actors) = b0 -> bool)
     then fun H0 : (n < n_max_actors) = true =>
            ~~ actor_n_is_corrupt_internal_unwrap actors
               (Ordinal (n:=n_max_actors) (m:=n) H0)
    else xpred0) H.


Definition actor_n_is_honest_internal (gs: GlobalState) (n: nat) : bool :=
  let b := n < n_max_actors in
  let H : (n < n_max_actors) = b := erefl b in
    (if b as b0 return ((n < n_max_actors) = b0 -> bool)
     then fun H0 : (n < n_max_actors) = true =>
            ~~ actor_n_is_corrupt_internal gs
               (Ordinal (n:=n_max_actors) (m:=n) H0)
    else xpred0) H.

Lemma actor_n_is_honest_unwrapP (gs: GlobalState) (n: nat) :
  actor_n_is_honest_internal gs n =
  actor_n_is_honest_internal_unwrap [gs.actors] n.
Proof.
  by rewrite /actor_n_is_honest_internal//=.
Qed.

Definition actor_n_is_honest (w: World) (n: nat) : bool :=
  let b := n < n_max_actors in
  let H : (n < n_max_actors) = b := erefl b in
    (if b as b0 return ((n < n_max_actors) = b0 -> bool)
     then fun H0 : (n < n_max_actors) = true =>
            ~~ actor_n_is_corrupt w (Ordinal (n:=n_max_actors) (m:=n) H0)
    else xpred0) H.



Lemma actor_n_is_honest_internalP w n :
  actor_n_is_honest w n = actor_n_is_honest_internal [w.state] n.
Proof.
  by rewrite/actor_n_is_honest//=.
Qed.



Definition is_uncorrputed_actor
           (actors: n_max_actors.-tuple
                                [eqType of
                                        ([eqType of LocalState] * [eqType of bool])])
           (addr: Addr) : option ('I_n_max_actors* LocalState).
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



Definition adopt_at_round
           (w' : World) (w : World) (bc : BlockChain) (agent: Addr) (r : nat) :=
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
      then let: (w_state, w_is_corrupt) :=
              (nth (initLocalState, true) (world_actors w) agent) in
           let: (w'_state, w'_is_corrupt) :=
              (nth (initLocalState, true) (world_actors w') agent) in
              (~~ w_is_corrupt) && (~~ w'_is_corrupt) && 
              (honest_current_chain w'_state != bc) &&
              (honest_current_chain w_state == bc)
        else false
    end.




Definition no_adversarial_blocks' (w: World) (from to : nat) : nat:= 
  foldr (fun round acc => acc + adversarial_block_count w round) 0 (itoj from to).

Definition no_adversarial_blocks
           (w: World) (from to : nat) : 'I_(N_rounds * n_max_actors).
  case ((no_adversarial_blocks' w from to) < (N_rounds * n_max_actors)) eqn: H.
  exact (Ordinal H).
  exact (Ordinal valid_N_rounds_mul_n_max_actors).
Defined.

Definition no_successful_rounds' (w : World) (from : nat) (to : nat) : nat :=
  length(filter
    (fun round => successful_round w round)
    (itoj from to)).


Definition no_successful_rounds (w: World) (from to : nat) : 'I_N_rounds :=
  let b := no_successful_rounds' w from to < N_rounds in
  (if b as b0
      return ((no_successful_rounds' w from to < N_rounds) = b0 -> 'I_N_rounds)
      then fun H => Ordinal H
      else fun _ => Ordinal valid_N_rounds) (erefl b).

About bounded_successful_round_internal.


Definition no_bounded_successful_rounds'_internal (bm : BlockMap) (from to : nat) : nat :=
  length(filter
    (fun round => bounded_successful_round_internal bm round)
    (itoj from to)).


Definition no_bounded_successful_rounds' (w : World) (from : nat) (to : nat) : nat :=
  length(filter
    (fun round => bounded_successful_round w round)
    (itoj from to)).

Lemma no_bounded_successful_rounds'_internalP (w : World) from to :
  no_bounded_successful_rounds' w from to =
  no_bounded_successful_rounds'_internal [w.blocks] from to.
Proof.
  by rewrite/no_bounded_successful_rounds'//=.
Qed.

Lemma valid_Sn n : n > 0 -> n.+1 > 0. by []. Qed.




Definition no_bounded_successful_rounds_internal
           (bm: BlockMap) (from to : nat) : 'I_N_rounds.+1 :=
  let b := ((no_bounded_successful_rounds'_internal bm from to) < N_rounds.+1 ) in
  (if b as b0
      return (((no_bounded_successful_rounds'_internal bm from to) < N_rounds.+1 ) =
              b0 -> 'I_N_rounds.+1)
      then fun H => Ordinal H
      else fun _ => Ordinal (valid_Sn _ valid_N_rounds)) (erefl b).



Definition no_bounded_successful_rounds (w: World) (from to : nat) : 'I_N_rounds.+1 :=
  let b := ((no_bounded_successful_rounds' w from to) < N_rounds.+1 ) in
  (if b as b0 return (((no_bounded_successful_rounds' w from to) < N_rounds.+1 ) =
                      b0 -> 'I_N_rounds.+1)
      then fun H => Ordinal H
      else fun _ => Ordinal (valid_Sn _ valid_N_rounds)) (erefl b).


Lemma no_bounded_successful_rounds_internalP (w : World) from to :
  no_bounded_successful_rounds w from to =
  no_bounded_successful_rounds_internal [w.blocks] from to.
Proof.
  by rewrite/no_bounded_successful_rounds'//=.
Qed.


Lemma count_bounded_successful_rounds'_rangeP_weak w from to :
  from >= N_rounds -> count [eta bounded_successful_round w] (iota from to) = 0.
  move=> Hrlt.
  apply has_countPn.
  apply/hasPn => r' .
  rewrite mem_iota => /andP .
  move=> [Hrgtform Hrltto].
  apply bounded_successful_round_rangeP.
  by apply (leq_trans Hrlt).
Qed.


Lemma no_bounded_successful_rounds'_rangeP_weak w from to :
  from >= N_rounds -> no_bounded_successful_rounds' w from to = 0.
Proof.
  move=> Hrlt.
  rewrite/no_bounded_successful_rounds'.
  rewrite -length_sizeP size_filter.
  by apply count_bounded_successful_rounds'_rangeP_weak.
Qed.

Lemma no_bounded_successful_rounds'_rangeP_alt w from to :
  no_bounded_successful_rounds' w from to <= to - from.
Proof.
  rewrite /no_bounded_successful_rounds' -length_sizeP size_filter /itoj.
  by apply (leq_trans (count_size _ _)); rewrite size_iota //=.
Qed.

Lemma no_bounded_successful_rounds'_rangeP w from to :
  0 < from ->  no_bounded_successful_rounds' w from to < N_rounds.
Proof.
  move=> Hfrmvld.
  move: (no_bounded_successful_rounds'_rangeP_alt w from to) => Hrng.
  case Hlt: (to < from).
    move: (Hlt) (Hrng) => /(ltn_addr 1).
    rewrite addn1 -subn_eq0  subSS => /eqP ->; rewrite leqn0 => /eqP ->.
    by exact valid_N_rounds.
  move/negP/negP: Hlt; rewrite -leqNgt => Hlt.
  case Hfrom: (from >= N_rounds).
  by rewrite no_bounded_successful_rounds'_rangeP_weak //=; exact valid_N_rounds.
  move/negP/negP: Hfrom; rewrite -ltnNge => Hfrom.
  move: Hlt; rewrite leq_eqVlt => /orP [/eqP Htoeqf | Hlt].
     by move: Hrng; rewrite Htoeqf subnn leqn0 => /eqP ->; exact valid_N_rounds.
  case Hto: (to < N_rounds).
    move/(subn_ltn_pr ): (Hto) => Ht.
    move: (Ht from) => Hfr.
    by apply (leq_ltn_trans Hrng).
  move/negP/negP: Hto; rewrite -leqNgt => Hto.
  case Htvld: (to > 0); last first.
    move/negP/negP: Htvld; rewrite -eqn0Ngt => /eqP Heq0.
    by move: Hto valid_N_rounds; rewrite Heq0 => /leq_ltn_trans H /H; rewrite ltnn.

  rewrite /no_bounded_successful_rounds' -length_sizeP size_filter /itoj .
  move: (Hfrom) (Hfrmvld) => /ltn_exists H /H [mid [Hmid Hmideq]]. clear H.
  move: (Hto)  => /leq_exists [mid'].
  rewrite -{1}Hmideq => <-.
  rewrite addnC (addnC from) addnA -addnBA.
  rewrite subnn addn0 addnC.
  rewrite iota_add count_cat.
  rewrite Hmideq.
  rewrite (count_bounded_successful_rounds'_rangeP_weak w N_rounds).
  rewrite addn0.
  move: (count_size ([eta bounded_successful_round w]) (iota from mid)).
  rewrite size_iota => /leq_ltn_trans Hltn.
  by apply Hltn.
  by [].
  by [].
Qed.

Lemma no_bounded_successful_rounds'_rangeSP w from to :
  no_bounded_successful_rounds' w from to < N_rounds.+1.
Proof.
  case Hfltr: (0 < from).
    by
      apply (ltn_trans (no_bounded_successful_rounds'_rangeP w from to Hfltr))
      => //=.
  move: (no_bounded_successful_rounds'_rangeP_alt w from to) => Hrng.
  move/negP/negP: Hfltr.
  rewrite -eqn0Ngt => /eqP Heq0.
  case Hto: (to < N_rounds).
    move/(subn_ltn_pr ): (Hto) => Ht.
    move: (Ht from) => Hfr.
    apply (leq_ltn_trans Hrng).
    rewrite Heq0 subn0 -(addn1 N_rounds).
    by apply ltn_addr.
  move/negP/negP: Hto; rewrite -leqNgt => Hto.
  case Htvld: (to > 0); last first.
    move/negP/negP: Htvld; rewrite -eqn0Ngt => /eqP Heq0'.
    by rewrite Heq0 Heq0' //=.
   
  move: (Hto); rewrite leq_eqVlt => /orP [/eqP HNroeq| Hltn]; last first.
    move: (Hltn) valid_N_rounds => /ltn_exists H /H [mid [Hltto Heq]].
    rewrite -Heq.
    rewrite Heq0.
    rewrite /no_bounded_successful_rounds' -length_sizeP size_filter /itoj .
    rewrite subn0 iota_add count_cat add0n addnC.
    rewrite  count_bounded_successful_rounds'_rangeP_weak //= add0n.
    move: (count_size [eta bounded_successful_round w] (iota 0 N_rounds)).
    by rewrite size_iota ltnS.
  rewrite HNroeq.
  rewrite /no_bounded_successful_rounds' -length_sizeP size_filter /itoj .
  rewrite Heq0 subn0.
  move: (count_size [eta bounded_successful_round w] (iota 0 to)).
  by rewrite size_iota ltnS.
Qed.





Lemma no_bounded_successful_roundsP (P : 'I_N_rounds.+1 -> Prop) w from to : 
  P (Ordinal  (valid_Sn _ valid_N_rounds)) ->
  (forall prf :
       ((no_bounded_successful_rounds' w from to < N_rounds.+1) = true),
      P (Ordinal prf )) ->
  P (no_bounded_successful_rounds w from to).
Proof.
  move=> H0 Hind.
  rewrite/no_bounded_successful_rounds.
  set (Nb := ((no_bounded_successful_rounds' w from to))).
  case Heq: (Nb >= N_rounds.+1).
    move: (erefl _).
    move: [eta Ordinal (n:=N_rounds.+1) (m:=Nb)].
    rewrite leqNgt in Heq.
    move/negP/negP: Heq.
    rewrite -eqbF_neg => /eqP Heq.
    by rewrite Heq.
  move: (erefl _ ).
  move/negP/negP: Heq.
  rewrite -ltnNge.
  move=> Hlt.
  suff: [eta Ordinal (n:=N_rounds.+1) (m:=Nb)] = fun _ => Ordinal Hlt.
  move=> ->.
  by rewrite Hlt.
  apply: functional_extensionality=> G.
  by rewrite (proof_irrelevance _ Hlt G).
Qed.

Lemma no_bounded_successful_rounds_excl_lower w r : 
        (bounded_successful_round w r) ->
          no_bounded_successful_rounds' w (r + 1 - delta) r = 0.
Proof.
  rewrite/bounded_successful_round => /andP [] /allP Hall Hsucc.
  rewrite /no_bounded_successful_rounds'.
  rewrite -!length_sizeP !size_filter  !has_countPn //=.
  apply /hasPn => r' Hrrng; rewrite /bounded_successful_round negb_and.
  by apply/orP; right; rewrite -unsuccessful_roundP; apply Hall.
Qed.

Lemma no_bounded_successful_rounds_excl_upper w r :  
        (bounded_successful_round w r) ->
          no_bounded_successful_rounds' w r.+1 (r + delta) = 0.
  case Hdlta: (0 < delta ); last first.
  move/negP/negP: Hdlta.
  rewrite -eqn0Ngt => /eqP dtis0 _.
  rewrite /no_bounded_successful_rounds'.
  rewrite -!length_sizeP !size_filter  !has_countPn //=.
  apply /hasPn => r' .
  rewrite dtis0 addn0.
  rewrite mem_iota.
  rewrite subn_eqP //= addn0 => /andP [].
  by move=>/ltn_transPn H /H.
  move=> /bounded_successful_round_lim Hbs.
  rewrite /no_bounded_successful_rounds'.
  rewrite -!length_sizeP !size_filter  !has_countPn //=.
  apply /hasPn => r' .
  rewrite mem_iota subnKC //=.
  move=> Hrng.
  by apply Hbs.
  by elim r => //=.
Qed.



Lemma no_bounded_successful_rounds'_excl w s r :
        (~~ bounded_successful_round w s) ->
        no_bounded_successful_rounds' w r s =
        no_bounded_successful_rounds' w r s.+1.
Proof.
  move=> Hbnd.
  rewrite /no_bounded_successful_rounds';
  rewrite /itoj .
  case Hltr: (r <= s).
  rewrite subSn; last first. by [].
  rewrite -addn1.
  rewrite iota_add filter_cat //= ifN .
  by rewrite cats0.
  by rewrite subnKC .
  move/negP/negP:Hltr.
  rewrite -ltnNge => Heq0.
  rewrite subn_eqP //=.
  rewrite -subn_eq0 in Heq0.
  move/eqP: Heq0 => -> //=.
  by apply ltnW.
Qed.

Lemma no_bounded_successful_rounds_excl w s r :
        (~~ bounded_successful_round w s) ->
        no_bounded_successful_rounds w r s =
        no_bounded_successful_rounds w r s.+1.
Proof.
  move=> Hsb.
  rewrite /no_bounded_successful_rounds.
  by rewrite -no_bounded_successful_rounds'_excl //=.
Qed.



Lemma no_bounded_successful_rounds'_lim_gen w s r: 0 < delta ->
  bounded_successful_round w s ->
  no_bounded_successful_rounds' w r s =
  no_bounded_successful_rounds' w r (s.+1 - delta).
Proof.
  move=> Hdelta Hbounded_success; move: (Hbounded_success).
  rewrite/bounded_successful_round => /andP [] //= /allP Hall Hsucc.
  move: (Hbounded_success) => /no_bounded_successful_rounds_excl_lower.
  move: (Hbounded_success) => /no_bounded_successful_rounds_excl_upper.
  rewrite /no_bounded_successful_rounds' -!length_sizeP !size_filter  //= /itoj subnAC.
  move=> Hupper_bound Hlower_bound.
  case Hsltr :(s < r).
    move: (Hsltr); rewrite -subn_eq0 => /eqP ->; rewrite sub0n.
    by move: (Hsltr) => /(ltn_addr 1); rewrite addn1 -subn_eq0 subSS => /eqP -> //=.
  move/negP/negP: Hsltr; rewrite -leqNgt => Hsltr.
  case Hltn : (delta <= s - r).
 move: Hsltr.
 rewrite leq_eqVlt =>/orP [ /eqP Hrseq | ] .
 move: Hltn Hdelta.
 rewrite Hrseq subnn leqn0 => /eqP ->.
 by rewrite ltnn.
 move=> Hsltr.
 have Hsleqnr: (r <= s). by apply ltnW.
 rewrite -{1}(@subnK delta  (s - r)) //=.
 rewrite -{2}(@subnK 1 delta ) //=.
 rewrite subn1.
 rewrite (addnC delta.-1).
 rewrite addnA addn1.
 rewrite -subSn //=.
 rewrite -subSn //=.
 case HrltSs: (r <= s.+1 - delta); last first.
    move/negP/negP: HrltSs.
    rewrite -ltnNge => HrltSs.
    move: (HrltSs) => /(ltn_addr 1).
    rewrite addn1.
    move: (Hltn).
    move: (Hsltr)=> /(ltn_addr 1).
    rewrite addn1.
    rewrite -!subn_eq0.
    rewrite !subSS subnAC subnBA //=.
    rewrite !subn_eq0 => _ /leq_add H /H.
    rewrite addnBA.
    rewrite addnC.
    rewrite -addnBA.
    by rewrite -addnBA //= subnn addn0 addSn ltnn.
    by apply leq_addl.
    by rewrite -addn1; apply ltnW; apply ltn_addr.
 rewrite iota_add count_cat {2}subnAC addnBA //=.
 move: (Hltn).
 rewrite -subn_eq0 //= subnBA //= => Hltn'.
 move: (Hdelta); rewrite (addnC r) -addnBA //= subnn addn0.
 move: Hlower_bound; rewrite {1}addn1 -subnBA //= subKn. by rewrite subn1 => ->.
 rewrite leq_subLR addnC; apply (leq_trans Hltn); rewrite -ltnS -(addn1 (s + _)).
 by apply ltn_addr; rewrite addn1 ltnS; apply leq_subr.
 
  move/negP/negP: Hltn.
  rewrite -ltnNge => Hltn; move: (Hltn).
  rewrite -subn_eq0 .
  rewrite -subSn //= => /eqP -> //=.
  apply has_countPn; apply /hasPn => r'; rewrite mem_iota => /andP[ Hgtsd ].
  case Hlts: (r < s); last first.
  move/negP/negP: Hlts.
  rewrite -ltnNge  -subn_eq0 subSS => /eqP ->.
  rewrite addn0. move/leq_ltn_trans: Hgtsd => H /H. by rewrite ltnn.
  rewrite subnKC//= => Hrlts.
  rewrite /bounded_successful_round negb_and.
  apply/orP.
  move: (Hltn).
  rewrite -subn_eq0 -subSn; last first. by apply ltnW.
  rewrite subnAC subn_eq0 =>/leq_trans Hlt.
  move/Hlt: Hgtsd => Hlbndr. clear Hlt; right.
  rewrite -unsuccessful_roundP.
  apply Hall; rewrite /itoj addn1 mem_iota.
  apply/andP; split=> //=.
  move/leq_ltn_trans: (Hlbndr) => Hlt.
  move/Hlt: (Hrlts); clear Hlt.
  move: Hltn Hlts Hrlts.
  case: delta => //= delta .
  case Hdlt: (delta <= s). by rewrite !subSS subKn //= subnK //=.
  move/negP/negP: Hdlt.
  rewrite -ltnNge .
  move=> Hdlt; move: (Hdlt).
  move=>/(ltn_addr 1).
  rewrite addn1 -subn_eq0 subSS => /eqP ->.
  by rewrite subn0 add0n.
Qed.

Lemma no_bounded_successful_rounds'_lim_subd w s r : (0 < delta) -> (r <= s) ->
  bounded_successful_round w (s) ->
                (no_bounded_successful_rounds' w r s.+1)%nat =
                (no_bounded_successful_rounds' w r (s.+1 - delta) + 1)%nat.
Proof.
  move=> Hdlta0 Hrlts Hbound .
  rewrite -no_bounded_successful_rounds'_lim_gen //=.
  rewrite /no_bounded_successful_rounds'.
  rewrite  -!length_sizeP !size_filter  //= /itoj subSn; last first. by [].
  rewrite -addn1 iota_add count_cat.
  by rewrite addnBA //= (addnC r) -addnBA //= subnn addn0 addn0 Hbound //=.
Qed.

(* todo: move to invmisc *)
Lemma length_rcons A (x : A) (xs : seq.seq A) : length (rcons xs x) = (length xs).+1.
Proof.
  by rewrite -!length_sizeP size_rcons.
Qed.
Lemma count_rcons T (P : pred T) (xs : seq T) x :
  count P (rcons xs  x) = count P xs + nat_of_bool (P x).
Proof.
  move: x.
  elim: xs => //= y ys IHx x .
  by rewrite IHx addnA.
Qed.



Lemma unsuccessful_round_internal_insert_adversarial bm bl hr :
    fixlist_is_top_heavy bm ->
    [length bm] < BlockHistory_size ->
    [eta unsuccessful_round_internal [bm <- (bl, (true, hr))]]  = 
    [eta unsuccessful_round_internal bm].
Proof.
  move=> Hith Hlen.
  apply: functional_extensionality=> x.
  rewrite /unsuccessful_round_internal/BlockMap_records//=.
  rewrite fixlist_insert_rewrite //=.
  rewrite map_rcons filter_rcons //=.
  by rewrite Bool.andb_false_r //=.
Qed.

Lemma unsuccessful_round_internal_insert_honest bm bl hr :
    fixlist_is_top_heavy bm ->
    [length bm] < BlockHistory_size ->
    [eta unsuccessful_round_internal [bm <- (bl, (false, hr))]] =
    predI [eta unsuccessful_round_internal bm]   (fun x=> ~~ (nat_of_ord hr == x)).
Proof.
  move=> Hith Hlen.
  apply: functional_extensionality=> x.
  rewrite /unsuccessful_round_internal/BlockMap_records//=.
  rewrite -!length_sizeP !size_filter.
  rewrite fixlist_insert_rewrite //=.
  rewrite map_rcons count_rcons //=.
  rewrite Bool.andb_true_r //=.
  case: (_ == x) => //=.
  have Haddn y : (y + 1 == 0) = false. by case: y => //=.
  by rewrite Haddn Bool.andb_false_r.
  by rewrite addn0 Bool.andb_true_r.
Qed.


Lemma successful_round_internal_insert_adversarial bm bl hr round :
    fixlist_is_top_heavy bm ->
    [length bm] < BlockHistory_size ->
    successful_round_internal [bm <- (bl, (true, hr))] round  = 
    successful_round_internal bm round.
Proof.
  move=> Hith Hlen.
  rewrite /successful_round_internal/BlockMap_records//=.
  rewrite fixlist_insert_rewrite //=.
  rewrite map_rcons filter_rcons //=.
  by rewrite Bool.andb_false_r //=.
Qed.

Lemma successful_round_internal_insert_honest bm bl hr round :
    fixlist_is_top_heavy bm ->
    [length bm] < BlockHistory_size ->
    successful_round_internal [bm <- (bl, (false, hr))] round  = 
    successful_round_internal bm round ||  (nat_of_ord hr == round).
Proof.
  move=> Hith Hlen.
  rewrite /successful_round_internal/BlockMap_records//=.
  rewrite fixlist_insert_rewrite //=.
  rewrite map_rcons filter_rcons //=.
  rewrite Bool.andb_true_r //=.
  case: (_ == round) => //=.
    by rewrite length_rcons //= ltn0Sn Bool.orb_true_r.
  by rewrite  Bool.orb_false_r.
Qed.






Lemma no_bounded_successful_rounds'_internal_insert_adversarial bm hr s r bl :
  [length bm] < BlockHistory_size  ->
  fixlist_is_top_heavy bm ->
  no_bounded_successful_rounds'_internal
    (fixlist_insert bm ((bl), (true, hr))) s r =
  no_bounded_successful_rounds'_internal
    bm s r.
Proof.
  move=> Hlen Hith.
  rewrite /no_bounded_successful_rounds'_internal/bounded_successful_round_internal//=.
  rewrite unsuccessful_round_internal_insert_adversarial //=.
  rewrite -!length_sizeP.
  rewrite !size_filter.
  apply: eq_count.
  rewrite /eqfun => x .
  by rewrite successful_round_internal_insert_adversarial //=.
Qed.

Lemma all_neq_itoj hr x :
  (hr == x) ->
  all (fun x0 : nat => (hr) != x0) (itoj (x + 1 - delta) x) = true.
Proof.
  move=>/eqP ->; apply/allP => x'; rewrite mem_iota => /andP [].
  rewrite subnKC.
    by rewrite neq_ltn => Hxdltx' Hx'ltx; apply/orP; right.
  move: delta_valid;  case: delta => //= delta _ ; rewrite addn1 subSS.
  apply leq_subr.
Qed.





Lemma no_bounded_successful_rounds'_internal_insert_honest bm hr s r bl :
  [length bm] < BlockHistory_size  ->
  fixlist_is_top_heavy bm ->
    all (fun x : nat => x <= nat_of_ord hr) (itoj 0 r) ->
  no_bounded_successful_rounds'_internal
    (fixlist_insert bm ((bl), (false, hr))) s r =
  no_bounded_successful_rounds'_internal
    bm s r.
Proof.
  move=> Hlen Hith Hleq.
  rewrite /no_bounded_successful_rounds'_internal/bounded_successful_round_internal//=.
  rewrite -!length_sizeP !size_filter .
  apply: eq_in_count.
  rewrite /eqfun  => x .
  rewrite mem_iota => /andP [].
  case Hrlts: (r < s).
    move: (Hrlts) => /(ltn_addr 1); rewrite addn1 -subn_eq0 subSS => /eqP ->; rewrite addn0.
    by move=>/leq_ltn_trans H /H; rewrite ltnn.
  move/negP/negP:Hrlts; rewrite -leqNgt => Hrlts; rewrite subnKC //= => Hsltx Hxltr.
  rewrite unsuccessful_round_internal_insert_honest => //=.
  rewrite successful_round_internal_insert_honest => //=.
  rewrite all_predI.
  move/allP: Hleq => Hleq; move: (Hleq x); rewrite  mem_iota subnKC //=; clear Hleq .
  move=> Hleq; move: (Hleq Hxltr); clear Hleq => Hleq.

Admitted.






Lemma no_bounded_successful_rounds'_lim w s r :
  0 < delta ->
  delta <= s ->
  r <= s - delta ->
  bounded_successful_round w (s - delta) ->
                (no_bounded_successful_rounds' w r (s.+1 - delta))%nat =
               (no_bounded_successful_rounds' w r (s.+1 - 2 * delta) + 1)%nat.
Proof.
  move=> Hdlta0 Hdltas Hrbnd Hbound.
  rewrite subSn //=.
  rewrite no_bounded_successful_rounds'_lim_subd //=.
  rewrite -subSn //= .
  by rewrite -subnDA addnn -muln2 mulnC //=.
Qed.

Lemma no_bounded_successful_rounds_lim w s r :
  0 < delta ->
  delta <= s ->
  r <= s - delta ->
  ((no_bounded_successful_rounds' w r (s.+1 - 2 * delta)) + 1) < N_rounds.+1 ->
  bounded_successful_round w (s - delta) ->
  (nat_of_ord (no_bounded_successful_rounds w r
                                            (s.+1 - delta))%nat) =
  (nat_of_ord (no_bounded_successful_rounds w r
                                            (s.+1 - 2 * delta)) + 1)%nat.
Proof.
  move=> Hdlta0 Hdltas Hrbnd Hbound.
  rewrite /no_bounded_successful_rounds => Hbounded_succ.
  rewrite no_bounded_successful_rounds'_lim //= .
  move: [eta _ ].
  move: [eta _ ].
  move: (erefl _ ).
  move: (erefl _ ).
  rewrite {2 4}Hbound.
  move/ltn_weaken: (Hbound) => Hbound'.
  by rewrite {2 4}Hbound' => prf prf' H1 H2; rewrite /nat_of_ord //=.
Qed.



Lemma bounded_successful_round_init round :
  ~~  bounded_successful_round initWorld round .
Proof.
  rewrite /bounded_successful_round//=.
  rewrite negb_and; apply/orP; right.
  rewrite /successful_round/initWorld//=.
  rewrite /BlockMap_records/BlockMap_new//=.
    by move:
         (fixlist_empty_is_empty
            [finType of BlockMap_keytype * BlockMap_valuetype]
            BlockHistory_size);
    rewrite /fixlist_is_empty => /eqP -> //=.
Qed.

Lemma no_bounded_successful_rounds'_init r s :
  no_bounded_successful_rounds' initWorld r s = 0.
Proof.
  rewrite/no_bounded_successful_rounds'//=/initWorldAdoptionHistory //=.
  rewrite /itoj -length_sizeP size_filter;
  apply has_countPn; apply /hasPn => round Hvldround.
  by apply bounded_successful_round_init.
Qed.




Lemma no_bounded_successful_rounds_init r s :
  nat_of_ord (no_bounded_successful_rounds initWorld r s) = 0.
Proof.
  by rewrite/no_bounded_successful_rounds no_bounded_successful_rounds'_init //=.
Qed.






Definition no_bounded_uniquely_successful_rounds'
           (w : World) (from : nat) (to : nat) : nat :=
  length(filter
    (fun round => bounded_uniquely_successful_round w round)
    (itoj from to)).

Definition no_bounded_uniquely_successful_rounds
           (w: World) (from to : nat) : 'I_N_rounds :=
  let b := ((no_bounded_uniquely_successful_rounds' w from to) < N_rounds ) in
  (if b as b0
      return (((no_bounded_uniquely_successful_rounds' w from to) < N_rounds ) =
              b0 -> 'I_N_rounds)
      then fun H => Ordinal H
      else fun _ => Ordinal valid_N_rounds) (erefl b).





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
             (* root -> .. -> [b1] -> [b2] -> .... -> head*)
             (* block 1 was hashed first *) (r1 < r2),
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

Lemma honest_activation_simplify w' addr :
  honest_activation [w'.state] = Some addr ->
  nat_of_ord [[w'.state].#active] = nat_of_ord addr.
Proof.
  rewrite /honest_activation.
  case: w'=> [ wgs wtp wif wmp whsh wblh wch wadvm wadvtx whontx wadopt ]//=.
  case: wgs => [gls ga gca gcr].
  move: (erefl _).
  case: {2 3 }(gca < n_max_actors)%nat => //= prf'.
  by case: ((tnth _ _).2) => //= [] [] <- //=.
Qed.

Lemma actor_n_is_honestP w r : forall prf,
    actor_n_is_honest w r =
    ~~ actor_n_is_corrupt w (Ordinal (n:=n_max_actors) (m:=r) prf).
Proof.
  move=> prf.
  rewrite /actor_n_is_honest; move: (erefl _).
  case Hltn: {2 3}(r < n_max_actors)%nat => //= prf' .
  by rewrite (proof_irrelevance _ prf' prf).
  move: Hltn.
  by rewrite {1}prf.
Qed.




Lemma local_state_base_nth addr : tnth initLocalStates addr = (initLocalState, false).
Proof.
  rewrite (tnth_nth (initLocalState, false)).
  rewrite /initLocalStates.
  destruct addr as [m Hm].
  rewrite /tnth/ncons/ssrnat.iter//=. move: m Hm.
  elim n_max_actors => //=.
  move=> n IHn m .
  case m => //=.
Qed.


Definition honest_actor_has_chain_at_round w addr c r : bool := 
   (has
      (* there is a record *)
      (fun pr => 
         let: (rec_chain, rec_round, rec_actr)  := pr in 
         [&&
            (* of the block adopting/broadcasting the chain *)
            (rec_chain  == c),
          (* at round r or earlier *)
          (nat_of_ord rec_round <= r)%nat &
          (* by the actor *) 
          (nat_of_ord rec_actr == addr) ])
      (fixlist_unwrap (world_adoption_history w))
   )
.

Definition actor_n_has_chain_length_at_round_internal
           (ah: fixlist [eqType of BlockChain * 'I_N_rounds * 'I_n_max_actors] (n_max_actors * N_rounds))
           l addr r : bool :=
   (has
      (* there is a record *)
      (fun pr => 
         let: (rec_chain, rec_round, rec_actr)  := pr in 
         [&&
          (* of the block adopting/broadcasting the chain *)
          (fixlist_length rec_chain  == l),
          (* at round r *)
          (eq_op ( rec_round) ( r)) &
          (* by the actor *) 
          (nat_of_ord rec_actr == addr) ])
      (fixlist_unwrap ah)
   )
   ||
   (* or - implicit in the starting conditions, every actor has a chain length of 0 at round 0 *)
   ((eq_op (nat_of_ord r) 0%nat)%nat && (eq_op l 0)%nat).




Definition actor_n_has_chain_length_at_round w l addr r : bool :=
   (has
      (* there is a record *)
      (fun pr => 
         let: (rec_chain, rec_round, rec_actr)  := pr in 
         [&&
          (* of the block adopting/broadcasting the chain *)
          (fixlist_length rec_chain  == l),
          (* at round r *)
          (eq_op ( rec_round) ( r)) &
          (* by the actor *) 
          (nat_of_ord rec_actr == addr) ])
      (fixlist_unwrap (world_adoption_history w))
   )
   ||
   (* or - implicit in the starting conditions, every actor has a chain length of 0 at round 0 *)
   ((eq_op (nat_of_ord r) 0%nat)%nat && (eq_op l 0)%nat).

Lemma actor_n_has_chain_length_at_round_internalP w l addr r :
  actor_n_has_chain_length_at_round w l addr r =
  actor_n_has_chain_length_at_round_internal [w.adopt_history] l addr r.
Proof.
  by rewrite /actor_n_has_chain_length_at_round//=.
Qed.

Definition actor_n_has_chain_length_ge_at_round_internal
           (ah: fixlist [eqType of BlockChain * 'I_N_rounds * 'I_n_max_actors] (n_max_actors * N_rounds))
           l addr (r : 'I_N_rounds) : bool :=
   (has
      (* then there is a record *)
      (fun pr => 
         let: (rec_chain, rec_round, rec_actr)  := pr in 
         [&&
          (* of the block adopting/broadcasting a chain of at least length l *)
          (fixlist_length rec_chain >= l)%nat,
          (* at round r or earlier *)
          (nat_of_ord rec_round <= nat_of_ord r)%nat &
          (* by the actor *) 
          (nat_of_ord rec_actr == addr) ])
      (fixlist_unwrap ah)
   )
   ||
   (* or - implicit in the starting conditions, every actor has a chain length of 0 at round 0 *)
   ((eq_op l 0)%nat).




Definition actor_n_has_chain_length_ge_at_round w l addr (r : 'I_N_rounds) : bool :=
   (has
      (* then there is a record *)
      (fun pr => 
         let: (rec_chain, rec_round, rec_actr)  := pr in 
         [&&
          (* of the block adopting/broadcasting a chain of at least length l *)
          (fixlist_length rec_chain >= l)%nat,
          (* at round r or earlier *)
          (nat_of_ord rec_round <= nat_of_ord r)%nat &
          (* by the actor *) 
          (nat_of_ord rec_actr == addr) ])
      (fixlist_unwrap (world_adoption_history w))
   )
   ||
   (* or - implicit in the starting conditions, every actor has a chain length of 0 at round 0 *)
   ((eq_op l 0)%nat).


Lemma actor_n_has_chain_length_ge_at_round_internalP w l addr r :
  actor_n_has_chain_length_ge_at_round w l addr r =
  actor_n_has_chain_length_ge_at_round_internal [w.adopt_history] l addr r.
Proof.
  by rewrite /actor_n_has_chain_length_ge_at_round//=.
Qed.


Lemma no_bounded_successful_rounds'_eq0 : forall w r s, (s < r \/ (eq_op r s /\ eq_op r 0))%nat -> (no_bounded_successful_rounds' w r s) = 0%nat.
Proof.
  move=> w r s Hrs; rewrite /no_bounded_successful_rounds/no_bounded_successful_rounds'; apply/eqP => //=.
  destruct Hrs .
  by rewrite itoj_eq_0 => //=.
  by move: H => [/eqP -> /eqP ->] //=.
Qed.




Lemma no_bounded_successful_rounds_eq0 : forall w r s, (s < r \/ (eq_op r s ))%nat -> nat_of_ord (no_bounded_successful_rounds w r s) = 0%nat.
Proof.
  move=> w r s Hrs; rewrite /no_bounded_successful_rounds/no_bounded_successful_rounds'; apply/eqP => //=.
  destruct Hrs .
  by rewrite itoj_eq_0 => //=.
  rewrite /itoj.
  by move/eqP: (H) ->; rewrite subnn //=.
Qed.

Lemma actor_has_chain_length_generalize  w l o_addr s :
  actor_n_has_chain_length_at_round w l o_addr s ->
  actor_n_has_chain_length_ge_at_round w l o_addr s.
Proof.
  have blt0 (x:bool) : (x > 0)%nat = x. by case x.
  rewrite /actor_n_has_chain_length_ge_at_round/actor_n_has_chain_length_at_round !has_count.
  move=> /orP [ | /andP [/eqP Hseq  Hleq]]; last first.
  by apply/orP; right.
  move=> H; apply/orP; left; move: H.
  elim (fixlist_unwrap _) => //= [[[c r] addr] xs] IHn.
  rewrite add_lt0; move=>/orP; case => //=.
  by rewrite blt0; move=>/andP; case; [move=>/andP [/eqP -> /andP [/eqP -> /eqP ->]]] => _; rewrite !leqnn eq_refl.
  move=>/IHn Hbase.
  by rewrite add_lt0; apply/orP; right.
Qed.  



Lemma  actor_has_chain_length_weaken w l o_addr s l':
  (l' <= l)%nat ->
  actor_n_has_chain_length_ge_at_round w l o_addr s ->  
  actor_n_has_chain_length_ge_at_round w l' o_addr s.
Proof.
  rewrite /actor_n_has_chain_length_ge_at_round !has_count.
  rewrite leq_eqVlt; move=>/orP[/eqP -> |] //=.
  move=>  Hvalid.  
  induction (fixlist_unwrap _) => //=.
    by move=>/eqP Heq; move: Hvalid; rewrite Heq ltn0.
  move=> /orP [ | /eqP  Heq]; last first.
    by move: Hvalid; rewrite Heq ltn0.
  rewrite !add_lt0; move=>/orP; case => //= ;last first.
  move=> /(@or_introl _ (is_true (eq_op l 0)%nat))/orP/IHl0 => /orP [ Hlt |  Hleq0]; last first.
    by apply/orP; right.
    by apply/orP; left; apply/orP; right.
  move=>/andP [ Hgt0  Hlt0] //=.
  apply/orP.
  left .
  apply/orP; left.
  apply/andP;split.
  move: Hgt0.
  have bool_gt0 (b : bool) : (0 < b)%nat = b. by case b.
  move: a => [[b r] a].
  rewrite !bool_gt0 //=.
  move=>/andP [l_leq /andP [rs eq_addr]].
  apply/andP; split; [|apply/andP] => //=.
  have Hlt_trans x y z : (x <= y)%nat -> (y <= z)%nat  -> (x <= z)%nat.
    by move=>/leq_trans Himpl; move=> /Himpl.
  by apply (Hlt_trans l' l); [apply ltnW | ] .
  move: Hlt0.
  rewrite leq_eqVlt ; move=>/orP[/eqP |] //=.
Qed.


Definition world_executed_to_max_round w :=
  foldl (fun acc x =>
           let: (rec_chain, rec_round, rec_actr) := x in
           max (nat_of_ord rec_round) acc) 0%nat (fixlist_unwrap (world_adoption_history w)).


Definition world_executed_to_round w r : bool :=
  (r < (global_current_round (world_global_state w)) )%nat.


 
Definition honest_message_has_chain_length l (msg: Message)  :=
  match msg with
    (* selective messages are only sent by parties with malicious intentions *)
    | MulticastMsg _ chain =>  false
    | BroadcastMsg chain =>  fixlist_length chain == l
  end.

Definition honest_message_has_chain_length_ge l (msg: Message)  :=
  match msg with
    (* selective messages are only sent by parties with malicious intentions *)
    | MulticastMsg _ chain =>  false
    | BroadcastMsg chain =>  l <= fixlist_length chain 
  end.

Definition message_pool_contains_chain_of_length (ls : MessagePool) l :=
  has (honest_message_has_chain_length l) (fixlist_unwrap ls).

Definition message_pool_contains_chain_ge_of_length (ls : MessagePool) l :=
  has (honest_message_has_chain_length_ge l) (fixlist_unwrap ls).


