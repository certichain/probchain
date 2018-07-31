From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype fintype choice ssrfun seq path.

From mathcomp.ssreflect
Require Import tuple.

From Probchain
Require Import FixedList Parameters.
Set Implicit Arguments.


(* To ensure that all blocks are unqiue, each block contains a random nonce *)
Definition Nonce := ordinal_finType (Hash_value.+1).
(* Hashed can not be a parameter, as it has to be comparable to a numerical T *)
Definition Hashed := ordinal_finType (Hash_value.+1).
(* Simmilarly, Addr must be an index into the honest actors, thus not a parameter*)
Definition Addr := ordinal (n_max_actors + 2).

Canonical nonce_of_eqType := Eval hnf in [eqType of Nonce].
Canonical nonce_of_choiceType := Eval hnf in [choiceType of Nonce].
Canonical nonce_of_countType := Eval hnf in [countType of Nonce].
Canonical nonce_of_finType := Eval hnf in [finType of Nonce].

Canonical hashed_of_eqType := Eval hnf in [eqType of Hashed].
Canonical hashed_of_choiceType := Eval hnf in [choiceType of Hashed].
Canonical hashed_of_countType := Eval hnf in [countType of Hashed].
Canonical hashed_of_finType := Eval hnf in [finType of Hashed].

Canonical addr_of_eqType := Eval hnf in [eqType of Addr].
Canonical addr_of_choiceType := Eval hnf in [choiceType of Addr].
Canonical addr_of_countType := Eval hnf in [countType of Addr].
Canonical addr_of_finType := Eval hnf in [finType of Addr].




Definition validate_transactions (xs : seq Transaction) : bool :=
  match xs with 
    | [::] => true (* Vacously true *)
    | h :: t => Transaction_valid h t (* Thank's to the consistency axiom *)
  end.

Inductive TransactionMessage := 
  | BroadcastTransaction of Transaction
  | MulticastTransaction of (Transaction * (fixlist [eqType of Addr] n_max_actors)).

Definition transaction_message_sum (m : TransactionMessage) := match m with
    | MulticastTransaction (addr, bc) =>  inl (addr, bc)
    | BroadcastTransaction bc      => inr bc
    end.

Definition sum_transaction_message m := match m with
    | inl (addr, bc) => MulticastTransaction (addr, bc)
    | inr bc      => BroadcastTransaction bc
    end.
 
Lemma transaction_message_cancel : cancel transaction_message_sum sum_transaction_message.
Proof.
  case.
  by [].
  move=> [addr bc]  //=.
Qed.

Definition transaction_message_eqMixin :=
  CanEqMixin transaction_message_cancel.
Canonical transaction_message_eqType :=
  Eval hnf in EqType TransactionMessage transaction_message_eqMixin.

Definition transaction_message_choiceMixin :=
  CanChoiceMixin transaction_message_cancel.
Canonical transaction_message_choiceType :=
  Eval hnf in ChoiceType TransactionMessage transaction_message_choiceMixin.

Definition transaction_message_countMixin :=
  CanCountMixin transaction_message_cancel.
Canonical transaction_message_countType :=
  Eval hnf in CountType TransactionMessage transaction_message_countMixin.
  
Definition transaction_message_finMixin :=
  CanFinMixin transaction_message_cancel.
Canonical transaction_message_finType :=
  Eval hnf in FinType TransactionMessage transaction_message_finMixin.


Canonical transaction_of_eqType := Eval hnf in [eqType of Transaction].
Canonical transaction_of_choiceType := Eval hnf in [choiceType of Transaction].
Canonical transaction_of_countType := Eval hnf in [countType of Transaction].
Canonical transaction_of_finType := Eval hnf in [finType of Transaction].




Definition TransactionPool := fixlist [eqType of TransactionMessage] TransactionPool_length.
Definition initTransactionPool : TransactionPool := fixlist_empty [eqType of TransactionMessage] TransactionPool_length .


Definition BlockRecord := fixlist Transaction Transactions_per_block.
Definition initBlockRecord : BlockRecord := fixlist_empty Transaction Transactions_per_block.


Canonical transaction_pool_of_eqType := Eval hnf in [eqType of TransactionPool].
Canonical transaction_pool_of_choiceType := Eval hnf in [choiceType of TransactionPool].
Canonical transaction_pool_of_countType := Eval hnf in [countType of TransactionPool].
Canonical transaction_pool_of_finType := Eval hnf in [finType of TransactionPool].


Canonical block_record_of_eqType := Eval hnf in [eqType of BlockRecord].
Canonical block_record_of_choiceType := Eval hnf in [choiceType of BlockRecord].
Canonical block_record_of_countType := Eval hnf in [countType of BlockRecord].
Canonical block_record_of_finType := Eval hnf in [finType of BlockRecord].







(* RndGen will be passed down from the probabilistic component and used to simulate any probabilistic components *)
(* RndGen encodes the random/unknown aspects of the system 
  specifically, 
      - creating transaction
      - droppping transactions 
      - minting blocks
      - adversary corrupting
      - adversary broadcasting
          - *)
(* together with the restrictions imposed by world step, all valid
   sequences of actions can be considered *)
Inductive RndGen  := 
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


Record Block : Type := Bl {
  block_nonce: Nonce;
  block_link: Hashed;
  block_records: BlockRecord;
  block_proof_of_work: ordinal Maximum_proof_of_work;
  
  (* extra information - can't be kept on block, as it may be modified by the adversary*)
  (* block_is_adversarial: bool; *)
  (* block_hash_round: nat; *)
}.

Definition block_prod (b : Block) :=
  (block_nonce b, block_link b, block_records b, block_proof_of_work b).
Definition prod_block (product: (Nonce * Hashed * BlockRecord * (ordinal Maximum_proof_of_work))%type) : Block :=
  let (triple1, pow1) := product in
    let (tuple1, br1) := triple1 in
      let (n1, h1) := tuple1 in
        Bl n1 h1 br1 pow1.

 

Definition block_prod_enum := (prod_enum 
    (prod_finType (prod_finType [finType of Nonce] [finType of Hashed]) [finType of BlockRecord]) 
    [finType of (ordinal Maximum_proof_of_work)]).

Definition block_enum := map prod_block 
  block_prod_enum. 


Lemma block_cancel : cancel block_prod prod_block.
Proof.
  rewrite /cancel.
  move=> b.
  destruct b => //=.
Qed.

Definition block_eqMixin := CanEqMixin block_cancel.
Canonical block_eqType := Eval hnf in EqType Block block_eqMixin.

Definition block_choiceMixin := CanChoiceMixin block_cancel.
Canonical block_choiceType := Eval hnf in ChoiceType Block block_choiceMixin.
Definition block_countMixin := CanCountMixin block_cancel.
Canonical block_countType := Eval hnf in CountType Block block_countMixin.

Definition block_finMixin := CanFinMixin block_cancel.
Canonical block_finType := Eval hnf in FinType Block block_finMixin.

Canonical block_of_eqType := Eval hnf in [eqType of Block].
Canonical block_of_choiceType := Eval hnf in [choiceType of Block].
Canonical block_of_countType := Eval hnf in [countType of Block].
Canonical block_of_finType := Eval hnf in [finType of Block].



Definition BlockChain := fixlist [eqType of Block] Maximum_blockchain_length.
Definition initBlockChain := fixlist_empty [eqType of Block] Maximum_blockchain_length.
(* converts a blockchain into a transaction sequence *)

Canonical block_chain_of_eqType := Eval hnf in [eqType of BlockChain].
Canonical block_chain_of_choiceType := Eval hnf in [choiceType of BlockChain].
Canonical block_chain_of_countType := Eval hnf in [countType of BlockChain].
Canonical block_chain_of_finType := Eval hnf in [finType of BlockChain].




Definition BlockChain_unwrap (b : BlockChain) := flatten (map (fun block => fixlist_unwrap (block_records block)) (fixlist_unwrap b)).


Inductive Message := 
  | MulticastMsg (addr : fixlist [eqType of Addr] n_max_actors ) (bc : BlockChain)  
  | BroadcastMsg (bc : BlockChain).





Definition message_eq (m1 m2 : Message) :=
  match m1, m2 with 
    | MulticastMsg a1 b1 , MulticastMsg a2 b2 => (a1 == a2) && (b1 == b2)
    | BroadcastMsg b1, BroadcastMsg b2 => b1 == b2
    | _, _ => false
    end.


Lemma message_eqP : Equality.axiom message_eq.
Proof.
  move=> m1 m2.
  case m1 eqn: Hm1, m2 eqn: Hm2 => //=.
    case (_ && _) eqn: H; move:H => /andP H; constructor.
      by destruct H; move: H H0 => /eqP <- /eqP <-.
    move=> H0.
    move: H.
    injection H0 => <- <-.
    move=> H.
    by apply H.

  by constructor.
  by constructor.
  case (_ == _) eqn: H; constructor.
  by move: H => /eqP <-.
  rewrite /not.
  move=> H0.
  move: H => /eqP.
  injection H0.
  move=> <- H.
  by apply H.
Qed.

Definition message_eqMixin := @EqMixin Message message_eq message_eqP.
Canonical message_eqType := Eval hnf in EqType Message message_eqMixin.

Definition message_sum (m : Message) := match m with
    | MulticastMsg addr bc => inl (addr, bc)
    | BroadcastMsg bc      => inr bc
    end.

Definition sum_message m := match m with
    | inl (addr, bc) => MulticastMsg addr bc
    | inr bc      => BroadcastMsg bc
    end.
    About sum_message.

Lemma message_cancel : cancel message_sum sum_message.
Proof.
  rewrite /cancel.
  move=> m.
  destruct m => //=.
Qed.

Definition message_choiceMixin :=
  CanChoiceMixin message_cancel.
Canonical message_choiceType :=
  Eval hnf in ChoiceType Message message_choiceMixin.
Definition message_countMixin :=
  CanCountMixin message_cancel.
Canonical message_countType :=
  Eval hnf in CountType Message message_countMixin.
Definition message_finMixin :=
  CanFinMixin message_cancel.
Canonical message_finType :=
  Eval hnf in FinType Message message_finMixin.

Canonical message_of_eqType := Eval hnf in [eqType of Message].
Canonical message_of_choiceType := Eval hnf in [choiceType of Message].
Canonical message_of_countType := Eval hnf in [countType of Message].
Canonical message_of_finType := Eval hnf in [finType of Message].




Definition MessagePool := fixlist [eqType of Message] MessagePool_length.
Definition initMessagePool := fixlist_empty [eqType of Message] MessagePool_length.

Canonical message_pool_of_eqType := Eval hnf in [eqType of MessagePool].
Canonical message_pool_of_choiceType := Eval hnf in [choiceType of MessagePool].
Canonical message_pool_of_countType := Eval hnf in [countType of MessagePool].
Canonical message_pool_of_finType := Eval hnf in [finType of MessagePool].



Parameter BlockChain_compare_lt : BlockChain -> BlockChain -> bool.
