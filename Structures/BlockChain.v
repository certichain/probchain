From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype fintype choice ssrfun seq path.

From mathcomp.ssreflect
Require Import tuple.

From mathcomp.ssreflect
Require Import tuple.

From Probchain
Require Import FixedList.
Set Implicit Arguments.


(* maximum number of nodes that can be corrupted *)
Parameter t_max_corrupted : nat.
(* number of actors in the system *)
Parameter n_max_actors : nat.

(* represents the length of bitstrings used in hashes - note: no actual
   bitstrings are used, but rather emulated by a value in the ordinal 
   from 0 - 2^k-1*)
Parameter Hash_length_k : nat.

(* Represents the maximum number of transactions that may be inflight at a time *)
Parameter TransactionPool_length : nat.

Parameter Transaction : finType.
(* determines whether a transaction is valid or not with respect to another sequence of transactions*)
Parameter Transaction_valid : Transaction -> seq Transaction -> bool. 

(* a hash is valid iff hash(block) < T*)
Parameter T_Hashing_Difficulty : nat.
(* delay between activation and success *)
Parameter delta : nat.

Parameter Transactions_per_block : nat.

Parameter Maximum_proof_of_work : nat.

(* To keep the structures finite, we have to constrain the maximum size of the blockchain*)
Parameter Maximum_blockchain_length : nat.

Parameter MessagePool_length : nat.


(* A range from 0 to n where n is the maximum hash value*)
Definition Hash_value := 2^Hash_length_k.

(* To ensure that all blocks are unqiue, each block contains a random nonce *)
Definition Nonce := ordinal_finType Hash_value.
(* Hashed can not be a parameter, as it has to be comparable to a numerical T *)
Definition Hashed := ordinal_finType Hash_value.
(* Simmilarly, Addr must be an index into the honest actors, thus not a parameter*)
Definition Addr := ordinal n_max_actors.


(* Ensures that valid sequences of transactions are well formed *)
Axiom transaction_valid_consistent : forall (x y : Transaction) (ys : seq Transaction), 
    Transaction_valid x (y :: ys) -> Transaction_valid y ys.

(*
  Transactions can be wrong for two reasons:
    1. signed incorrectly
    2. conflict with prior records
  If signed incorrectly:
    1. a transaction would be invalid even with an empty list of transactions
    2. the transaction would be invalid for any at all
*)
Axiom transaction_inherently_invalid : forall (x : Transaction) (ys : seq Transaction), 
  not (Transaction_valid x [::]) -> not (Transaction_valid x ys).

Definition validate_transactions (xs : seq Transaction) : bool :=
  match xs with 
    | [::] => true (* Vacously true *)
    | h :: t => Transaction_valid h t (* Thank's to the consistency axiom *)
  end.

Inductive TransactionMessage := 
  | BroadcastTransaction of Transaction
  | MulticastTransaction of (Transaction * (seq Addr)).

Definition TransactionPool := fixlist Transaction TransactionPool_length.
Definition initTransactionPool : TransactionPool := fixlist_empty Transaction TransactionPool_length .


Definition BlockRecord := fixlist Transaction Transactions_per_block.
Definition initBlockRecord : BlockRecord := fixlist_empty Transaction Transactions_per_block.


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

Definition block_eq (b : Block) (o : Block) := (block_prod b) == (block_prod o).
Lemma block_eqP : Equality.axiom block_eq.
Proof.
  move=> b1 b2.
  rewrite /block_eq /block_prod.
  destruct b1; destruct b2.
  case (_ == _) eqn: H.
    move:H => //= /eqP H //=.
    injection (H) => <- <- <- <-; constructor => //=.

  move: H => //= /eqP H.
  constructor.
  rewrite /not.
  move=> H0.
  move: H.
  injection H0.
  move=> <- <- <- <- .
  rewrite /not => H.
  case H => //=.
Qed.
  
Definition block_eqMixin := @EqMixin Block block_eq block_eqP.
Canonical block_eqType := Eval hnf in EqType Block block_eqMixin.

Definition block_prod_enum := (prod_enum 
    (prod_finType (prod_finType [finType of Nonce] [finType of Hashed]) [finType of BlockRecord]) 
    [finType of (ordinal Maximum_proof_of_work)]).

Definition block_enum := map prod_block 
  block_prod_enum. 

Lemma block_enumP : Finite.axiom block_enum.
Proof.
  rewrite /Finite.axiom.
  move=>  b.
  rewrite /block_enum => //=.
  rewrite /block_prod_enum => //=.
  destruct b.
  rewrite <-prod_enumP with (T1 := (prod_finType (prod_finType [finType of 'I_Hash_value] [finType of 'I_Hash_value])) [finType of BlockRecord]) 
                            (T2 := [finType of 'I_Maximum_proof_of_work])
                            (x := (block_nonce0, block_link0, block_records0, block_proof_of_work0)).
  induction (prod_enum _) => //=.
  symmetry.
  case (_ == _) eqn:H => //=.
  destruct a as [[[a_n a_l] a_r] a_p].
  move: H=> /eqP H.
  injection H => -> -> -> ->.
  rewrite -IHl => //=.
  have H' : ({|
  block_nonce := block_nonce0;
  block_link := block_link0;
  block_records := block_records0;
  block_proof_of_work := block_proof_of_work0 |} ==
  {|
  block_nonce := block_nonce0;
  block_link := block_link0;
  block_records := block_records0;
  block_proof_of_work := block_proof_of_work0 |}) = true.
  by apply /eqP.
  by rewrite H'.
  rewrite add0n.
  destruct a as [[[a_n a_l] a_r] a_p] => //=.
  move: H => /eqP H.
  rewrite /not in H.
  have H': ({|
  block_nonce := a_n;
  block_link := a_l;
  block_records := a_r;
  block_proof_of_work := a_p |} ==
  {|
  block_nonce := block_nonce0;
  block_link := block_link0;
  block_records := block_records0;
  block_proof_of_work := block_proof_of_work0 |}) = false.
  apply /eqP => H0.
  move: H.
  injection H0.
  move=> <- <- <- <-.
  move=> H.
  by apply H.
  rewrite H' => //=.
Qed. 



Lemma block_cancel : cancel block_prod prod_block.
Proof.
  rewrite /cancel.
  move=> b.
  destruct b => //=.
Qed.

Definition block_choiceMixin := CanChoiceMixin block_cancel.
Canonical block_choiceType := Eval hnf in ChoiceType Block block_choiceMixin.
Definition block_countMixin := CanCountMixin block_cancel.
Canonical block_countType := Eval hnf in CountType Block block_countMixin.

Definition block_finMixin := Finite.Mixin block_countMixin block_enumP.
Canonical block_finType := Eval hnf in FinType Block block_finMixin.





Definition BlockChain := fixlist [eqType of Block] Maximum_blockchain_length.
Definition initBlockChain := fixlist_empty [eqType of Block] Maximum_blockchain_length.
(* converts a blockchain into a transaction sequence *)




Definition BlockChain_unwrap (b : BlockChain) := flatten (map (fun block => fixlist_unwrap (block_records block)) (fixlist_unwrap b)).

Parameter BlockChain_compare_lt : BlockChain -> BlockChain -> bool.

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

About sum_enum.
(*
  TODO : finitize message
*)
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




Definition MessagePool := fixlist [eqType of Message] MessagePool_length.


