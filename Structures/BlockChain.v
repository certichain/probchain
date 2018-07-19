From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq path.

(* To ensure that all blocks are unqiue, each block contains a random nonce *)
Definition Nonce := nat.
(* Hashed can not be a parameter, as it has to be comparable to a numerical T *)
Definition Hashed := nat.
(* Simmilarly, Addr must be an index into the honest actors, thus not a parameter*)
Definition Addr := nat.


Parameter Transaction : eqType.
(* determines whether a transaction is valid or not with respect to another sequence of transactions*)
Parameter Transaction_valid : Transaction -> seq Transaction -> bool. 

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

Definition TransactionPool := seq (TransactionMessage).


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
    | TransactionDrop of nat
    (* used by both Honest Parties to mint blocks*)
    (* Hashed represents the return value of the random oracle if the block is new*)
    (* Nonce represents the nonce used to create the block*)
    (* Both parameters will be probabilistically generated *)
    | HonestMintBlock of (Hashed * Nonce)
    (* the adversary gets an additional parameter specifying which chain
       in it's pool it should mint onto *)
    | AdvMintBlock of (Hashed)
    (* Used to represent the adversary corrupting players - nat is an index into
       which player to corrupt*)
    | AdvCorrupt of Addr
    (* used by adversary parties to broadcast chains - nat is an index into 
       the adversaries local blockchain pool*)
    | AdvBroadcast of (list Addr)
    (* Used by adversary parties to create transactions at any round *)
    | AdvTransactionGen of ((list Addr))
    .


Record Block := Bl {
  block_nonce: Nonce;
  block_link: Hashed;
  block_records: seq Transaction;
  block_proof_of_work: nat;
  
  (* extra information - can't be kept on block, as it may be modified by the adversary*)
  (* block_is_adversarial: bool; *)
  (* block_hash_round: nat; *)
}.





Definition BlockChain := seq Block.
(* converts a blockchain into a transaction sequence *)
Definition BlockChain_unwrap (b : BlockChain) := flatten (map (fun bchain => block_records bchain)  b) .

Parameter BlockChain_compare_lt : BlockChain -> BlockChain -> bool.

Inductive Message := 
  | MulticastMsg (addr : seq Addr) (bc : BlockChain)  
  | BroadcastMsg (bc : BlockChain).

Definition MessagePool := seq Message.


