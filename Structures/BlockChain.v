From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq path.



(* Hashed can not be a parameter, as it has to be comparable to a numerical T *)
Definition Hashed := nat.
(* Simmilarly, Addr must be an index into the honest actors, thus not a parameter*)
Definition Addr := nat.


Parameter Transaction : eqType.
(* determines whether a transaction is valid or not with respect to another sequence of transactions*)
Parameter Transaction_valid : Transaction -> seq Transaction -> bool. 

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
    (* used by both Honest and Adversary Parties to generate transactions *)
    | HonestTransactionGen of Transaction 
    | TransactionDrop of nat
    (* used by both Honest and Adversary Parties to mint blocks*)
    (* The nat represents the return value of the random oracle if the block is new*)
    (* this nat will be probabilistically analyzed*)
    | MintBlock of nat  
    (* Used to represent the adversary corrupting players - nat is an index into
       which player to corrupt*)
    | AdvCorrupt of Addr
    (* used by adversary parties to broadcast chains - nat is an index into 
       the adversaries local blockchain pool*)
    | AdvBroadcast of (nat * list nat)
    | AdvTransactionGen of (Transaction * (list Addr))
    | AdvTarget of  seq nat.


Record Block := Bl {
  block_link: Hashed;
  block_records: seq Transaction;
  block_proof_of_work: nat;
  
  (* extra information *)
  block_is_adversarial: bool;
  block_hash_round: nat;
}.



Definition BlockChain := seq Block.
(* converts a blockchain into a transaction sequence *)
Definition BlockChain_unwrap (b : BlockChain) := flatten (map (fun bchain => block_records bchain)  b) .


Inductive Message := 
  | MulticastMsg (addr : seq Addr) (bc : BlockChain)  
  | BroadcastMsg (bc : BlockChain).



