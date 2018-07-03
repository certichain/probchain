
From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq path.





(* Hashed can not be a paremter, as it has to be comparable to a numerical T *)
Definition Hashed := nat.
(* Simmilarly, Addr must be an index into the honest actors, thus not a parameter*)
Definition Addr := nat.
(* RndGen will be passed down from the probabilistic component and used to simulate any probabilistic components *)
Definition RndGen := nat.

Parameter Transaction : eqType.
(* determines whether a transaction is valid or not with respect to another sequence of transactions*)
Parameter Transaction_valid : Transaction -> seq Transaction -> bool. 

Definition TransactionPool := seq (Transaction * (seq Addr)).

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
  | NormalMsg (addr : Addr) (bc : BlockChain)  
  | BroadcastMsg (bc : BlockChain).



