From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat seq ssrfun.




Definition Hashed := nat.
Definition Addr := nat.
Definition RndGen := nat.

Inductive Transaction := valid | invalid.

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


Inductive Message := 
  | NormalMsg (addr : Addr) (bc : BlockChain) 
  | BroadcastMsg (bc : BlockChain).



