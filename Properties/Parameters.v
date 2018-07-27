
From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype fintype choice ssrfun seq path.

(* maximum number of nodes that can be corrupted *)
Parameter t_max_corrupted : nat.
(* number of actors in the system *)
Parameter n_max_actors : nat.
Axiom valid_n_max_actors : 0 < n_max_actors.

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
Axiom valid_Maximum_proof_of_work : 0 < Maximum_proof_of_work. 

(* To keep the structures finite, we have to constrain the maximum size of the blockchain*)
Parameter Maximum_blockchain_length : nat.

Parameter MessagePool_length : nat.

Parameter Honest_TransactionPool_size: nat.
Parameter Honest_MessagePool_size: nat.

(* A range from 0 to n where n is the maximum hash value*)
Definition Hash_value := 2^Hash_length_k.



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



(* The Blockmap finite structure will be used to store all hashed blocks
    throughout the execution of the system. *)
(* As it is finite, we need to specify a size before execution. As such
   we will need to add constraints to ensure the system never exceeds
   the maximum number of blocks  *)
Parameter BlockHistory_size : nat.

(* a finite structure will be used to store all chains seen 
    throughout the execution of the system. *)
(* As it is finite, we need to specify a size before execution. As such
   we will need to add constraints to ensure the system never exceeds
   the maximum number of chains *)
Parameter ChainHistory_size : nat.

(* Defines the number of rounds being considered *)
Parameter N_rounds : nat.
Axiom valid_N_rounds : 0 < N_rounds.


Parameter oraclestate_size: nat.