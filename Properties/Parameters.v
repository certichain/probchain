
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
Axiom valid_Maximum_blockchain_length : (0 < Maximum_blockchain_length).

Parameter MessagePool_length : nat.

Parameter Honest_TransactionPool_size: nat.
Parameter Honest_MessagePool_size: nat.

(* A range from 0 to n where n is the maximum hash value*)
Definition Hash_value := 2^Hash_length_k.
Lemma hash_valid_range : 0 < 2 ^ Hash_length_k.
    by rewrite expn_gt0; apply/orP; left.
Qed.





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
  ~~ (Transaction_valid x [::]) -> ~~ (Transaction_valid x ys).

Axiom transaction_reject_duplicate : forall (x : Transaction) (xs : seq Transaction),
    x \in xs -> ~~ (Transaction_valid x xs).


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



(*
    N_rounds * n_max_actors is a upper bound on the number of blocks hashed throughout the system.
*)
Lemma valid_N_rounds_mul_n_max_actors : 0 <  N_rounds * n_max_actors.
Proof.
  rewrite muln_gt0.
  apply /andP.
  split.
  exact valid_N_rounds.
  exact valid_n_max_actors.
Qed.  





Parameter oraclestate_size: nat.


Lemma ltNn {n} :  0 < n - 1 -> 0 < n.
Proof.
    rewrite subn_gt0.
    move => /(ltn_addr 1).
    rewrite addnS addn0 ltnS //=.
Qed.


(* Note: These quotas stand for the exclusive
upper bound on the number of messages an adversary can send (hence the - 1)
We do this, so that the max_value can be used as an ordinal *)
Parameter Adversary_max_Message_sends : nat.
Axiom valid_Adversary_max_Message_sends_strong :  0 < (Adversary_max_Message_sends - 1).
Definition valid_Adversary_max_Message_sends := ltNn valid_Adversary_max_Message_sends_strong .

Parameter Adversary_max_Transaction_sends : nat.
Axiom valid_Adversary_max_Transaction_sends_strong :  0 < (Adversary_max_Transaction_sends - 1).
Definition valid_Adversary_max_Transaction_sends := ltNn valid_Adversary_max_Transaction_sends_strong .


Parameter Honest_max_Transaction_sends : nat.
Parameter valid_Honest_max_Transaction_sends_strong : 0 < (Honest_max_Transaction_sends - 1).
Definition valid_Honest_max_Transaction_sends := ltNn valid_Honest_max_Transaction_sends_strong .



(* Ensure that an adversary can not overflow the buffers *)
Axiom valid_Message_BufferOverflow : Honest_MessagePool_size >  n_max_actors + Adversary_max_Message_sends.
(* Buffers are cleared every round.
   Each honest party sends at most 1 message per round
   Adversary sends at most Adversary_max_Message_sends per round
   Hence, provided Honest_messagePool_size > n_max_actors + Adversary_max_Message_sends,
   the buffer will not overflow
   *)

Axiom valid_Transaction_BufferOverflow : Honest_TransactionPool_size >  n_max_actors + Honest_max_Transaction_sends.

(* Ensure that the chain history is never overflowed*)
Axiom valid_ChainHistory_BufferOverflow : ChainHistory_size >  (n_max_actors + Adversary_max_Message_sends) * N_rounds.
(* 
    Each honest actor mints a block at most once a round, and thus outputs a chain at most once a round.
    An adversary outputs at most Adversary_max_Message_sends per round,
    thus even under the worst conditions, the maximum number of blocks that may be produced in a round is
    (n_max_actors + Adversary_max_message_sends) * N_max_rounds.
*)



(* Ensure that the blockmap is large enough to record every block that may be produced during execution *)
Axiom valid_BlockHistory_BufferOverflow : BlockHistory_size  > (n_max_actors + 1) * N_rounds.
(*
    Every party in the system is permitted 1 query to the hash function per round.
    As the number of parties are constant, irrespective of the proportion of corrupted nodes,
    the maximum number of blocks that may be hashed in a round is n_max_actors + 1.
    (+1) as the adversary can also hash blocks.
*)
Require Import Reals.
Parameter Epsilon_concentration_of_blocks : R.
Parameter Delta_honest_advantage : R.
Axiom valid_Delta_honest_advantage : Rle (Rdiv (INR t_max_corrupted) (INR (n_max_actors - t_max_corrupted))) (Rminus R1  Delta_honest_advantage).
Parameter Eta_block_to_round : R.
Parameter f_probability_honest_success : R.
