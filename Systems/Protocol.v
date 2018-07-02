
Require Import FMapAVL.
Require Import Coq.Structures.OrderedTypeEx.
Require Import OrderedType.
(* Implementation of Bitcoin Protocol *)
(* Does not compile yet - as probability issues have not been resolved. *)
From Probchain
Require Import BlockChain OracleState.

From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat seq ssrfun.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.



Variable hash : 
RndGen -> (Hashed * seq Transaction * nat) -> OracleState -> (OracleState * Hashed).



Record Adversary := Advrs {
  adversary_local_transaction_pool: seq Transaction;
  adversary_local_message_pool: seq BlockChain;
  adversary_proof_of_work: nat;
}.

Record LocalState := LclSt {
  honest_current_chain: BlockChain;
  honest_local_transaction_pool: seq Transaction;
  honest_local_message_pool: seq BlockChain;
  honest_proof_of_work: nat;
}.


Definition GlobalState := ((seq (LocalState * bool)) * Addr * nat)%type.


Definition MessagePool := seq Message.

Record World := mkWorld {
  world_global_state: GlobalState;
  world_transaction_pool: TransactionPool;
  world_inflight_pool: MessagePool;
  world_message_pool: MessagePool;
  world_hash: RndGen -> (Hashed * seq Transaction * nat) -> OracleState -> (OracleState * Hashed)
}.
