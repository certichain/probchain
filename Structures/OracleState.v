From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype fintype choice ssrfun seq path.

From mathcomp.ssreflect
Require Import tuple.

Set Implicit Arguments.


From Probchain
Require Import BlockChain InvMisc FixedList FixedMap.

Parameter OracleState_size: nat.

Definition OracleState_keytype := [eqType of ([eqType of ([eqType of Hashed] * [eqType of BlockRecord])] * (ordinal Maximum_proof_of_work))%type].
Definition OracleState := fixmap  OracleState_keytype  [eqType of Hashed] OracleState_size.

Definition OracleState_new : OracleState := fixmap_empty OracleState_keytype [eqType of Hashed] OracleState_size.


Definition OracleState_find k (m : OracleState) := fixmap_find k m.



Definition OracleState_put (k: OracleState_keytype) (v : Hashed) (m: OracleState) :=
  fixmap_put k v m.

