From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype fintype choice ssrfun seq path.

From mathcomp.ssreflect
Require Import tuple.

Set Implicit Arguments.


From Probchain
Require Import BlockChain InvMisc FixedList FixedMap Parameters.


Definition oraclestate_keytype := [eqType of ([eqType of ([eqType of Nonce] * [eqType of Hashed] * [eqType of BlockRecord])] )%type].

Definition OracleState := fixmap  oraclestate_keytype  [eqType of Hashed] oraclestate_size.

Definition oraclestate_new : OracleState := fixmap_empty oraclestate_keytype [eqType of Hashed] oraclestate_size.


Definition oraclestate_find k (m : OracleState) := fixmap_find k m.



Definition oraclestate_put (k: oraclestate_keytype) (v : Hashed) (m: OracleState) : OracleState :=
  fixmap_put k v m.


Canonical oraclestate_of_eqType := Eval hnf in [eqType of (OracleState)].
Canonical oraclestate_of_choiceType := Eval hnf in [choiceType of (OracleState)].
Canonical oraclestate_of_countType := Eval hnf in [countType of (OracleState)].
Canonical oraclestate_of_finType := Eval hnf in [finType of (OracleState)].



