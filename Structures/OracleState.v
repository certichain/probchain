From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype fintype choice ssrfun seq path.

From mathcomp.ssreflect
Require Import tuple.

Set Implicit Arguments.


From Probchain
Require Import BlockChain InvMisc FixedList FixedMap Parameters.


Definition oraclestate_keytype := [eqType of ([eqType of ([eqType of Hashed] * [eqType of BlockRecord])] * (ordinal Maximum_proof_of_work))%type].

Definition oraclestate := fixmap  oraclestate_keytype  [eqType of Hashed] oraclestate_size.

Definition oraclestate_new : oraclestate := fixmap_empty oraclestate_keytype [eqType of Hashed] oraclestate_size.


Definition oraclestate_find k (m : oraclestate) := fixmap_find k m.



Definition oraclestate_put (k: oraclestate_keytype) (v : Hashed) (m: oraclestate) :=
  fixmap_put k v m.


  Definition oraclestate_prod (m : oraclestate) := finmap_prod m.
  Definition prod_oraclestate pair : oraclestate := prod_finmap pair.

  Lemma oraclestate_cancel : cancel oraclestate_prod prod_oraclestate.
  Proof.
    by case.
  Qed.


  Definition oraclestate_eqMixin  :=
  CanEqMixin oraclestate_cancel.
  Canonical oraclestate_eqType :=
  Eval hnf in EqType oraclestate oraclestate_eqMixin.


  Definition oraclestate_choiceMixin  :=
  CanChoiceMixin oraclestate_cancel.
  Canonical oraclestate_choiceType :=
  Eval hnf in ChoiceType oraclestate oraclestate_choiceMixin.

  Definition oraclestate_countMixin :=
  CanCountMixin oraclestate_cancel.
  Canonical oraclestate_countType :=
  Eval hnf in CountType oraclestate oraclestate_countMixin.
  
  Definition oraclestate_finMixin :=
  CanFinMixin oraclestate_cancel.
  Canonical oraclestate_finType :=
  Eval hnf in FinType oraclestate oraclestate_finMixin.



