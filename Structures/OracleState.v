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


  Definition oraclestate_prod (m : OracleState) := finmap_prod m.
  Definition prod_oraclestate pair : OracleState := prod_finmap pair.

  Lemma oraclestate_cancel : cancel oraclestate_prod prod_oraclestate.
  Proof.
    by case.
  Qed.


  Definition oraclestate_eqMixin  :=
  CanEqMixin oraclestate_cancel.
  Canonical oraclestate_eqType :=
  Eval hnf in EqType OracleState oraclestate_eqMixin.


  Definition oraclestate_choiceMixin  :=
  CanChoiceMixin oraclestate_cancel.
  Canonical oraclestate_choiceType :=
  Eval hnf in ChoiceType OracleState oraclestate_choiceMixin.

  Definition oraclestate_countMixin :=
  CanCountMixin oraclestate_cancel.
  Canonical oraclestate_countType :=
  Eval hnf in CountType OracleState oraclestate_countMixin.
  
  Definition oraclestate_finMixin :=
  CanFinMixin oraclestate_cancel.
  Canonical oraclestate_finType :=
  Eval hnf in FinType OracleState oraclestate_finMixin.


Canonical oraclestate_of_eqType := Eval hnf in [eqType of (OracleState)].
Canonical oraclestate_of_choiceType := Eval hnf in [choiceType of (OracleState)].
Canonical oraclestate_of_countType := Eval hnf in [countType of (OracleState)].
Canonical oraclestate_of_finType := Eval hnf in [finType of (OracleState)].

