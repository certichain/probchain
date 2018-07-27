
From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype fintype choice ssrfun seq path.

From mathcomp.ssreflect
Require Import tuple.


From Probchain
Require Import BlockChain FixedMap FixedList Parameters.

Set Implicit Arguments.


Definition blockmap_keytype := [eqType of Block].
Definition blockmap_valuetype := [eqType of (bool * (ordinal N_rounds) )].
Definition BlockMap := fixmap blockmap_keytype blockmap_valuetype  BlockHistory_size.

Definition blockmap_new : BlockMap := fixmap_empty blockmap_keytype blockmap_valuetype BlockHistory_size.


Definition blockmap_find (bl : Block) (map : BlockMap) : option blockmap_valuetype := 
    fixmap_find bl map.



Definition blockmap_put_honest (bl : Block) (round: (ordinal N_rounds)) (map: BlockMap) :=
    fixmap_put (bl) (false, round) map.
        
Definition blockmap_put_adversarial (bl : Block) (round : (ordinal N_rounds)) (map: BlockMap):=
    fixmap_put (bl) (true, round) map.


Definition blockmap_put_honest_on_success (o_bl : option Block) (round: (ordinal N_rounds)) (map: BlockMap) :=
    match o_bl with
        | Some (bl) => fixmap_put (bl) (false, round) map
        | None => map
    end.        

Definition blockmap_put_adversarial_on_success (o_bl : option Block) (round: (ordinal N_rounds)) (map: BlockMap) :=
    match o_bl with
        | Some (bl) => fixmap_put (bl) (true, round) map
        | None => map
    end.        



  Definition blockmap_prod (m : BlockMap) := finmap_prod m.
  Definition prod_blockmap pair : BlockMap := prod_finmap pair.

  Lemma blockmap_cancel : cancel blockmap_prod prod_blockmap.
  Proof.
    by case.
  Qed.


  Definition blockmap_eqMixin  :=
  CanEqMixin blockmap_cancel.
  Canonical blockmap_eqType :=
  Eval hnf in EqType BlockMap blockmap_eqMixin.


  Definition blockmap_choiceMixin  :=
  CanChoiceMixin blockmap_cancel.
  Canonical blockmap_choiceType :=
  Eval hnf in ChoiceType BlockMap blockmap_choiceMixin.

  Definition blockmap_countMixin :=
  CanCountMixin blockmap_cancel.
  Canonical blockmap_countType :=
  Eval hnf in CountType BlockMap blockmap_countMixin.
  
  Definition blockmap_finMixin :=
  CanFinMixin blockmap_cancel.
  Canonical blockmap_finType :=
  Eval hnf in FinType BlockMap blockmap_finMixin.
