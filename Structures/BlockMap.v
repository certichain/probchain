
From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype fintype choice ssrfun seq path.

From mathcomp.ssreflect
Require Import tuple.


From Probchain
Require Import BlockChain FixedMap FixedList Parameters.

Set Implicit Arguments.


Definition BlockMap_keytype := [eqType of Block].
Definition BlockMap_valuetype := [eqType of (bool * (ordinal N_rounds) )].
Definition BlockMap := fixmap BlockMap_keytype BlockMap_valuetype  BlockHistory_size.

Definition BlockMap_new : BlockMap := fixmap_empty BlockMap_keytype BlockMap_valuetype BlockHistory_size.


Definition BlockMap_find (bl : Block) (map : BlockMap) : option BlockMap_valuetype := 
    fixmap_find bl map.

Definition BlockMap_blocks (bmap : BlockMap) : seq (bool * nat) :=
    map (fun pair => let: (b, or) := pair in (b, nat_of_ord or)) (fixlist_unwrap (fixmap_value bmap)).

Definition BlockMap_put_honest (bl : Block) (round: (ordinal N_rounds)) (map: BlockMap) :=
    fixmap_put (bl) (false, round) map.
        
Definition BlockMap_put_adversarial (bl : Block) (round : (ordinal N_rounds)) (map: BlockMap):=
    fixmap_put (bl) (true, round) map.


Definition BlockMap_put_honest_on_success (o_bl : option Block) (round: (ordinal N_rounds)) (map: BlockMap) :=
    match o_bl with
        | Some (bl) => fixmap_put (bl) (false, round) map
        | None => map
    end.        

Definition BlockMap_put_adversarial_on_success (o_bl : option Block) (round: (ordinal N_rounds)) (map: BlockMap) :=
    match o_bl with
        | Some (bl) => fixmap_put (bl) (true, round) map
        | None => map
    end.        



  Definition BlockMap_prod (m : BlockMap) := finmap_prod m.
  Definition prod_BlockMap pair : BlockMap := prod_finmap pair.

  Lemma BlockMap_cancel : cancel BlockMap_prod prod_BlockMap.
  Proof.
    by case.
  Qed.


  Definition BlockMap_eqMixin  :=
  CanEqMixin BlockMap_cancel.
  Canonical BlockMap_eqType :=
  Eval hnf in EqType BlockMap BlockMap_eqMixin.


  Definition BlockMap_choiceMixin  :=
  CanChoiceMixin BlockMap_cancel.
  Canonical BlockMap_choiceType :=
  Eval hnf in ChoiceType BlockMap BlockMap_choiceMixin.

  Definition BlockMap_countMixin :=
  CanCountMixin BlockMap_cancel.
  Canonical BlockMap_countType :=
  Eval hnf in CountType BlockMap BlockMap_countMixin.
  
  Definition BlockMap_finMixin :=
  CanFinMixin BlockMap_cancel.
  Canonical BlockMap_finType :=
  Eval hnf in FinType BlockMap BlockMap_finMixin.
