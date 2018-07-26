
From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype fintype choice ssrfun seq path.

From mathcomp.ssreflect
Require Import tuple.


From Probchain
Require Import BlockChain FixedMap FixedList.

Set Implicit Arguments.

(* The Blockmap finite structure will be used to store all hashed blocks
    throughout the execution of the system. *)
(* As it is finite, we need to specify a size before execution. As such
   we will need to add constraints to ensure the system never exceeds
   the maximum number of blocks  *)
Parameter BlockHistory_size : nat.
(* Defines the number of rounds being considered *)
Parameter N_rounds : nat.


Definition blockmap_keytype := [eqType of Block].
Definition blockmap_valuetype := [eqType of (bool * (ordinal N_rounds) )].
Definition blockmap := fixmap blockmap_keytype blockmap_valuetype  BlockHistory_size.

Definition blockmap_new : blockmap := fixmap_empty blockmap_keytype blockmap_valuetype BlockHistory_size.


Definition blockmap_find (bl : Block) (map : blockmap) : option blockmap_valuetype := 
    fixmap_find bl map.



Definition blockmap_put_honest (bl : Block) (round: (ordinal N_rounds)) (map: blockmap) :=
    fixmap_put (bl) (false, round) map.
        
Definition blockmap_put_adversarial (bl : Block) (round : (ordinal N_rounds)) (map: blockmap):=
    fixmap_put (bl) (true, round) map.


Definition blockmap_put_honest_on_success (o_bl : option Block) (round: (ordinal N_rounds)) (map: blockmap) :=
    match o_bl with
        | Some (bl) => fixmap_put (bl) (false, round) map
        | None => map
    end.        

Definition blockmap_put_adversarial_on_success (o_bl : option Block) (round: (ordinal N_rounds)) (map: blockmap) :=
    match o_bl with
        | Some (bl) => fixmap_put (bl) (true, round) map
        | None => map
    end.        



  Definition blockmap_prod (m : blockmap) := finmap_prod m.
  Definition prod_blockmap pair : blockmap := prod_finmap pair.

  Lemma blockmap_cancel : cancel blockmap_prod prod_blockmap.
  Proof.
    by case.
  Qed.


  Definition blockmap_eqMixin  :=
  CanEqMixin blockmap_cancel.
  Canonical blockmap_eqType :=
  Eval hnf in EqType blockmap blockmap_eqMixin.


  Definition blockmap_choiceMixin  :=
  CanChoiceMixin blockmap_cancel.
  Canonical blockmap_choiceType :=
  Eval hnf in ChoiceType blockmap blockmap_choiceMixin.

  Definition blockmap_countMixin :=
  CanCountMixin blockmap_cancel.
  Canonical blockmap_countType :=
  Eval hnf in CountType blockmap blockmap_countMixin.
  
  Definition blockmap_finMixin :=
  CanFinMixin blockmap_cancel.
  Canonical blockmap_finType :=
  Eval hnf in FinType blockmap blockmap_finMixin.
