
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

Definition BlockMap_records (bmap : BlockMap) : seq (bool * nat) :=
    map (fun pair => let: (_,(b, or)) := pair in (b, nat_of_ord or)) (fixlist_unwrap  bmap).

Lemma BlockMap_records_roundP bmap : all (fun pair => let: (_, or) := pair in  or < N_rounds) (BlockMap_records (bmap)).
Proof.
  rewrite /BlockMap_records.
  elim: (fixlist_unwrap bmap) => //= pair' xs IHb.
  apply/andP; split.
  by move: pair' => [is_crpt [vl Hvl]] //=.
  by apply IHb.
Qed.

Definition BlockMap_blocks (bmap : BlockMap) : seq Block :=
    map (fun pair => let: (b,_) := pair in b) (fixlist_unwrap  bmap).

Definition BlockMap_pairs (bmap: BlockMap) : seq (Block * (bool * nat)) :=
    map (fun pair => let: (b',(b, or)) := pair in (b', (b, nat_of_ord or))) (fixlist_unwrap  bmap).


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



