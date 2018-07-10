From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat seq ssrfun eqtype.
Require Import FMapAVL.

From Probchain
Require Import BlockChain InvBlock.

(* Rather than using a map, we will make our own record to 
   map blocks to their meta information - mainly to allow 
   for easy iteration*) 

Definition BlockMap := seq (Block * bool * nat).



Definition BlockMap_find (bl : Block) (map : BlockMap) : option (bool * nat):= 
    foldr
        (fun (new_pair : Block * bool * nat) (acc : option (bool * nat)) =>
            match acc with
                | Some val => acc
                | None =>
                    let: (bl', is_corrupt, round) := new_pair in
                    if (bl' == bl)
                        then Some (is_corrupt, round)
                        else None
                end)
        None
        (map).



Definition BlockMap_put_honest (bl : Block) (round: nat) (map: BlockMap) :=
    (bl, false, round) :: map.
        
Definition BlockMap_put_adversarial (bl : Block) (round : nat) (map: BlockMap):=
    (bl, true, round) :: map.

Definition BlockMap_new : BlockMap := nil.
