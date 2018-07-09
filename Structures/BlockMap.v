From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat seq ssrfun eqtype.
Require Import FMapAVL.

From Probchain
Require Import BlockChain InvBlock.

Module M := FMapAVL.Make(Block_as_OT).
Definition BlockMap := M.t (bool * nat).


Definition BlockMap_new : BlockMap.
Proof.
  (* TODO(Kiran): complete this proof *) 
 Qed.


Definition BlockMap_find k (b : BlockMap) := M.find k b.


(* Used to record additional state of blocks *)
(* The extra logic is so that an adversary can not change an honest block into an adversarial block by hashing it*)
Definition BlockMap_put  block (block_info: bool * nat) (b : BlockMap) := 
    let (new_is_adversarial, last_round) := block_info in
        if new_is_adversarial 
            then
            (* if it is adversarial, check if the last entry was adversarial *)
                match BlockMap_find block b with
                    | None => M.add block block_info b
                    | Some old_block_info => 
                            let (old_is_adversarial, _) := old_block_info in
                                if old_is_adversarial 
                                    (* if the old one was also adversarial, then update *)
                                    then M.add block block_info b
                                    (* if the old one was honest, then don't change it*)
                                    else b
                end
            else
            (* If it isn't adversarial, then just put it in*)
                M.add block block_info b.




