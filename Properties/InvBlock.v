From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat seq ssrfun eqtype.

Require Import Coq.Structures.OrderedTypeEx.
Require Import OrderedType.
Require Import Eqdep.

From Probchain
Require Import BlockChain.



Module Block_as_OT <: OrderedType.
  
  Definition t : Type := Block.
  
   Definition lt (x y : Block) :=
      ((Nat_as_OT.lt (block_nonce x) (block_nonce y)) \/
      ((Nat_as_OT.eq (block_nonce x) (block_nonce y)) /\ (Nat_as_OT.lt (block_link x) (block_link y))) /\
      ((Nat_as_OT.eq (block_nonce x) (block_nonce y)) /\ (Nat_as_OT.eq (block_link x) (block_link y)) /\  (Nat_as_OT.lt (block_proof_of_work x) (block_proof_of_work y))) 
      ) /\ (eq (block_records x) (block_records y)). 



  Definition eq : Block ->
       Block ->
       Prop := fun (x y : Block) =>
      Nat_as_OT.eq (block_nonce x) (block_nonce y) /\
      Nat_as_OT.eq (block_link x) (block_link y) /\
      Nat_as_OT.eq (block_proof_of_work x) (block_proof_of_work y) /\
      eq (block_records x) (block_records y). 



      
     Definition eq_refl : forall x : Block, eq x  x. Proof. Admitted.
     
     Definition eq_sym : forall x y : Block, eq x y -> eq y x. Proof. Admitted.

     Definition eq_trans : forall x y z : Block, eq x y -> eq y  z -> eq x  z. Proof. Admitted.

     Parameter lt_trans : forall x y z : Block, lt x y -> lt y z -> lt x z.
     Parameter lt_not_eq : forall x y : Block, lt x y -> ~ eq x y.
     Definition compare : forall x y : Block, OrderedType.Compare lt eq x y. Proof. Admitted.
     Definition eq_dec : forall n m : Block, {eq n m} + {not (eq n m)}. Proof. Admitted.

End Block_as_OT.

