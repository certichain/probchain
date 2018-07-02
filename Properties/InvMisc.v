From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat seq ssrfun.

Require Import Coq.Structures.OrderedTypeEx.
Require Import OrderedType.

From Probchain
Require Import BlockChain.

Module Seq_as_OT <: OrderedType.

     Definition t : Set := (list Transaction).
     Definition eq : list Transaction -> list Transaction -> Prop := eq.
    
     Definition eq_refl : forall x : t, x = x.
     Proof. by []. Qed.
     Definition eq_sym : forall x y : t, x = y -> y = x.
     Proof. by []. Qed.
     Definition eq_trans : forall x y z : t, x = y -> y = z -> x = z.
     Proof. apply eq_trans. Qed.
     Definition lt : list Transaction -> list Transaction -> Prop := fun a b => (length a) < (length b).
     Parameter lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
     Parameter lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
     Definition compare : forall x y : list Transaction, Compare lt eq x y.
     Proof.
        induction x.
        induction y.
          by constructor 2.
          by constructor 1.
        Admitted.
       
     Definition eq_dec : forall n m : list Transaction, {n = m} + {n <> m}.
     Proof.

     Admitted.
     
End Seq_as_OT.


Module Hash_Triple_as_OT <: OrderedType.
  
  Definition t : Set := (Hashed * list Transaction * nat).
  
  Definition eq : Hashed * seq.seq Transaction * nat ->
       Hashed * seq.seq Transaction * nat ->
       Prop := fun (x y : (Hashed * list Transaction * nat)) =>
      Nat_as_OT.eq (fst (fst x)) (fst (fst y)) /\
      Seq_as_OT.eq (snd (fst x)) (snd (fst y)) /\
      Nat_as_OT.eq   (snd x) (snd y).
      
   Definition lt (x y : (Hashed * list Transaction * nat)) :=
    Nat_as_OT.lt (fst (fst x)) (fst (fst y)) \/
    (Nat_as_OT.eq (fst (fst x)) (fst (fst y)) /\ Seq_as_OT.lt (snd (fst x)) (snd (fst y))) \/
    (Nat_as_OT.eq (fst (fst x)) (fst (fst y)) /\ (Seq_as_OT.eq (snd (fst x)) (snd (fst y)) /\ Nat_as_OT.lt (snd x) (snd y))).    
      
     Definition eq_refl : forall x : (Hashed * list Transaction * nat), eq x  x. Proof. Admitted.
     
     Definition eq_sym : forall x y : (Hashed * list Transaction * nat), eq x y -> eq y x. Proof. Admitted.

     Definition eq_trans : forall x y z : (Hashed * list Transaction * nat), eq x y -> eq y  z -> eq x  z. Proof. Admitted.

     Parameter lt_trans : forall x y z : (Hashed * list Transaction * nat), lt x y -> lt y z -> lt x z.
     Parameter lt_not_eq : forall x y : (Hashed * list Transaction * nat), lt x y -> ~ eq x y.
     Definition compare : forall x y : (Hashed * list Transaction * nat), OrderedType.Compare lt eq x y. Proof. Admitted.
     Definition eq_dec : forall n m : (Hashed * list Transaction * nat), {eq n m} + {not (eq n m)}. Proof. Admitted.

End Hash_Triple_as_OT.

