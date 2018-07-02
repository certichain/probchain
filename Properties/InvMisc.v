From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat seq ssrfun eqtype.

Require Import Coq.Structures.OrderedTypeEx.
Require Import OrderedType.
Require Import Eqdep.

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


Module BlockEq.

    Lemma eqb_refl   : true = (true == true).
    Proof.
      by [].
    Qed.


    Definition eq_transaction (t1 t2 : Transaction) := 
      match t1 with
        | valid => if t2 is valid then true else false
        | invalid => if t2 is invalid then true else false
      end.
    Lemma eq_transactionP : Equality.axiom eq_transaction.
    Proof.
      case => [[|] | [|]] ; rewrite /eq_transaction//=; [ by constructor 1 | by constructor 2 | by constructor 2 | by constructor 1].
    Qed.
    Canonical Transaction_eqMixin := Eval hnf in EqMixin eq_transactionP.
    Canonical Transaction_eqType := Eval hnf in EqType Transaction Transaction_eqMixin.



      Definition eq_block (bc1 bc2 : Block) := 
      ((block_link bc1) == (block_link bc2)) &&
      ((block_records bc1) == (block_records bc2)) &&
      ((block_proof_of_work bc1) == (block_proof_of_work bc2)).

      Lemma eq_blockP : Equality.axiom eq_block.
      Proof.
        case => [bl br bpow bia bhr b]; rewrite /eq_block//=.
        (* TODO(Kiran): Complete this proof *)
      Admitted.
      

    Canonical Block_eqMixin := Eval hnf in EqMixin eq_blockP.
    Canonical Block_eqType := Eval hnf in EqType Block Block_eqMixin.


End BlockEq.
Export BlockEq.

