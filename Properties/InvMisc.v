From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat seq ssrfun eqtype.

Require Import Coq.Structures.OrderedTypeEx.
Require Import OrderedType.
Require Import Eqdep.

From Probchain
Require Import BlockChain.


Module Hash_Triple_as_OT <: OrderedType.
  
  Definition t : Type := (Hashed * seq.seq Transaction * nat).
  
  Definition eq : Hashed * seq.seq Transaction * nat ->
       Hashed * seq.seq Transaction * nat ->
       Prop := fun (x y : (Hashed * list Transaction * nat)) =>
      Nat_as_OT.eq (fst (fst x)) (fst (fst y)) /\
      eq (snd (fst x)) (snd (fst y)) /\
      Nat_as_OT.eq   (snd x) (snd y).
      

   Definition lt (x y : (Hashed * list Transaction * nat)) :=
    Nat_as_OT.lt (fst (fst x)) (fst (fst y)) \/
    (Nat_as_OT.eq (fst (fst x)) (fst (fst y))) /\ (Nat_as_OT.lt (snd x) (snd y)).    
      
     Definition eq_refl : forall x : (Hashed * list Transaction * nat), eq x  x. Proof. Admitted.
     
     Definition eq_sym : forall x y : (Hashed * list Transaction * nat), eq x y -> eq y x. Proof. Admitted.

     Definition eq_trans : forall x y z : (Hashed * list Transaction * nat), eq x y -> eq y  z -> eq x  z. Proof. Admitted.

     Parameter lt_trans : forall x y z : (Hashed * list Transaction * nat), lt x y -> lt y z -> lt x z.
     Parameter lt_not_eq : forall x y : (Hashed * list Transaction * nat), lt x y -> ~ eq x y.
     Definition compare : forall x y : (Hashed * list Transaction * nat), OrderedType.Compare lt eq x y. Proof. Admitted.
     Definition eq_dec : forall n m : (Hashed * list Transaction * nat), {eq n m} + {not (eq n m)}. Proof. Admitted.

End Hash_Triple_as_OT.


Module BlockEq.


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


(* Couldn't find a remove_nth function in stdlib or ssreflect*)
Fixpoint rem_nth {A:Type} (n : nat) (ls : list A) : list A := 
    match n with
      | 0 => if ls is h::t then t else nil
      | S n' => if ls is h :: t 
            then h :: (rem_nth n' t)
            else ls
      end.

(*
Example rem_nth_test_1 : rem_nth 0 [:: 1; 2; 3] = [:: 2; 3].
Proof. by []. Qed.

Example rem_nth_test_2 : rem_nth 1 [:: 1; 2; 3] = [:: 1; 3].
Proof. by []. Qed.


Example rem_nth_test_3 : rem_nth 2 [:: 1; 2; 3] = [:: 1; 2].
Proof. by []. Qed.
*)

(* Also couldn't find any utilities for dealing with option types *)
Definition option_cons 
  {A : Type} 
  (self : option A) 
  (list : seq.seq A) : seq.seq A := match self with 
    | Some value => value :: list
    | None => list
  end.

(*Example option_cons_test_1 : option_cons (Some 1) [:: 2; 3] = [:: 1; 2; 3].
Proof. by []. Qed.


Example option_cons_test_2 : option_cons None [:: 2; 3] = [:: 2; 3].
Proof. by []. Qed.*)

Lemma options_cons_some_eq_cons : forall (A : Type) (x : A) (xs : seq.seq A), option_cons (Some x) xs = cons x xs.
Proof.
  by [].
Qed.

Lemma options_cons_none_ident : forall (A : Type) (xs : seq.seq A), option_cons None xs = xs.
Proof.
  by [].
Qed.

