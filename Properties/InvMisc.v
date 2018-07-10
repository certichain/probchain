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

Print rem.

Fixpoint prefix {A : eqType} (xs : list A) (ys : list A) :=
  if length xs > length ys 
    then false
    else 
      match ys with
        | [::] => xs == [::]
        | y' :: ys' => if length ys == length xs
              then xs == ys
              else prefix  xs ys'
        end.
    
Example prefix_example_1 : prefix  [:: 1; 2; 3] [:: 4; 5; 1; 2; 3].
Proof. by []. Qed.

Example prefix_example_2 : @prefix _ [:: 1; 2; 3] [:: 1; 2; 3].
Proof. by []. Qed.
