From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype fintype choice ssrfun seq path finfun.

Require Import Coq.Structures.OrderedTypeEx.
Require Import OrderedType.
Require Import Eqdep.




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

Fixpoint all_consecutive_sequences {A} (xs : list A) (l : nat) (p : list A -> bool) :=
  if (length xs) < l
    then true
  else 
    match xs with
      | [::] => true
      | x' :: xs' => p (take l xs) && all_consecutive_sequences xs' l p
      end.


Definition mod_incr (n : nat) (pf: n > 0) (m : 'I_n) : 'I_n. 
  case_eq (m < n)=> H.
  exact (Ordinal H).
  exact (Ordinal pf).
Qed.
