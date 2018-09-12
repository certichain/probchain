From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype fintype choice ssrfun seq path finfun tuple.



(* utility function for ranges of values form (inclusive) a to b (exclusive) *)
Definition itoj (m n : nat) : seq.seq nat :=
  iota m (n - m).

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






Lemma negb_eqn b: b != true -> eq_op b false.
Proof.
  by case b.
Qed.


Lemma length_sizeP (T : Type) (ls : seq.seq T) : size ls = length ls.
Proof.
  by elim ls.
Qed.

Lemma has_countPn (T : Type) (a : pred T) (s : seq T) : ~~ has a s -> count a s = 0.
Proof.
  rewrite has_count.
  by rewrite -eqn0Ngt => /eqP .
Qed.

Lemma ltn_transPn n r : n < r -> r < n.+1 -> False.
Proof.
  elim: n => //= .
  by elim r => //=.
  move=> n IHn.
  move=> Hltn Hltr.
  apply IHn.
  rewrite leq_eqVlt in Hltn.
  move/orP: Hltn => [/eqP <- //=|].
  move/ltn_trans: Hltr => H /H.
  by rewrite ltnn.
  rewrite leq_eqVlt in Hltr.
  move/orP: Hltr => [/eqP [] Hwr|].
  move: Hltn.
  rewrite Hwr.
  by rewrite ltnn.
  rewrite -{1}(addn1 r).
  rewrite -{1}(addn1 n.+1).
  by rewrite ltn_add2r.
Qed.

Lemma subn_eqP n m : n <= m -> n - m = 0.
Proof.
  by rewrite -subn_eq0 => /eqP ->.
Qed.




Lemma ltn1 n : (n < 1)%nat = (n == 0%nat)%bool.
Proof.
  by elim n.
Qed.



Lemma ltnSn_eq a b : (a < b.+1)%nat -> (b < a.+1)%nat -> (a == b)%bool.
Proof.
  move: a.
  induction b => //= a.
  rewrite ltn1.
  by move=>  /eqP -> .
  have H (x y : nat) : (x > 0)%nat -> (x.-1 == y)%bool = (x == y.+1)%bool. by elim x  =>//=.
  case (0 < a)%nat eqn: Hva.
  rewrite -H //=.
  move=> Haltb Hblta.
  apply IHb.
  rewrite -ltnS.
  by rewrite prednK.
  by rewrite prednK.

  move/negP/negP: Hva.
  rewrite -leqNgt.
  rewrite leq_eqVlt.
  rewrite (ltnS b.+1).
  move=>/orP[/eqP ->|].
  by rewrite ltn0.
  by rewrite ltn0.
Qed.

Lemma addr_ltn a b c:
   (a + b < c)%nat -> (a < c)%nat.
Proof.
    by move=>/(ltn_addr b); rewrite ltn_add2r.
Qed.




Lemma ltn_leq_split a b c : (a + b - 1 < c.+1)%nat -> ~~ (b <= c)%nat -> ((b == c.+1)%bool  && (a == 0%nat)%bool).
Proof.
  rewrite -ltnNge.
  case (b) => [|b'].
  by rewrite ltn0.
  rewrite subn1 addnS.
  move=> Hab. move: (Hab).
  have Hltnadn x : (x > 0)%nat -> x.+1.-1 = x.-1.+1. by elim x => //=.
  move=> Habltn; move: Hab; rewrite prednK //=.
  move=> Hab; move: (Hab); rewrite addnC.
  move=> /addr_ltn Hbltc Hcltb.
  move: (ltnSn_eq _ _ Hbltc Hcltb) => /eqP Hbeq; move: Hab.
  rewrite Hbeq -(addn1 c) addnC ltn_add2l ltn1.
  move=>/eqP ->; apply/andP.
  by [].
Qed.


Lemma ltn_SnnP a b : (a.+1 < b.+1)%nat <-> (a < b)%nat.
Proof.
  split.
  by elim: a => //=.
  by elim: a => //=.
Qed.



Lemma subn_ltn_pr a b c : (a < c)%nat -> (a - b < c)%nat.
Proof.
  move: a b.
  elim: c => //= c .
  move=> IHn a b.
  case H: (a < c)%nat.
    move=> _.
    rewrite -(addn1 c).
    apply ltn_addr.
    by apply IHn.
  move/negP/negP: H .
  rewrite -leqNgt .
  rewrite -ltnS.
  move=> /ltnSn_eq H /(H) /eqP Heqa.
  induction a => //=.
  induction b => //=.
  by rewrite -Heqa subn0.
  rewrite subSS.
  rewrite -(addn1 c).
  apply ltn_addr.
  apply IHn.
  by rewrite Heqa.
Qed. 

Lemma ltn_subn_pr a b c : (a < b - c) -> (a < b).
Proof.
  move: a b.
  elim: c=>//= [ a b | c  IHc a b].
  by rewrite subn0.
  rewrite subnS -subn1 subnAC =>/IHc.
  rewrite ltn_subRL addnC addn1.
  case: b => //= b /ltn_SnnP /(ltn_addr 1).
  by rewrite addn1.
Qed.


Lemma leq_subn_pr a b c : (a <= b - c) -> (a <= b).
Proof.
  rewrite {1}leq_eqVlt => /orP [/eqP -> | ].
  by apply leq_subr.
  move=>/ltn_subn_pr Hlt.
  by apply/ltnW.
Qed.



Lemma ltnn_subS n : (n > 0) -> n.-1 < n.
Proof.
    by case n .
Qed.

Lemma ltn_weaken a b c : a + b < c -> a < c.
Proof.
  elim: c => //= c IHc.
  rewrite leq_eqVlt => /orP [/eqP [] <- |].
  rewrite -addnS.
  by elim a => //=.
  rewrite -(addn1 (a + b)).
  rewrite -(addn1 c).
  rewrite ltn_add2r.
  move=>/IHc Hlt.
  by apply ltn_addr.
Qed.


Lemma ltn_subl1 a b : a < b -> a.-1 < b.
Proof.
  move: b.
  elim:a => //= a IHa b.
  by rewrite -{1}(addn1 a) => /ltn_weaken.
Qed.

Lemma ltn_subl a b c : a < b -> a - c < b.
Proof.
  move: a b.
  elim: c => //= [a b | c IHc a b].
  by rewrite subn0.
  move=> /IHc Hlt.
  rewrite subnS.
  by apply ltn_subl1.
Qed.

Lemma ltn_subLR  m n p : ( p > 0) -> (n  < p + m) -> (n - m < p).
Proof.
  move: n p.
  elim: m => [//=|m IHn].
  move=>  n p.
  by rewrite addn0 subn0.
  move=> n p p_vld H.
  rewrite subnS.
  rewrite -subn1.
  rewrite subnAC.
  apply IHn =>//=.
  rewrite addnS  ltnS in H.
  rewrite leq_eqVlt in H.
  move/orP: H => [/eqP ->|].
  by rewrite addnC -addnBA; [rewrite ltn_add2l subn1; apply ltnn_subS|].
  move=> H.
  rewrite subn1.
  by apply ltn_subl1.
Qed.




