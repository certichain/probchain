From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype fintype choice ssrfun seq path.

From mathcomp.ssreflect
Require Import tuple.

Set Implicit Arguments.

Definition ntuple_cons (A : Type) (n : nat) (a : A) (list : n.-tuple A) : (n.+1).-tuple A.
Proof.
    case list=> tval /eqP H0.
    split with (tval := (a :: tval)).
    by rewrite  -H0.
Qed.

Lemma size_exists (A: eqType) (ls : seq A) (n' : nat) : (size ls) = n'.+1 -> exists (ls' : seq A) (a : A), ls == (a :: ls').
Proof.
    move: n'.
    induction ls.
        move=> n' H.
        inversion H.
    move=> n' //= /eq_add_S H .
    destruct n'.
        apply size0nil in H.
        exists [::].
        exists a.
        by rewrite H.
    apply IHls in H.
    destruct H as [ls' [a']].
    move: H=> /eqP-H. 
    rewrite H.
    exists (a' :: ls').
    by exists a.
Qed.

Definition ntuple_head (A : Type) (n' : nat) (list : (n'.+1).-tuple A) : A .
Proof.
    apply (thead list).
Qed.

Definition ntuple_tail (A : Type) (n' : nat) (list : (n'.+1).-tuple A) : n'.-tuple A.
Proof.
    move: (tuple_eta list) => H.
    split with (tval := behead list).
    apply behead_tupleP.
Qed.


Section fixlist.
    Variable A : eqType.
    Variable n' : nat.

    Definition fixlist n := n.-tuple (option A).


    (* I wanted to write this, but it wouldn't type check*)
    (* Fixpoint fixlist_insert (m : nat) (list : fixlist m.+1) (a : A) : fixlist m.+1 :=
        match tnth list (inord m) return fixlist m.+1  with
            | None => [tuple of (Some value) :: [tuple of behead list]]
            | Some value => match m return fixlist m.+1 with
                                | 0 => list
                                | m'.+1 =>  [tuple of (Some value) :: fixlist_insert m' [tuple of behead list] a ]
                                end
            end. *)


    Lemma fixlist_insert (m : nat) (list : fixlist m.+1) (a : A) : fixlist m.+1.
        move: a.
        move: list.
        elim m.
        move=> list a.
        case (tnth list (inord m)) eqn: H; last first.
            exact [tuple of (Some a) :: [tuple of behead list]].
        exact list.
        move=> m0 fixlist_insert list a.
        destruct (tnth list (inord (m0.+1))) eqn: H; last first.
            exact [tuple of (Some a) :: [tuple of behead list]].
            exact [tuple of (Some s) :: [tuple of fixlist_insert (ntuple_tail list) a]].
    Qed.




(* 
    Lemma fixlist_remove_h (m m' : nat) : (m'.+1 = m) -> fixlist m.+1 -> fixlist m'.+2.
    Proof.
        move=> H list.
        rewrite -H in list.
        exact list.
    Qed.
 *)
    (* Fixpoint fixlist_remove (m : nat) (list : fixlist m.+1) (n : nat) : fixlist m.+1 :=
        match m as m', n return _ = m -> fixlist _ with
            | m'.+1, n'.+1 => fun epf => [tuple of ntuple_head list ::  @fixlist_remove m' (ntuple_tail list) n']
            | 0, n'.+1 => fun epf => [ tuple of [:: ntuple_head list]]
            | m'.+1, 0 => fun epf => match (tnth list (inord m'))  with
                            | None =>  list 
                            | Some v => [tuple of None :: (ntuple_tail list)]
                          end
            | 0, 0 => fun epf =>  [tuple of [:: None] ]
           end (erefl _)
           .
    *)


    Fixpoint fixlist_remove (m : nat) (list : fixlist m.+1) (n : nat) : fixlist m.+1.
        move: list.
        induction  m  as [|m'] eqn: Hm.
        induction n as [|n''] eqn: Hn.
            (* 0, 0 *)
            move=> _.
            exact [tuple of [:: None]].
            (* 0, n.+1 *)
            move=> list.
            exact list.
        case n eqn: Hn.
            (*m'.+1, 0 *)
            move=> list.
            exact [tuple of ntuple_head list ::  @fixlist_remove m' (ntuple_tail list) n'].
        (* m'.+1, n'.+1 *)
        move=> list.
        case (tnth list (inord m')) eqn: Hs; first last. 
            (* None *)
            exact list.
        (* Some v *)
        exact [tuple of None :: (ntuple_tail list)].
    Qed.
   

    (* Fixpoint fixlist_set_nth (m : nat) (list : fixlist  m.+1) (a : A) (n : nat) : fixlist m.+1 :=
         match m, n with
            | m'.+1, n'.+1 => [tuple of ntuple_head list ::  @fixlist_remove m' (ntuple_tail list) n']
            | 0, n'.+1 => [tuple of [:: ntuple_head list]]
            | m'.+1, 0 => [tuple of (Some a) :: (ntuple_tail list)] 
            | 0, 0 =>  [tuple of [:: Some a] ]
       end. *)

    Fixpoint fixlist_set_nth (m : nat) (list : fixlist  m.+1) (a : A) (n : nat) : fixlist m.+1.
    Proof.
        induction  m  as [|m'] eqn: Hm.
        induction n as [|n''] eqn: Hn.
            (* 0, 0 *)
            exact [tuple of [:: Some a]].
            (* 0, n.+1 *)
            exact list.
        case n eqn: Hn.
            (* m.+1, 0 *)
            exact [tuple of (Some a) :: (ntuple_tail list)].
            (* m'.+1, n'.+1 *)
            exact [tuple of ntuple_head list ::  @fixlist_set_nth m' (ntuple_tail list) a n0].
    Qed.

