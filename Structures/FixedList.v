From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype fintype choice ssrfun seq path.

From mathcomp.ssreflect
Require Import tuple.


Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.ProofIrrelevance.



Set Implicit Arguments.

Definition ntuple_cons (A : Type) (n : nat) (a : A) (list : n.-tuple A) : (n.+1).-tuple A.
Proof.
    case list=> tval /eqP H0.
    split with (tval := (a :: tval)).
    by rewrite  -H0.
Defined.

Definition ntuple_head (A : Type) (n' : nat) (list : (n'.+1).-tuple A) : A .
Proof.
    apply (thead list).
Defined.

Definition ntuple_tail (A : Type) (n' : nat) (list : (n'.+1).-tuple A) : n'.-tuple A.
Proof.
    move: (tuple_eta list) => H.
    split with (tval := behead list).
    apply behead_tupleP.
Defined.

Lemma size_ncons_nil (A : Type) (a : A) (n : nat): (size (ncons n a [::])) == n.
Proof.
    rewrite size_ncons => //=.
    by rewrite addn0.
Defined.


Fixpoint set_tnth (A : Type) (m : nat) (list : m.-tuple A) (a : A) (n : nat) : m.-tuple A.
Proof.
    induction  m  as [|m'] eqn: Hm.
    induction n as [|n''] eqn: Hn.
        (* 0, 0 *)
        exact list.
        (* 0, n.+1 *)
        exact list.
    case n eqn: Hn.
        (* m.+1, 0 *)
        exact [tuple of a :: (ntuple_tail list)].
        (* m'.+1, n'.+1 *)
        exact [tuple of ntuple_head list ::  set_tnth A m' (ntuple_tail list) a n0].
Defined.




Section fixlist.
    Variable A : eqType.
Definition fixlist n := n.-tuple (option A).

    Definition fixlist_empty n : fixlist n :=
        @Tuple n
            (option A) 
            (ncons n None [::])
            (size_ncons_nil   None n).

    Definition fixlist_of n (a : A) : fixlist n:=
        @Tuple n
            (option A) 
            (ncons n (Some a) [::])
            (size_ncons_nil (Some a) n).

    (* I wanted to write this, but it wouldn't type check*)
    (* Fixpoint fixlist_insert (m : nat) (list : fixlist m.+1) (a : A) : fixlist m.+1 :=
        match tnth list (inord m) return fixlist m.+1  with
            | None => [tuple of (Some value) :: [tuple of behead list]]
            | Some value => match m return fixlist m.+1 with
                                | 0 => list
                                | m'.+1 =>  [tuple of (Some value) :: fixlist_insert m' [tuple of behead list] a ]
                                end
            end. *)

    Eval compute in (nat_of_ord (@inord 0 3)).

    Definition fixlist_insert {m : nat} (list : fixlist m)  :=
      nat_rect (fun m0 : nat => fixlist m0 -> A -> fixlist m0) (fun (list0 : fixlist 0) (_ : A) => list0)
       (fun (m0 : nat) (fixlist_insert : fixlist m0 -> A -> fixlist m0) (list0 : fixlist m0.+1) (a0 : A) =>
        let o := thead list0 in
        let H : thead list0 = o := erefl o in
        match o as o0 return (thead list0 = o0 -> fixlist m0.+1) with
        | Some s =>
            fun _ : thead list0 = Some s => [tuple of Some s :: [tuple of fixlist_insert (ntuple_tail list0) a0]]
        | None => fun _ : thead list0 = None => [tuple of Some a0 :: [tuple of behead list0]]
        end H) m list.

    Definition fixlist_unwrap (m : nat) (list : fixlist m) : seq A :=
        flatten (map (fun o_value => match o_value with
                            | Some value => [:: value]
                            | None => [::]
                            end) list).


    (* Lemma fixlist_insert (m : nat) (list : fixlist m) (a : A) : fixlist m. *)
    (*     move: a. *)
    (*     move: list. *)
    (*     elim m. *)
    (*     move=> list a. *)
    (*         exact list. (* can not insert anything into an empty list*) *)
    (*     move=> m0 fixlist_insert list a. *)
    (*     case (thead list) eqn:H; last first. *)
    (*         exact [tuple of (Some a) :: [tuple of behead list]]. *)
    (*         exact [tuple of (Some s) :: [tuple of fixlist_insert (ntuple_tail list) a]]. *)
    (* Defined. *)




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


    (* remove will remove the nth index of the list *)
    Fixpoint fixlist_remove (m : nat) (list : fixlist m) (n : nat) : fixlist m.
        move: list.
        induction  m  as [|m'] eqn: Hm.
        induction n as [|n''] eqn: Hn.
            (* 0, 0 *)
            move=> _.
            exact [tuple of [::]].
            (* 0, n.+1 *)
            move=> list.
            exact list.
        case n eqn: Hn.
            (*m'.+1, 0 *)
            move=> list.
            exact [tuple of None :: (ntuple_tail list)].
        (* m'.+1, n0.+1 *)
        move=> list.
            exact [tuple of ntuple_head list ::  @fixlist_remove m' (ntuple_tail list) n0].
    Defined.

    (* rem will remove all instances of a in the list*)
    Lemma fixlist_rem (m : nat) (list: fixlist m) (a : A) : fixlist m.
        induction m.
            (* if m is 0, return empty list *)
            exact list.
        (* assume we have a rem function for lists of length m*)
        (* consider a list of length m.+1 *)
        case (ntuple_head list) eqn: H.
            (* if it's head is not none, *)
            case (s == a) eqn: H'.
                (* if the value of the head is equal to the value being removed*)
                (* return a list with None in the place of the first value, and all subsequent ones removed*)
                exact [tuple of None :: IHm (ntuple_tail list)].
            (* if the value of the head is not equal, just keep the head, remve from the tail*)
            exact [tuple of (Some s) :: IHm (ntuple_tail list)].
        (* if the value of the head is none, just remove from the tail*)
        exact [tuple of None :: IHm (ntuple_tail list)].
    Defined.


    (* Fixpoint fixlist_set_nth (m : nat) (list : fixlist  m.+1) (a : A) (n : nat) : fixlist m.+1 :=
         match m, n with
            | m'.+1, n'.+1 => [tuple of ntuple_head list ::  @fixlist_remove m' (ntuple_tail list) n']
            | 0, n'.+1 => [tuple of [:: ntuple_head list]]
            | m'.+1, 0 => [tuple of (Some a) :: (ntuple_tail list)] 
            | 0, 0 =>  [tuple of [:: Some a] ]
       end. *)

    Definition fixlist_set_nth (m : nat) (list : fixlist  m) (a : A) (n : nat) : fixlist m := set_tnth list (Some a) n .

    (* Definition fixlist_nth (m : nat) (default : A) (list : fixlist m) (n : nat) : A :=
        if n < m then
            match m with
                | 0 => default
                | m'.+1 => tnth list (Ordinal (m'.+1))
                end
        else default. *)

    Definition fixlist_nth (m : nat) (default : A) (list : fixlist m)  (n : nat) : A.
    Proof.
        case (n < m) eqn: H; last first.
            exact default.
        
        apply ltn_addr with (p := 1) in H .
        case m eqn: H1.
            exact default.
        move: (ltn0Sn n0)=> H''.
        move: (Ordinal H'')=> ind.
        case (tnth list ind) eqn: isSome.
            exact s.
            exact default.
    Defined.

    Definition fixlist_get_nth (m : nat)  (list : fixlist m)  (n : nat) : option A.
    Proof.
        case (n < m) eqn: H; last first.
            exact None.
        
        apply ltn_addr with (p := 1) in H .
        case m eqn: H1.
            exact None.
        move: (Ordinal (ltn0Sn n0))=> ind.
        case (tnth list ind) eqn: isSome.
            exact (Some s).
            exact None.
    Defined.


    (* Fixpoint fixlist_length' (m : nat) (list : fixlist  m.+1) : nat :=
        match m with 
            | 0 => match ntuple_head list with 
                | Some _ => 1 
                | None   => 0
                end
            | m'.+1 => match ntuple_head list with 
                | Some _ => 1 + fixlist_length' (ntuple_tail list)
                | None   =>  fixlist_length' (ntuple_tail list)
                end
            end. *)



    Fixpoint fixlist_length (m : nat) (list : fixlist  m) : nat :=
      length (fixlist_unwrap list).

    Definition fixlist_is_empty (m : nat) (list: fixlist m) : bool :=
      (fixlist_unwrap list) == [::].

    (* a fixed list is top heavy if all the empty spaces are at the tail of the list*)
    Definition fixlist_is_top_heavy (m : nat) (list : fixlist m) : bool :=
      nat_rect (fun m0 : nat => fixlist m0 -> bool) xpredT
       (fun (m0 : nat) (fixlist_is_top_heavy : fixlist m0 -> bool) (list0 : fixlist m0.+1) =>
          let o := thead list0 in
          let H : thead list0 = o := erefl o in
          match o as o0 return (thead list0 = o0 -> bool) with
          | Some s => fun _ : thead list0 = Some s => fixlist_is_top_heavy [tuple of behead list0]
          | None => fun _ : thead list0 = None => fixlist_is_empty [tuple of behead list0]
          end H) m list
      .

    (* Proof. *)
    (*   move: list. *)
    (*   elim m. *)
    (*     move=> list. *)
    (*     exact true. *)
    (*   move=> m0 fixlist_is_top_heavy list. *)
    (*   case (thead list) eqn: H; last first. *)
    (*   exact (fixlist_is_empty [tuple of behead list]). *)
    (*   exact (fixlist_is_top_heavy [tuple of behead list]). *)
    (* Defined. *)



    (* Fixpoint fixlist_filter (m : nat) (P : pred A) (list : fixlist m) : fixlist m :=
        match m with
            | 0 => list
            | m'.+1 => match ntuple_head list with
                | Some a => if P a then [tuple of (Some a) :: fixlist_filter (ntuple_tail list)]
                                    else [tuple of fixlist_filter (ntuple_tail list)]
                | None => [tuple of fixlist_filter (ntuple_tail list)]
                end
            end. *)
    Fixpoint fixlist_filter (m : nat) (P : pred A) (list : fixlist m) : fixlist m.
        case m eqn: H.
            exact list.
        case (ntuple_head list).
            move=> a.
            case (P a) eqn: H'.
                exact [tuple of (Some a) :: fixlist_filter n P (ntuple_tail list)].
            exact [tuple of None :: fixlist_filter n P (ntuple_tail list)].
        exact [tuple of None :: fixlist_filter n P (ntuple_tail list)].
    Defined.




    (* Fixpoint fixlist_contains (m : nat) (a : A) (list : fixlist m) : bool :=
        match m with
            | 0 => false
            end
            | m'.+1 => match ntuple_head list with 
                | Some a' => if a' == a then true else fixlist_contains (ntuple_tail list)
                | None => fixlist_contains (ntuple_tail list)
                end
            end. *)

    Definition fixlist_contains (m : nat) (a : A) (list : fixlist m) : bool :=
      has (fun x => x == a) (fixlist_unwrap list).


    Fixpoint fixlist_index_of' (m : nat) (n: nat) (a : A) (list : fixlist m) : option nat. 
        case m eqn: H.
            exact None.
        case (ntuple_head list).
            move=> a'.
            case (a' == a) eqn: H'.
                exact (Some n).
                exact (fixlist_index_of' n0 n.+1 a (ntuple_tail list)).
            exact (fixlist_index_of' n0 n.+1 a (ntuple_tail list)).
    Defined. 

    Definition fixlist_index_of (m : nat) (a : A) (list : fixlist m) : option nat := 
        fixlist_index_of' 0 a list.

    (* uses a fixlist like a fixed length queue, inserting at the start and removing from the end*)
    Fixpoint fixlist_enqueue (m : nat) (a : option A) (list: fixlist m) : (fixlist m * option A).
     (* :=
        match m with 
            | 0     => list  (* simply drop the a *)
            | m'.+1 => [tuple of a :: fixlist_shiftl' (ntuple_head list) (ntuple_tail list)]
            end. *)
        case m eqn: H.
            exact (list, a).
        case (@fixlist_enqueue _ (ntuple_head list) (ntuple_tail list)) => shifted_tail output.
        exact ([tuple of a :: shifted_tail], output).
    Defined.

    Definition fixlist_shiftl (m : nat) (list: fixlist m) : fixlist m :=
        let: (result, output) := fixlist_enqueue None list in
        result.


    
    Lemma eqn_incr a b : a == b -> a.+1 == b.+1.
    Proof. by move=>/eqP/(f_equal S)/eqP. Qed.

    Lemma size_incr (X : Type) (m : nat) (ls : seq X) (o: X) : (size ls == m) -> (size (o::ls) == m.+1).
    Proof. by []. Qed.

    Lemma fixlist_coerce_some (m : nat) (ls : seq (option A)) (o: (A)) (pf: size ls == m) (pf': size ((Some o) :: ls) == m.+1) :
      (fixlist_unwrap (Tuple pf')) = o :: (fixlist_unwrap (Tuple pf)). 
      Proof.
        move: pf pf'.
        by elim ls => //.
      Qed.

    Lemma fixlist_coerce_none (m : nat) (ls : seq (option A)) (pf: size ls == m) (pf': size (None :: ls) == m.+1) :
      (fixlist_unwrap (Tuple pf')) = (fixlist_unwrap (Tuple pf)). 
      Proof.
        move: pf pf'.
        by elim ls => //.
      Qed.

     Lemma fixlist_insert_coerce_none (m : nat) (ls : seq (option A)) (o: (A)) (pf: size ls == m) (pf': size (None :: ls) == m.+1) :
      (fixlist_unwrap (fixlist_insert (Tuple pf') o) = o :: (fixlist_unwrap (Tuple pf))). 
      Proof.
        move: ls pf pf' .
        by elim m => //=.
      Qed.


      Lemma ntuple_tail_coerce (m : nat) (T: Type) (y  x: T) xs : forall (pf' : (size [:: y, x & xs] == m.+2)) (pf: size [:: x & xs] == m.+1),
        (ntuple_tail (Tuple (n:=m.+2) (tval:=[:: y, x & xs]) pf')) = (Tuple (n:=m.+1) (tval:=[:: x & xs]) pf).
      Proof.
        move: x y m.
        case: xs => [x y |x0 xs x y].
        move=> m Hpf' Hpf.
        move: (Hpf') (Hpf).
        move/eqP:Hpf => Hpf.
        move=> pf' pf.
        rewrite /ntuple_tail //=.
        generalize (behead_tupleP (Tuple (n:=m.+2) (tval:=[:: y; x]) pf')) as H_tail.
        have Hobv: (behead (Tuple (n:=m.+2) (tval:=[:: y; x]) pf')) = ([:: x] ). by []. 
        have Hobv': m.+2.-1 = m.+1. by [].
        move=> H_tail.
        dependent rewrite Hobv in H_tail.
        dependent rewrite Hobv' in H_tail.
        by rewrite (proof_irrelevance _  H_tail pf).

        move=> m pf' pf .
        rewrite /ntuple_tail //=.
        generalize (behead_tupleP (Tuple (n:=m.+2) (tval:=[:: y, x, x0 & xs]) pf')) as H_tail.
        move=> H_tail.
        have Hobv: (behead (Tuple (n:=m.+2) (tval:=[:: y, x, x0 & xs]) pf')) = [:: x, x0 & xs]. by [].
        have Hobv': m.+2.-1 = m.+1. by [].

        dependent rewrite Hobv in H_tail.
        dependent rewrite Hobv' in H_tail.
        by rewrite (proof_irrelevance _  H_tail pf).

      Qed.



      Lemma fixlist_insert_size_idem  (m : nat) (ls : fixlist m) (a : A) : size (fixlist_insert ls a) = size ls.
      Proof.
        destruct ls as [ls Hls].
        move: ls Hls .
        elim: m=> //= m Ihm xs Hxs.
        case: (thead _) => [s//=|//=]; last first.
        move: Hxs.
        by case xs => //=.
        move: Hxs.
        case: xs => //= x xs Hxs'.
        move: (Hxs').
        move/eqP: Hxs'=>Hxs'.
        case:Hxs'=>/eqP Hxs.
        move: (Ihm xs Hxs) => IHm.
        move=> Hxs'//=.
        case x => //=; last first.
        rewrite /ntuple_tail//=.
        generalize (behead_tupleP (Tuple (n:=m.+1) (tval:=None :: xs) Hxs')) as H_tail.
        move=> H_tail.
        have Hobv: (behead (Tuple (n:=m.+1) (tval:=None :: xs) Hxs')) = xs. by []. 
        have Hobv': m.+1.-1 = m. by[].
        dependent rewrite Hobv in H_tail.
        dependent rewrite Hobv' in H_tail.
        rewrite -IHm.
        by rewrite (proof_irrelevance _  H_tail Hxs).
        move=> s'.
        rewrite /ntuple_tail//=.
        generalize (behead_tupleP (Tuple (n:=m.+1) (tval:=Some s' :: xs) Hxs')) as H_tail.
        move=> H_tail.
        have Hobv: (behead (Tuple (n:=m.+1) (tval:=Some s' :: xs) Hxs')) = xs. by[].
        have Hobv': m.+1.-1 = m. by[].
        dependent rewrite Hobv in H_tail.
        dependent rewrite Hobv' in H_tail.
        rewrite -IHm.
        by rewrite (proof_irrelevance _  H_tail Hxs).
  Qed. 


      Lemma tval_injectivitiy (T:Type) n (t: n.-tuple T) (pf: size t == n) : Tuple (n:=n) (tval:=tval t) pf =  t. 
      Proof.
        destruct t as [t t_pf].
        move=>//=.
          by rewrite (proof_irrelevance _ pf t_pf).
      Qed.







     Lemma fixlist_insert_coerce_some (m : nat) (ls : seq (option A)) (s o: A) (pf: size ls == m) (pf': size (Some s :: ls) == m.+1) :
      (fixlist_unwrap (fixlist_insert (Tuple pf') o) = s :: fixlist_unwrap (fixlist_insert (Tuple pf) o)). 
      Proof.
        rewrite fixlist_coerce_some.
        by rewrite fixlist_insert_size_idem .
        rewrite /ntuple_tail//= .
        generalize (behead_tupleP (Tuple (n:=m.+1) (tval:=Some s :: ls) pf')) as H_tail.
        move=> H_tail.
        have Hobv: (behead (Tuple (n:=m.+1) (tval:=Some s :: ls) pf')) = ls. by [].
        have Hobv': m.+1.-1 = m. by [].
        dependent rewrite Hobv in H_tail.
        dependent rewrite Hobv' in H_tail.
        clear Hobv.
        clear Hobv'.
        move=>Hpf.
        suff: (Tuple (n:=m) (tval:=fixlist_insert (Tuple (n:=m) (tval:=ls) H_tail) o) Hpf) = (fixlist_insert (Tuple (n:=m) (tval:=ls) pf) o).
        by move=> ->.
        rewrite (proof_irrelevance _ pf H_tail).
        by rewrite tval_injectivitiy.
    Qed.



      Lemma fixlist_contains_obv a m' xs Hxs : fixlist_contains a (fixlist_insert (Tuple (n:=m') (tval:=xs) Hxs) a) =
  has (eq_op^~ a) (fixlist_unwrap (fixlist_insert (Tuple (n:=m') (tval:=xs) Hxs) a)).
        Proof.
          apply/eqP=>//=.
        Qed.
        

    Lemma fixlist_has_eq (m : nat) (list: fixlist m) (a : A) (P: pred A) :
       (has P (fixlist_unwrap (fixlist_insert list a))) = has P (fixlist_unwrap list) || [ && P a, fixlist_contains a (fixlist_insert list a) & ~~ has P (fixlist_unwrap list)].
      Proof.
        destruct list as [xs Hxs].
        move: m Hxs .
        elim: xs => //=.
        move=> m xs.
        case H: (P a).
        move: (xs).
        by move/eqP: xs => <- //=.
        move=> //=.
        by induction m=>//=.

        move=> x xs IHx m.
        case m.
        by move=> Hxs; move/eqP:(Hxs)=>Hwrong; inversion Hwrong.
        case x =>[s m'|]; last first.
        move=> m' Hxs.
        rewrite  (@fixlist_insert_coerce_none ) //=.
        rewrite fixlist_coerce_none.
        move: (Hxs).
        move/eqP: Hxs => Hxs.
        case: Hxs => /eqP Hxs Hxs'.
        case (has P (fixlist_unwrap (Tuple (n:=m') (tval:=xs) Hxs'))) => //=.
        by apply orbT.
        rewrite Bool.orb_false_r.
        case (P a) => //=.
        rewrite /fixlist_contains//=.
        have :a == a. by[].
        by move=> ->.

        move=> Hxs'.
        rewrite  (@fixlist_insert_coerce_some m' xs s a) .
        rewrite fixlist_coerce_some /fixlist_contains.
        rewrite fixlist_insert_coerce_some //=.
        case Hps: (P s) => //=.
        move: (Hxs').
        move/eqP: Hxs' => Hxs'.
        case: Hxs' => /eqP Hxs'.
        move=> Hxs.
        rewrite IHx.
        case (has P (fixlist_unwrap (Tuple (n:=m') (tval:=xs) Hxs))) => //=.
        case Hpa: (P a) => //=.
        case Heq: (s == a) => //= .
        move/eqP: Heq => Heq.
        rewrite -Heq in Hpa.
        rewrite Hpa in Hps.
        by inversion Hps.
  Qed.


      Lemma fixlist_empty_is_top_heavy (m : nat) (ls : fixlist m) :
        fixlist_is_empty ls -> fixlist_is_top_heavy ls.
      Proof.
        case: ls => ls Hls.
        move: m Hls.
        elim ls => //=.
        by move=>m ls_H; move: (ls_H); move/eqP: ls_H => <-.
        move=> o_x xs IHm [//|m'] Hls .
        by case o_x => //=.
      Qed.


    Lemma fixlist_insert_preserves_top_heavy (m : nat) (ls : fixlist m) (a : A) :
        fixlist_is_top_heavy ls -> fixlist_is_top_heavy (fixlist_insert ls a).
      Proof.
        case: ls => ls Hls.
        move: m Hls a.
        elim: ls.
        move=> m ls_H.
        move: (ls_H).
        move/eqP: ls_H => Hls.
        by rewrite -Hls.
        move=> o_a  ls IHs .
        case: o_a ; last first.
        move=> m ls_H a.
        destruct m=>//=.
        move=>/fixlist_empty_is_top_heavy.


        (* stuck here *)

       (*  move=> H. *)
       (*  suff: (is_true *)
       (*  (@fixlist_is_top_heavy m *)
       (*     (@tuple m (option (Equality.sort A)) *)
       (*        (@behead_tuple (S m) (option (Equality.sort A)) *)
       (*           (@Tuple (S m) (option (Equality.sort A)) *)
       (*              (@cons (option (Equality.sort A)) (@None (Equality.sort A)) ls) ls_H)) *)
       (*        (fun sP : is_true (@eq_op nat_eqType (@size (option (Equality.sort A)) ls) m) => *)
       (*         @Tuple m (option (Equality.sort A)) ls sP))) = (@fixlist_is_top_heavy m *)
       (* (@tuple m (option (Equality.sort A)) *)
       (*    (@behead_tuple (S m) (option (Equality.sort A)) *)
       (*       (@tuple (S m) (option (Equality.sort A)) *)
       (*          (@cons_tuple m (option (Equality.sort A)) (@Some (Equality.sort A) a) *)
       (*             (@tuple m (option (Equality.sort A)) *)
       (*                (@behead_tuple (S m) (option (Equality.sort A)) *)
       (*                   (@Tuple (S m) (option (Equality.sort A)) *)
       (*                      (@cons (option (Equality.sort A)) (@None (Equality.sort A)) ls) ls_H)) *)
       (*                (fun sP : is_true (@eq_op nat_eqType (@size (option (Equality.sort A)) ls) m) => *)
       (*                 @Tuple m (option (Equality.sort A)) ls sP))) *)
       (*          (fun sP : is_true (@eq_op nat_eqType (S (@size (option (Equality.sort A)) ls)) (S m)) => *)
       (*           @Tuple (S m) (option (Equality.sort A)) *)
       (*             (@cons (option (Equality.sort A)) (@Some (Equality.sort A) a) ls) sP))) *)
       (*    (fun sP : is_true (@eq_op nat_eqType (@size (option (Equality.sort A)) ls) m) => *)
       (*     @Tuple m (option (Equality.sort A)) ls sP)))). *)
       (*  by move=> <-. *)

       (*  suff Hequal: ((@tuple m (option (Equality.sort A)) *)
       (*       (@behead_tuple (S m) (option (Equality.sort A)) *)
       (*          (@tuple (S m) (option (Equality.sort A)) *)
       (*             (@cons_tuple m (option (Equality.sort A)) (@Some (Equality.sort A) a) *)
       (*                (@tuple m (option (Equality.sort A)) *)
       (*                   (@behead_tuple (S m) (option (Equality.sort A)) *)
       (*                      (@Tuple (S m) (option (Equality.sort A)) *)
       (*                         (@cons (option (Equality.sort A)) (@None (Equality.sort A)) ls) ls_H)) *)
       (*                   (fun sP : is_true (@eq_op nat_eqType (@size (option (Equality.sort A)) ls) m) => *)
       (*                    @Tuple m (option (Equality.sort A)) ls sP))) *)
       (*             (fun sP : is_true (@eq_op nat_eqType (S (@size (option (Equality.sort A)) ls)) (S m)) => *)
       (*              @Tuple (S m) (option (Equality.sort A)) *)
       (*                (@cons (option (Equality.sort A)) (@Some (Equality.sort A) a) ls) sP))) *)
       (*       (fun sP : is_true (@eq_op nat_eqType (@size (option (Equality.sort A)) ls) m) => *)
       (*        @Tuple m (option (Equality.sort A)) ls sP)) = (@tuple m (option (Equality.sort A)) *)
       (*       (@behead_tuple (S m) (option (Equality.sort A)) *)
       (*          (@Tuple (S m) (option (Equality.sort A)) *)
       (*             (@cons (option (Equality.sort A)) (@None (Equality.sort A)) ls) ls_H)) *)
       (*       (fun sP : is_true (@eq_op nat_eqType (@size (option (Equality.sort A)) ls) m) => *)
       (*        @Tuple m (option (Equality.sort A)) ls sP))). *)

       (*  by dependent rewrite Hequal. *)
       (*  f_equal. *)
       (*  Set Printing All. *)
       (*  move=> _ _ _ _ . *)

       (*  suff Hiseq: ((@behead_tuple (S m) (option (Equality.sort A)) *)
       (*    (@tuple (S m) (option (Equality.sort A)) *)
       (*       (@cons_tuple m (option (Equality.sort A)) (@Some (Equality.sort A) a) *)
       (*          (@tuple m (option (Equality.sort A)) *)
       (*             (@behead_tuple (S m) (option (Equality.sort A)) *)
       (*                (@Tuple (S m) (option (Equality.sort A)) *)
       (*                   (@cons (option (Equality.sort A)) (@None (Equality.sort A)) ls) ls_H)) *)
       (*             (fun sP : is_true (@eq_op nat_eqType (@size (option (Equality.sort A)) ls) m) => *)
       (*              @Tuple m (option (Equality.sort A)) ls sP))) *)
       (*       (fun sP : is_true (@eq_op nat_eqType (S (@size (option (Equality.sort A)) ls)) (S m)) => *)
       (*        @Tuple (S m) (option (Equality.sort A)) *)
       (*          (@cons (option (Equality.sort A)) (@Some (Equality.sort A) a) ls) sP)))  = (@behead_tuple (S m) (option (Equality.sort A)) *)
       (*    (@Tuple (S m) (option (Equality.sort A)) (@cons (option (Equality.sort A)) (@None (Equality.sort A)) ls) *)
       (*       ls_H))). *)
       (*  by dependent rewrite Hiseq. *)
       (*  move=> //=. *)
       
       (*  by move=> <-. *)

       (*  suff: (is_true *)
       (*  (@fixlist_is_top_heavy m *)
       (*     (@tuple m (option (Equality.sort A)) *)
       (*        (@behead_tuple (S m) (option (Equality.sort A)) *)
       (*           (@Tuple (S m) (option (Equality.sort A)) *)
       (*              (@cons (option (Equality.sort A)) (@None (Equality.sort A)) ls) ls_H)) *)
       (*        (fun sP : is_true (@eq_op nat_eqType (@size (option (Equality.sort A)) ls) m) => *)
       (*         @Tuple m (option (Equality.sort A)) ls sP))) = (@fixlist_is_top_heavy m *)
       (* (@tuple m (option (Equality.sort A)) *)
       (*    (@behead_tuple (S m) (option (Equality.sort A)) *)
       (*       (@tuple (S m) (option (Equality.sort A)) *)
       (*          (@cons_tuple m (option (Equality.sort A)) (@Some (Equality.sort A) a) *)
       (*             (@tuple m (option (Equality.sort A)) *)
       (*                (@behead_tuple (S m) (option (Equality.sort A)) *)
       (*                   (@Tuple (S m) (option (Equality.sort A)) *)
       (*                      (@cons (option (Equality.sort A)) (@None (Equality.sort A)) ls) ls_H)) *)
       (*                (fun sP : is_true (@eq_op nat_eqType (@size (option (Equality.sort A)) ls) m) => *)
       (*                 @Tuple m (option (Equality.sort A)) ls sP))) *)
       (*          (fun sP : is_true (@eq_op nat_eqType (S (@size (option (Equality.sort A)) ls)) (S m)) => *)
       (*           @Tuple (S m) (option (Equality.sort A)) *)
       (*             (@cons (option (Equality.sort A)) (@Some (Equality.sort A) a) ls) sP))) *)
       (*    (fun sP : is_true (@eq_op nat_eqType (@size (option (Equality.sort A)) ls) m) => *)
       (*     @Tuple m (option (Equality.sort A)) ls sP)))). *)
       (*  by move=> <-. *)
       (*  auto. *)
       (*  rewrite /fixlist_is_top_heavy//=. *)
       (*  by rewrite functional_extensionality. *)
       (*  by rewrite (proof_irrelevance _). *)
       (*  move=> H. *)

       (*  move=> Hrewrite. *)
       (*  by rewrite (Hrewrite m H); exact H. *)
       (*  rewrite /fixlist_is_empty => /eqP His_empty. *)
       (*  destruct ls => //=. *)
       (*  rewrite /fixlist_is_top_heavy//=. *)
       (*  move: (ls_H). *)
       (*  move/eqP: ls_H => Hls. *)
       (*  rewrite -Hls //=. *)

        Admitted.

    Lemma fixlist_insert_rewrite (m : nat) (ls : fixlist m) (a : A) :
        fixlist_is_top_heavy ls -> fixlist_length ls < m -> fixlist_unwrap (fixlist_insert ls a) = rcons (fixlist_unwrap ls)  a.
      Proof.
        Admitted.







    Lemma fixlist_length_unwrap_ident : forall (m : nat) (ls : fixlist m), length (fixlist_unwrap ls) = fixlist_length ls.
    Proof.
        (* TODO(Kiran): Complete this proof *)
        Admitted.

End fixlist.

