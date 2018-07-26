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

Lemma size_ncons_nil (A : Type) (a : A) (n : nat): (size (ncons n a [::])) == n.
Proof.
    rewrite size_ncons => //=.
    by rewrite addn0.
Qed.

Section fixlist.
    Variable A : eqType.
    Variable n' : nat.
Definition fixlist n := n.-tuple (option A).

    Definition fixlist_empty n : fixlist n :=
        @Tuple n
            (option A) 
            (ncons n None [::])
            (size_ncons_nil   None n).

    (* I wanted to write this, but it wouldn't type check*)
    (* Fixpoint fixlist_insert (m : nat) (list : fixlist m.+1) (a : A) : fixlist m.+1 :=
        match tnth list (inord m) return fixlist m.+1  with
            | None => [tuple of (Some value) :: [tuple of behead list]]
            | Some value => match m return fixlist m.+1 with
                                | 0 => list
                                | m'.+1 =>  [tuple of (Some value) :: fixlist_insert m' [tuple of behead list] a ]
                                end
            end. *)


    Lemma fixlist_insert (m : nat) (list : fixlist m) (a : A) : fixlist m.
        move: a.
        move: list.
        elim m.
        move=> list a.
            exact list. (* can not insert anything into an empty list*)
        move=> m0 fixlist_insert list a.
        destruct (tnth list (inord (m0.+1))) eqn: H; last first.
            exact [tuple of (Some a) :: [tuple of behead list]].
            exact [tuple of (Some s) :: [tuple of fixlist_insert (ntuple_tail list) a]].
    Defined.




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
    Defined.
   

    (* Fixpoint fixlist_set_nth (m : nat) (list : fixlist  m.+1) (a : A) (n : nat) : fixlist m.+1 :=
         match m, n with
            | m'.+1, n'.+1 => [tuple of ntuple_head list ::  @fixlist_remove m' (ntuple_tail list) n']
            | 0, n'.+1 => [tuple of [:: ntuple_head list]]
            | m'.+1, 0 => [tuple of (Some a) :: (ntuple_tail list)] 
            | 0, 0 =>  [tuple of [:: Some a] ]
       end. *)

    Fixpoint fixlist_set_nth (m : nat) (list : fixlist  m) (a : A) (n : nat) : fixlist m.
    Proof.
        induction  m  as [|m'] eqn: Hm.
        induction n as [|n''] eqn: Hn.
            (* 0, 0 *)
            exact list.
            (* 0, n.+1 *)
            exact list.
        case n eqn: Hn.
            (* m.+1, 0 *)
            exact [tuple of (Some a) :: (ntuple_tail list)].
            (* m'.+1, n'.+1 *)
            exact [tuple of ntuple_head list ::  @fixlist_set_nth m' (ntuple_tail list) a n0].
    Defined.

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



    Fixpoint fixlist_length (m : nat) (list : fixlist  m) : nat. 
        case m eqn:H.
            exact 0.
        case (ntuple_head list).
            move=> a.
            exact (1 + fixlist_length n (ntuple_tail list)).
            exact (fixlist_length n (ntuple_tail list)).
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

    Fixpoint fixlist_contains (m : nat) (a : A) (list : fixlist m) : bool. 
        case m eqn: H.
            exact false.
        case (ntuple_head list).
            move=> a'.
            case (a' == a).
                exact true.
                exact (fixlist_contains n a (ntuple_tail list)).
            exact (fixlist_contains n a (ntuple_tail list)).
    Defined. 

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




    Definition fixlist_unwrap (m : nat) (list : fixlist m) : seq A :=
        flatten (map (fun o_value => match o_value with
                            | Some value => [:: value]
                            | None => [::]
                            end) list).
    
    Lemma fixlist_length_unwrap_ident : forall (m : nat) (ls : fixlist m), length (fixlist_unwrap ls) = fixlist_length ls.
    Proof.
        (* TODO(Kiran): Complete this proof *)
        Admitted.

End fixlist.

