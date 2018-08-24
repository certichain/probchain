From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat seq ssrfun eqtype bigop fintype choice .

From mathcomp.ssreflect
Require Import tuple.

Require Import Reals Fourier FunctionalExtensionality.
From infotheo
Require Import proba ssrR Reals_ext logb ssr_ext ssralg_ext bigop_ext Rbigop .

Require Import Nsatz.

Require Import Bvector.


From Probchain
Require Import ValidSchedule Deterministic Comp Notationv1 BlockChain Protocol OracleState BlockMap InvMisc Parameters FixedList FixedMap.

Set Implicit Arguments.

Variable probability_constant : R.

Lemma Rle_big_eqP (A : finType) (f g : A -> R) (P : pred A) :
   (forall i : A, P i -> f i <= g i) ->
   \rsum_(i | P i) g i = \rsum_(i | P i) f i <->
   (forall i : A, P i -> g i = f i).
Proof.
  move=> hf; split => [/Rle_big_eq H//=|].
    by  exact (H hf).
    move=> H.
      by  exact (@eq_bigr _ _ _ A _ P  g f H).
Qed.

Definition schedule_produces_none (s: seq.seq RndGen) :=
    o_w' <-$ world_step initWorld s;
    r <- if o_w' is Some(w) then false else true;
    ret r.

Definition p_schedule_produces_none (s:seq.seq RndGen) :=
    evalDist (world_step initWorld s) None.




Lemma local_state_base_nth addr : tnth initLocalStates addr = (initLocalState, false).
Proof.
  rewrite (tnth_nth (initLocalState, false)).
  rewrite /initLocalStates.
  destruct addr as [m Hm].
  rewrite /tnth/ncons/ssrnat.iter//=.
  move: m Hm.
  elim n_max_actors => //=.
  move=> n IHn m .
  case m => //=.
Qed.

Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.ProofIrrelevance.

(* Lemma honest_max_activation_base : honest_activation (world_global_state initWorld) = Some (Ordinal valid_n_max_actors). *)
(*  Proof. *)
(*  rewrite /honest_activation. *)
(*  rewrite /initWorld //=. *)
(*  move: valid_n_max_actors=>E.  *)
(*  move: (@Ordinal n_max_actors 0)=>o. *)
(*  suff X : (fun H => if (tnth initLocalStates (o H)).2 then None else Some (o H)) = fun _ =>  if (tnth initLocalStates (o E)).2 then None else Some (o E).                *)
(*    by rewrite X; rewrite E local_state_base_nth. *)
(*  apply: functional_extensionality=>G. *)
(*  by rewrite (proof_irrelevance _ E G). *)
(* Qed. *)


Notation "'P[' a '===' b ']'" := (evalDist a b).
Notation "'P[' a ']'" := (evalDist a true).
Notation "'E[' a ']'" := (expected_value a).
Notation " a '|>' b " := (w_a <-$ a; b w_a) (at level 50).
Notation " w '>>=' a '<&&>' b " := (fun w => ret (a  && b )) (at level 49).
Notation " w '>>=' a '<||>' b " := (fun w => ret (a  || b )) (at level 49).



Lemma addRA_rsum  (A : finType) f g : 
  \rsum_(i in A) (f i + g i)%R = (\rsum_(i in A) f i + \rsum_(i in A) g i)%R .
Proof.
  rewrite unlock.
  elim index_enum => //=.
  have H : R0 = 0.
    by [].
  move: (addR0   ).
  rewrite /right_id => H'.
  move: (H' R0).
  by rewrite H. (* there's some issues with the types 0 doesn't want to auto-coerce  to R0 *)
  move=> x xs IHn.
  by rewrite IHn addRA (addRC (f x) (g x)) -(addRA (g x)) (addRC (g x)) -(addRA (f x + _)).
Qed.
  

Lemma prob_disjunctive_distr (f g : option World -> bool) : forall sc,
   P[ world_step initWorld sc |> w >>= f w <||> g w ] =
    (P[ world_step initWorld sc |> w >>= f w <&&> ~~ g w] + 
    (* P[ world_step initWorld sc |> (fun x => ret (f x && ~~ g x))] +  *)
    P[ world_step initWorld sc |> w >>= ~~ f w <&&>  g w ] + 
    P[ world_step initWorld sc |> w >>=  f w <&&>  g w ])%R.
Proof.
  move => sc; elim sc  => //.
    rewrite /evalDist/DistBind.d/DistBind.f//=.
    rewrite -addRA_rsum.
    rewrite -addRA_rsum.
    apply Rle_big_eqP; move=> o_w' _ //=;
    case (f o_w'); case (g o_w'); rewrite /Dist1.f => //=.
    rewrite mulR0 mulR1 add0R add0R.
    by apply Rle_refl.
    rewrite mulR0 mulR1 addR0 addR0.
    by apply Rle_refl.
    rewrite mulR0 mulR1 addR0 add0R.
    by apply Rle_refl.
    rewrite mulR0 addR0 addR0.
    by apply Rle_refl.
    by rewrite mulR0 mulR1 addR0 add0R.
    by rewrite mulR1 mulR0 addR0 addR0.
    by rewrite mulR1 mulR0 add0R addR0.
    by rewrite mulR0 add0R add0R.
  (* Now for the inductive case *)
    move=> x xs IHn//.
    rewrite /evalDist/DistBind.d/DistBind.f/makeDist//=.
    rewrite -addRA_rsum.
    rewrite -addRA_rsum.
    apply Rle_big_eqP; move=> o_w' _ //.
    case (f o_w'); case (g o_w'); rewrite /Dist1.f => //=.
    rewrite mulR0 mulR1 add0R add0R.
      by apply Rle_refl.
    rewrite mulR0 mulR1 addR0 addR0.
    by apply Rle_refl.
    rewrite mulR0 mulR1 addR0 add0R.
    by apply Rle_refl.
    rewrite mulR0 addR0 addR0.
    by apply Rle_refl.
    have HINR1 : INR 1 = 1.
      by [].

    have HINR0 : INR 0 = 0.
      by [].

    case (f o_w'); case (g o_w'); rewrite /Dist1.f => //=.
    by rewrite mulR1 mulR0 addR0 add0R.
    by rewrite mulR0 addR0 addR0 mulR1.
    by rewrite mulR0 addR0 mulR1 add0R.
    by rewrite mulR0 addR0 addR0.
Qed.
  

Lemma prsumr_eq1P :
forall (pr : dist [finType of bool]),
 pr true = 0 <-> pr false = 1.
Proof.
  move=> [[f Hposf] Hdist].
  split => //=.
  move=> Htrue0.
  move: Hdist.
  rewrite unlock; rewrite /index_enum/[finType of bool]//=.
  by rewrite unlock; rewrite /index_enum//=; rewrite Htrue0 add0R addR0.
  move=> Hfalse1.
  move: Hdist.

  rewrite unlock; rewrite /index_enum/[finType of bool]//=.
  rewrite unlock; rewrite /index_enum//=.
  rewrite Hfalse1 addR0.
  by move=> /eqP; rewrite eq_sym -subR_eq subRR; move=> /eqP.
Qed.


Lemma prsumr_negP :
forall (pr : dist [finType of bool]),
 1 - pr true = pr false.
Proof.
  move=> [[f Hposf] Hdist] //=.
  move: Hdist.
  rewrite unlock; rewrite /index_enum/[finType of bool]//=.
  rewrite unlock; rewrite /index_enum//=.
  by rewrite addR0 addRC; move=>/eqP; rewrite eq_sym -subR_eq; move=>/eqP.
Qed.


Lemma prob_compl' (f : option World -> bool) : forall sc,
   P[ world_step initWorld sc |> (fun x => ret f x )] = 0 ->
    P[ world_step initWorld sc |> (fun x => ret (~~ f x))] = 1.
Proof.
  move=> sc.
  move=>/prsumr_eq1P.
  rewrite /evalDist//=.
Qed.


Lemma prob_compl (f : option World -> bool) : forall sc,
   1 - P[ world_step initWorld sc |> (fun x => ret f x )] =
    P[ world_step initWorld sc |> (fun x => ret (~~ f x))].
Proof.
  move => sc.
  (* trivial *)
  by rewrite prsumr_negP.
Qed.

Definition world_executed_to_round w r : bool :=
(has
      (* if there is a record *)
      (fun pr => 
         let: (rec_chain, rec_round, rec_actr)  := pr in 
         
          (* of any actor adopting/broadcasting a chain *)
          (* at round r (* this is to check that the world executed to this round *) *)
          (rec_round == r)%bool
           )
      (fixlist_unwrap (world_adoption_history w))
   ).

Definition honest_actor_has_chain_at_round w addr c r : bool := 
   (has
      (* there is a record *)
      (fun pr => 
         let: (rec_chain, rec_round, rec_actr)  := pr in 
         [&&
            (* of the block adopting/broadcasting the chain *)
            (rec_chain  == c),
          (* at round r or earlier *)
          (nat_of_ord rec_round <= r)%nat &
          (* by the actor *) 
          (nat_of_ord rec_actr == addr) ])
      (fixlist_unwrap (world_adoption_history w))
   )
.

Definition actor_n_has_chain_length_at_round w l addr r : bool :=
   (has
      (* there is a record *)
      (fun pr => 
         let: (rec_chain, rec_round, rec_actr)  := pr in 
         [&&
          (* of the block adopting/broadcasting the chain *)
          (fixlist_length rec_chain  == l),
          (* at round r *)
          (eq_op ( rec_round) ( r)) &
          (* by the actor *) 
          (nat_of_ord rec_actr == addr) ])
      (fixlist_unwrap (world_adoption_history w))
   ).



Definition actor_n_has_chain_length_ge_at_round w l addr (r : 'I_N_rounds) : bool :=
   (has
      (* then there is a record *)
      (fun pr => 
         let: (rec_chain, rec_round, rec_actr)  := pr in 
         [&&
          (* of the block adopting/broadcasting a chain of at least length l *)
          (fixlist_length rec_chain >= l)%nat,
          (* at round r or earlier *)
          (nat_of_ord rec_round <= nat_of_ord r)%nat &
          (* by the actor *) 
          (nat_of_ord rec_actr == addr) ])
      (fixlist_unwrap (world_adoption_history w))
   ).


(* Note: stopped here - might need to  add some extra components to strengthen this principle*)



(* note: rewrite this to use a weaker statement - rather than reasoning about the list
 directly, use the length instead *)
Definition chain_growth_pred w :=
  [forall r : 'I_N_rounds,
      forall l : 'I_Maximum_blockchain_length,
          forall addr: 'I_n_max_actors,
              (* if there is an actor with a chain of length l at round r *)
              actor_n_has_chain_length_at_round w (nat_of_ord l) (nat_of_ord addr) r
              ==>
              (*then*)
              (* forall rounds *)
              (* if the round is after the current round + delta - 1 *)
              [forall s : 'I_N_rounds, 
                  (nat_of_ord r + delta - 1 <= nat_of_ord s)%nat ==>
                        (* and the world executed to the round *)
                          world_executed_to_round w s ==>
                          (*then*)
                          [forall o_addr : 'I_n_max_actors,
                              (* all actors, if honest *)
                              (actor_n_is_honest w o_addr) ==>

                               (* have a chain of length of at least
                                 l + n_hashed_blocks r (s - delta) at round s *)
                                  actor_n_has_chain_length_ge_at_round
                                        w
                                        ((nat_of_ord l) + nat_of_ord (no_bounded_successful_rounds w r (s - delta)))
                                        o_addr
                                        s

                          ]
                ]

      ].

Definition chain_growth_pred_wrapper o_w :=
  match o_w with
    | None => false 
    | Some w => ~~ chain_growth_pred w
  end.

Lemma prob_some_wP : forall xs,
    (forall w, P[ (world_step initWorld xs) === (Some w) ] = 0) <->
            (P[ (world_step initWorld xs) |> (fun o_w => ret (isSome o_w)) ] = 0).
  Proof.
    split.
    rewrite {2}/evalDist/DistBind.d/makeDist/DistBind.f/pmf/pos_f-/evalDist.
    move=> H.
    apply prsumr_eq0P.
    move=> o_w' _.
    by apply Rmult_le_pos; [case (evalDist _); move=> pos_f Hdist; case pos_f => f Hposf; exact (Hposf _) | case (Dist1.d _); move => [f Hposf] Hdist; exact (Hposf _) ].
    move=> o_w' _.
    by case o_w' => //=; [move => w; rewrite (H w) mul0R | rewrite /Dist1.f//=; rewrite mulR0 ].

    rewrite /evalDist.
    rewrite {1}/DistBind.d.
    rewrite /DistBind.f.
    rewrite /makeDist.
    rewrite/pmf.
    rewrite /pos_f.
    move => /prsumr_eq0P H.
    suff Hobv:
(forall a : [finType of option World],
       a \in [finType of option World] ->
       0 <=
       (let (pos_f, _) :=
          let (pmf, _) :=
            (fix evalDist (A : finType) (c : Comp A) {struct c} : dist A :=
               match c in (Comp t) return (dist t) with
               | Ret A0 a0 => Dist1.d (A:=A0) a0
               | @Bind A0 B c0 f => DistBind.d (evalDist B c0) (fun b : B => evalDist A0 (f b))
               | @Rnd A0 n n_valid => Uniform.d n_valid
               end) [finType of option World] (world_step initWorld xs) in
          pmf in
        pos_f) a * (let (pos_f, _) := let (pmf, _) := Dist1.d (A:=bool_finType) a in pmf in pos_f) true).
    move: (H Hobv) => Heq0.
    clear H Hobv.
    move=> w.
    move: ((Heq0) (Some w) )=>H.
    clear Heq0.
    suff Hsimpl: (Some w \in [finType of option World]) .
    move: (H Hsimpl) => /Rmult_integral.
    clear  H Hsimpl.
    case => [Heq0|].
    by rewrite Heq0.
    by rewrite /Dist1.f; case (true == Some w)%bool eqn: H; rewrite H => //= /R_one_zero Hinc; inversion Hinc.
    by [].
    clear H.
    move=> o_w _.
    by apply Rmult_le_pos; [case (evalDist _); move=> pos_f Hdist; case pos_f => f Hposf; exact (Hposf _) | case (Dist1.d _); move => [f Hposf] Hdist; exact (Hposf _) ].
Qed.

   
 Lemma itoj_eq_0 s r : (s < r)%nat -> itoj r s = [::].
  Proof.
    rewrite /itoj; move=> Hsltr.
    have H: ((s - r)%nat = 0%nat). by apply /eqP; rewrite subn_eq0 leq_eqVlt; apply /orP; right.
    rewrite H => //=.
  Qed.


Lemma no_bounded_successful_rounds_eq0 : forall w r s, (s < r \/ (eq_op r s /\ eq_op r 0))%nat -> nat_of_ord (no_bounded_successful_rounds w r s) = 0%nat.
Proof.
  move=> w r s Hrs; rewrite /no_bounded_successful_rounds/no_bounded_successful_rounds'; apply/eqP => //=.
  destruct Hrs .
  rewrite itoj_eq_0 => //=.
  suff Hgeq: [eta Ordinal (n:=N_rounds) (m:=0)] = (fun x => Ordinal (n:=N_rounds) (m:=0) valid_N_rounds).
  rewrite Hgeq.
  rewrite valid_N_rounds => //=.
 apply: functional_extensionality=> G.
  by rewrite (proof_irrelevance _ valid_N_rounds G).
  (* TODO(Kiran): rewrite the underlying definition to not use dependant typing *)
  destruct H as [Heqrs Heq0].
  move/eqP: Heqrs=> <-.
  move/eqP: Heq0=> -> //=.
  suff Hgeq: [eta Ordinal (n:=N_rounds) (m:=0)] = (fun x => Ordinal (n:=N_rounds) (m:=0) valid_N_rounds).
  rewrite Hgeq.
  rewrite valid_N_rounds => //=.
 apply: functional_extensionality=> G.
  by rewrite (proof_irrelevance _ valid_N_rounds G).
Qed. 

Lemma no_bounded_successful_rounds_ext sc w r s : 
  (P[ world_step initWorld sc === Some w] <> 0) ->
        (~~ bounded_successful_round w s) ->
          no_bounded_successful_rounds w r s = no_bounded_successful_rounds w r s.+1.
Proof.
  (* TODO(Kiran): Complete this proof *)
Admitted.
About Ordinal.

Lemma  actor_has_chain_length_ext w l o_addr s Hsv Hs1v :
  actor_n_has_chain_length_ge_at_round w l o_addr (@Ordinal  N_rounds s Hsv) ->
  actor_n_has_chain_length_ge_at_round w l o_addr (@Ordinal  N_rounds s.+1 Hs1v).
Proof.
  (* TODO(Kiran): Complete this proof *)
Admitted.

Lemma  actor_has_chain_length_weaken w l o_addr s l':
  (l' <= l)%nat ->
  actor_n_has_chain_length_ge_at_round w l o_addr s ->  
  actor_n_has_chain_length_ge_at_round w l' o_addr s.
Proof.
  rewrite /actor_n_has_chain_length_ge_at_round !has_count.
  rewrite leq_eqVlt; move=>/orP[/eqP -> |] //=.
  move=>  Hvalid.  
  induction (fixlist_unwrap _) => //=.
  have add_lt0 x y: (0 < x + y)%nat = ((0 <x)%nat && (0 <= y)%nat) || ((0 <=x)%nat && (0 < y)%nat).
    by induction x => //=.
  rewrite !add_lt0; move=>/orP; case => //= ;last first.
  by move=> /IHl0 Hv; apply/orP; right.
  move=>/andP [ Hgt0  Hlt0] //=.
  apply/orP.
  left .
  apply/andP;split.
  move: Hgt0.
  have bool_gt0 (b : bool) : (0 < b)%nat = b. by case b.
  move: a => [[b r] a].
  rewrite !bool_gt0 //=.
  move=>/andP [l_leq /andP [rs eq_addr]].
  apply/andP; split; [|apply/andP] => //=.
  have Hlt_trans x y z : (x <= y)%nat -> (y <= z)%nat  -> (x <= z)%nat.
    by move=>/leq_trans Himpl; move=> /Himpl.
  by apply (Hlt_trans l' l); [apply ltnW | ] .
  move: Hlt0.
  rewrite leq_eqVlt ; move=>/orP[/eqP |] //=.
Qed.



Lemma world_executed_to_weaken w s Hs'valid Hsvalid:
  world_executed_to_round w (Ordinal (n:=N_rounds) (m:=s.+1) Hsvalid) ->
  world_executed_to_round w (Ordinal (n:=N_rounds) (m:=s) Hs'valid).
Proof.
  (* TODO(Kiran): Complete this proof *)
Admitted.

Lemma addr_ltn a b c:
   (a + b < c)%nat -> (a < c)%nat.
  Proof.
    by move=>/(ltn_addr b); rewrite ltn_add2r.
    Qed.





(*
  If an honest party has a chain of length l,
  then by round r + delta -1, every other party will have a chain of length at least l
*)
(* Note: we can only see the adoptions - so we have to say there is a round k earlier or at r, when the party
adopted a chain of length l *)
Lemma chain_growth_weak sc w l (r : 'I_N_rounds) :
  (* make sure that the world is valid *)
(P[ world_step initWorld sc === Some w] <> 0) ->
(exists (addr : 'I_n_max_actors) (k : 'I_N_rounds),
  (* if an honest party has a chain of length l at r *)
  (nat_of_ord k <= nat_of_ord r)%nat && actor_n_has_chain_length_at_round w l addr k) ->
  (* then at r + delta - 1, every actor would have broadcasted a chain of length at least l*)
  (* we're using this forall quantification here to allow creating a ordinal type without having to use dependant types*)
  forall s,
     (eq_op (r + delta - 1)%nat (nat_of_ord s)) ->
      (* and the world executed to the round *)
      world_executed_to_round w s ->
      (*then *)
      forall o_addr : 'I_n_max_actors,
          (* all actors, if honest *)
          (actor_n_is_honest w o_addr) ->
            (* have a chain of length of at least
              l  *)
              actor_n_has_chain_length_ge_at_round
                    w
                    l
                    o_addr
                    s.

Proof.
  (* TODO: Complete this proof *)

Admitted.

Lemma prob_chain_ext : forall xs x, 
 (forall w, P[ (world_step initWorld xs) === (Some w) ] = 0) -> (forall w, P[ world_step initWorld (x::xs) === Some w ] = 0).
  Proof.
    move=> xs x.
   (* elim xs => // . *)
    rewrite /evalDist//=.
    rewrite /Dist1.f /DistBind.f/Dist1.d.
    move=> Hbase w.
    apply prsumr_eq0P.
    move=> o_w' _.
    case o_w'.
    move=> w0.
    by rewrite (Hbase w0) mul0R; exact (Rle_refl (INR 0)).
    by apply Rmult_le_pos; [case (evalDist _); move=> pos_f Hdist; case pmf => f Hposf; exact (Hposf None) | by case (makeDist _); move=> pos_f Hdist; case pmf => f Hposf;exact (Hposf (Some w))].
   
    move=> o_w' _.
    by case o_w' => [w0|]; [rewrite (Hbase w0) mul0R | rewrite /makeDist/ Dist1.f//=; rewrite mulR0 ].
Qed.


  (* Probably not the best way to do this *)
  Lemma R_w_distr (A : finType) (f g : A -> R) : (forall w : A, (f w * g w) = 0) -> (forall w : A, (f w) = 0) \/ (exists w : A, (g w) = 0).
    move=> H.
    case ([forall w, f w == 0]) eqn: Hall0.
    by move/eqfunP: Hall0 => Hall; left.
    right.
    apply/exists_eqP.
    move/negP/negP: Hall0.
    rewrite negb_forall=>/existsP [w /eqP Hw].
    by move: (H w) => /Rmult_integral [Hf0 | Hg0]; [move: (Hw Hf0) => [] | apply /exists_eqP; exists w].
  Qed.


Lemma prob_chain_growth : forall sc,
   P[ world_step initWorld sc |> (fun w => ret chain_growth_pred_wrapper w) ] = R0.
Proof.
  move=> sc.
  (* let's convert these probability distributions into something easier to work with*)
  apply/prsumr_eq0P.
  (* first, let's handle the obvious stuff - that the distributions are positive functions *)
    move=> o_w _.
    rewrite /Dist1.f//=.
    case (evalDist _) => [[f Hfpos] Hb].
    apply Rmult_le_pos => //=.
    rewrite /Dist1.f//=.
    case (true == chain_growth_pred_wrapper _)%bool=> //=.
      by exact (Rle_refl (INR 0)).

  move=> o_w _.
  case o_w ; last first.
  (* let's also dispose of the obvious case when the world being tested is none *)
    move => //=.
    have H: (Dist1.f false true) = 0.
      by [].
    by rewrite H mulR0.

  (* we don't need the option world, as we know it must be of the some variant*)
  clear o_w.
  (* now, were in the main part of the function. let's do some induction to prove this *)
  elim: sc .
  (* base case *) 
  rewrite /evalDist/DistBind.d/DistBind.f/Dist1.d//=.
  move=>w.
  (* now let's deal with the simple case when the result is world being tested is not the initial world*) 
  case (w == initWorld)%bool eqn: H; last first.
  move/eqP:H => H.
  have Hzr : (Some w == Some initWorld)%bool = false.
    apply/eqP.
    move=> assum.
    by injection assum => /H//=.
  by rewrite /Dist1.f Hzr //= mul0R  .
  (* if the world being tested is the initial world... *)
  move/eqP: H => ->.
  rewrite /Dist1.f// .
  have H: (Some initWorld == Some initWorld)%bool.
    by [].
  rewrite H //= mul1R.
  clear H.
  (* we can rewrite our probabilistic statement as one about the equality of the underlying types *)
  suff H: chain_growth_pred initWorld => //=.
  rewrite H => //=.

  (* the rest of the base case can be proven simply by computation *)
  rewrite /chain_growth_pred. apply /forallP => r ; apply /forallP => l; apply /forallP => addr.
  rewrite /actor_n_has_chain_length_at_round//=; rewrite /initWorldAdoptionHistory.
  have Hfixlist_empty A v  : @fixlist_unwrap A v (@fixlist_empty A v) = [::].
  by elim v => //=.
  
  rewrite Hfixlist_empty //=.

  (* now for the inductive case *)
  move=> x xs Hind.
  move: (Hind).
  move=> /R_w_distr H.
  (* either the world is unreachable, or it does not satisfy the chain growth predicate *)
  case: H => [/prob_chain_ext Hunr | Hreal].
  (* if the world is unreachable, the result is trivial *)
  by move=> w; rewrite (Hunr ) mul0R.
  clear Hreal.

  (* if the word is reachable, the key point to invalidate is the chain growth predicate *)
  (* let's dispose the unnecassary components, to make the proof clearer *)
  move=> w.
  move: (Hind w) => /Rmult_integral Hv.
  clear Hind.
  case: Hv;last first.
    by move=> ->; rewrite mulR0.
  (* a little unsure of this term - this doesn't seem to provide anything of value*)
  rewrite -/evalDist => Hpr_invalid. 
  (* if the world is unreachable, the result is trivial*)
  case (P[ world_step initWorld (x :: xs) === Some w] == 0)%bool eqn: H.
    by move/eqP: H => ->; rewrite mul0R.
  move/eqP: H => Hpr_valid.
  apply /Rmult_eq_0_compat.
  right.

  (* Now, let's convert this probabilistic statement into one about the truth of the underlying expression *)
  rewrite /chain_growth_pred_wrapper/chain_growth_pred.
  rewrite /Dist1.d/Dist1.f//=.
  have H_INRP a :  a = false -> INR a = 0. by move=> ->.
  apply H_INRP; apply/negP/negP/forallP => r; apply/forallP => l.
  (* we can use the functions provided by fintype to convert this deterministic statement into a prop one *)
  apply/forallP=>addr; apply/implyP=> H_holds_chain; apply/forallP=> s.
  apply/implyP=>H_valid_range.
  apply/implyP=>H_world_exec.
  apply/forallP=> o_addr.
  apply/implyP=> H_is_honest.

  (* now can be proven in terms of simple logical operations! *) 
  (* now for the main part of the proof *)
  (* use the following tactics at this point in the proof to see the prop formulation of the chain growth lemma *)
  (* move: r c addr H_holds_chain s Hvr o_addr H_is_honest Hwround . *)
  move:    H_valid_range H_world_exec o_addr H_is_honest .
  destruct s as [s Hsvalid]; destruct r as [r Hrvalid] => //=.
  induction s ; rewrite leq_eqVlt => /orP; case => //=.
  rewrite subn_eq0;rewrite leq_eqVlt => /orP; case => //=.
  rewrite sub0n; rewrite no_bounded_successful_rounds_eq0.
  rewrite addn0.
  suff Hexist: (exists (addr0 : 'I_n_max_actors) (k : 'I_N_rounds),
                   (k <= (Ordinal Hrvalid))%nat && actor_n_has_chain_length_at_round w l addr0 k).

  move=> /eqP Hrdelta_eq1 H_world_exec o_addr Haddr_hon.
  apply (chain_growth_weak (x::xs) w l (Ordinal Hrvalid) Hpr_valid Hexist (Ordinal Hsvalid)) => //=.
  by rewrite Hrdelta_eq1.
  exists addr.
  exists (Ordinal Hrvalid).
  apply/andP;split => //=.
  by case (r == 0%nat)%bool eqn:H; [right |left; move/neq0_lt0n :H].
  have Hltn_1_eqn0 a b : (a + b < 1)%nat -> (a == 0%nat) && (b == 0%nat). by induction a ; induction b => //=.
  move=>/Hltn_1_eqn0/andP;case => /eqP Hr0 /eqP Hd0.
  destruct r => //=.
  rewrite no_bounded_successful_rounds_eq0. rewrite addn0 => //=.
  suff Hexist: (exists (addr0 : 'I_n_max_actors) (k : 'I_N_rounds),
                   (k <= (Ordinal Hrvalid))%nat && actor_n_has_chain_length_at_round w l addr0 k).
  apply: (chain_growth_weak (x::xs) w l (Ordinal Hrvalid) Hpr_valid Hexist (Ordinal Hsvalid)) => //=.
  by rewrite Hd0 => //=.
  exists addr.
  exists (Ordinal Hrvalid).
  by apply/andP;split .
  by rewrite Hd0; right.


  (* Current progress up to here. *)


  move=>/eqP Hsround o_addr H_is_honest Hwexec//=.
  rewrite -{1}Hsround .
  rewrite subnAC -addnBA => //=. rewrite subnn; rewrite addn0.
  rewrite no_bounded_successful_rounds_eq0. rewrite addn0.
  apply (chain_growth_weak (x::xs) w (c) (Ordinal Hrvalid) H) => //=.
  exists addr. exists (Ordinal Hrvalid) .
  apply /andP.
  split => //=.
  by apply/eqP.
  by case r; [right | move=> n; rewrite (subn1 n.+1) prednK //=; left].
  (* first base case of proof completed *)
  (* dispose of the *fake base case* *)
  induction s => //=.

  (* As in the bitcoin backbone proof, we consider 2 cases - one when Xi' = 0, and one when not *)
  case Hbsuc: (bounded_successful_round w (s - delta));last first.
  move/negP/negP:Hbsuc=>Hbsuc.
  rewrite subSn.
  rewrite -(no_bounded_successful_rounds_ext (x :: xs) w r (s - delta)) => //= Hrsvalid Hwex o_addr H_is_honest.
  move:(@addr_ltn s 1 N_rounds  ).
  rewrite {1}(addn1 s).
  move=> Hweaken.
  move/Hweaken:(Hsvalid)=> Hs'valid.
  apply (actor_has_chain_length_ext w (c + no_bounded_successful_rounds w r (s - delta)) o_addr s Hs'valid Hsvalid) .
  apply IHs => //=.




Admitted.



(* Lemma valid_schedules_can_not_fail_base : forall (x: RndGen), *)
(*     (* [::] is a valid schedule *) *)
(*     (* [::] never produces none *) *)
(*     (* we extend the sequence by a value which keeps it valid *) *)
(*     valid_schedule ([:: x]) -> *)
(*     (* this extended schedule also never produces none *) *)
(*     p_schedule_produces_none ([:: x]) = 0. *)
(* Proof. *)
(*   (* first, let's destructure [&&] into it's principal components *) *)
(*   move => x /andP [ Hr_chck /andP [Hp_chck Hq_chck]]. *)
(*   rewrite /valid_schedule/p_schedule_produces_none/schedule_produces_none. *)
(*   rewrite /evalDist /Dist1.d /Dist1.f /DistBind.f. *)

(*   (* Convert our goal from (\sum x in X, [ f x ]) = 0 to forall x, f x = 0*) *)
(*   apply prsumr_eq0P. *)
(*   move=> o_w Ho_w . *)
(*   (* To do this conversion, we need to quickly prove that our distribution function is strictly positive *) *)
(*   (* we'll do this by showing that each component of the product forming the distribution is positive *) *)
(*   apply Rmult_le_pos => //=. *)
(*   (* first, for (isSome world) - trivial*) *)
(*   case (eq_op o_w _) => //=. *)
(*     exact (Rle_refl (INR 0)). *)
(*   (* now for the evaluation of the world step function *) *)
(*   (* as the result of evalDist is a dist (which contains all proofs we need), we don't care what goes on inside it *) *)
(*   ecase (evalDist (match o_w with *)
(*           | Some _ => _ *)
(*           | None => _ *)
(*         end)). *)
(*   (* now we have a distribution, we need to split it open to view the lemmas it contains *) *)
(*   move=> [f Hf_ge] H //=. *)
(*   move=> w _. *)
(*   (* using the lemmas bundled with a dist, the proof is  trivial. *) *)
(*   destruct w => //; last first. *)
(*     by  rewrite mul0R. *)
(*   rewrite -/evalDist /makeDist //=. *)
(*   (* conversion done *) *)

(*   (* if the world is none, the result is 0, trivially*) *)
(*   case (eq_op _ _) eqn: H; last first => //=. *)
(*     by  rewrite mul0R. *)
(*   rewrite mul1R. *)
(*   (* thus, w must equal initworld - let's just rewrite our expressions to reflect this*) *)
(*   move/eqP: H =>  H. *)
(*   injection H. *)
(*   clear H. *)
(*   move=> ->. *)

(*   move: Hq_chck Hp_chck Hr_chck. *)
(*   (* prove the property for each type of schedule*) *)
(*   case x. *)
(*    (* Honest Transaction Gen *) *)
(*     - move=> [tx addr] Hr_chck Hp_chck Hq_chck //=. *)

(*       rewrite /evalDist /Dist1.d /Dist1.f /DistBind.f //=. *)
(*       rewrite ifT. *)
(*       destruct (tnth _) as [actor is_corrupt] eqn:H . *)
(*       rewrite ifF. *)
(*       (* Having assumed all that, irrespective of whether the transaction is valid, the output is not None *) *)
(*       by  case (Transaction_valid _) eqn: Htx_Variable  => //=. *)

(*       move: H. *)
(*       rewrite local_state_base_nth => H. *)
(*         by  injection H. *)
(*       exact (valid_Honest_max_Transaction_sends_strong). *)

(*     (* Transaction drop *) *)
(*     - move=> [ind Hind] Hr_chck Hp_chck Hq_chck. *)
(*       by  case (fixlist_get_nth _) => //. *)
(*     (* Honest Transaction Gen *) *)
(*     - move=> Hr_chck Hp_chck Hq_chck //. *)

(*       rewrite honest_max_activation_base local_state_base_nth //=. *)
(*       rewrite /evalDist /Dist1.d /Dist1.f /DistBind.f //=. *)
(*       rewrite /evalDist /Dist1.d /Dist1.f /DistBind.f //=. *)
(*       apply prsumr_eq0P. *)
(*       move=> addr Haddr. *)
(*       apply Rmult_le_pos => //=. *)
(*       apply rsumr_ge0. *)
(*       move => summand _. *)
(*       case (eq_op addr summand) => //=; last first. *)
(*         by  rewrite mulR0; exact (Rle_refl (INR 0)). *)
(*       rewrite mulR1 /Uniform.f. *)
(*       apply divR_ge0 => //=. *)
(*       rewrite card_ord. *)
(*       apply lt_0_INR. *)
(*       by  exact (Nat.lt_0_succ _). *)
(*       apply rsumr_ge0. *)
(*       move=> prod _. *)
(*       rewrite -/evalDist /Dist1.d /Dist1.f /DistBind.f //=. *)
(*       apply Rmult_le_pos => //=. *)
(*         case (evalDist _) => f Hpos. *)
(*         by destruct f => //=. *)
(*       apply rsumr_ge0 => o_w' _. *)
(*       case (eq_op None o_w') eqn: H. *)
(*       move/eqP: H=><-//=. *)
(*       rewrite mulR1. *)
(*         by case (evalDist _) => f Hpos; destruct f. *)
(*       rewrite H//mulR0; by exact (Rle_refl (INR 0)). *)
(*       move=> value _. *)
(*       apply /eqP. *)
(*       rewrite mulR_eq0. *)
(*       apply /orP. *)
(*       right. *)
(*       apply/eqP. *)
(*       apply prsumr_eq0P. *)
(*       move=> value_1 _. *)
(*       apply Rmult_le_pos => //=. *)
(*         by case (evalDist _) => f Hpos; destruct f. *)











(*
- - - - - - - - - - - - - - - - - - - - 
          Chain Quality Lemma
- - - - - - - - - - - - - - - - - - - - 
*)

(* The chain quality lemma is defined, given that... *)
Definition chain_quality_givens (schedule : seq.seq RndGen) (l u : nat) (agent : 'I_n_max_actors) :=
    o_w' <-$ world_step initWorld schedule;
    (* the schedule produces a world *)
    (* this first if should always return true if the schedule has been validated *)
    v <- if o_w' is Some(w')  then
        let: (actor, is_corrupt) := (tnth (world_actors w') agent) in
        let: current_chain := honest_current_chain actor in
            (* the selected actor is honest *)
            (~~ is_corrupt) && 
            (* the length of the actor's chain is greater than l *)
            ((fixlist_length current_chain ) > l)%nat
         else false;
    ret v.

Definition p_chain_quality_givens  (schedule : seq.seq RndGen) (l u : nat) (agent : 'I_n_max_actors) :=
    evalDist (chain_quality_givens schedule l u agent) true.




Definition has_chain_quality_property (s: seq.seq RndGen) (l u : nat) (agent : 'I_n_max_actors) :=
    o_current_w <-$ world_step initWorld s;
    result <- if o_current_w is Some(current_w) then 
        (((fixlist_length (honest_current_chain (fst (tnth (world_actors current_w) agent)))) > l)%nat &&
    chain_quality_property current_w l u agent) else false;
    ret result.

Definition p_has_chain_quality_property (s : seq.seq RndGen) (l u : nat) (agent : 'I_n_max_actors) :=
    evalDist (has_chain_quality_property s l u agent) true.



(* Probability that the ratio of blocks of an honest player is bounded by t / n-t, given that 
    the schedule produces a value
    the selected actor is honest
    the selected actors chain is longer than l
*)
Lemma p_chain_quality (l u : nat) : forall  (s: seq.seq RndGen) (agent : 'I_n_max_actors),
   (* Forall *valid* schedules, *)
   (valid_schedule s) -> 
   (* if the schedule is capable of producing worlds satisfying the givens *)
    (p_chain_quality_givens s l u agent > R0) ->
    (* Pr( givens_of result_w AND has_chain_quality_property ) / Pr (givens_of result_w ) = *)
    (* Pr (result_w has chain_quality_property, given the givens) *)

    (p_has_chain_quality_property s l u agent) / (p_chain_quality_givens s l u agent) = probability_constant.
    Admitted.









(*
- - - - - - - - - - - - - - - - - - - - 
          Common Prefix Lemma
- - - - - - - - - - - - - - - - - - - - 
*)

Definition adopted_at_round (c : BlockChain) (r : 'I_N_rounds) (w: World) :=
    (length (filter (fun rec => 
        let: (chain, round, addr) := rec in
        (chain == c) && (round == r))
    (fixlist_unwrap (world_adoption_history w))) > 0)%nat.



Definition common_prefix_givens 
    (* Todo: Add typical execution assumption*)
    (schedule : seq.seq RndGen)  (r : 'I_N_rounds) (c1 c2: BlockChain)  :=
    (* Consider two chains c1 c2 st, len(C2) >= len (C1)*)
    (w' <-$ world_step initWorld schedule;
    r <-
        if w' is Some(current_w) then
        (* if c1 is adopted by an honest party at round r and c2 is adopted or diffused at round r*)
            [&& (adopted_at_round c1 r current_w) & (adopted_at_round c2 r current_w) ]
        else 
            false;
    ret r).

Definition p_common_prefix_givens
    (schedule : seq.seq RndGen)  (r : 'I_N_rounds)  (c1 c2: BlockChain)  :=
    evalDist (common_prefix_givens schedule  r c1 c2 ) true.


Definition has_common_prefix_property
    (* Todo: Add typical execution assumption*)
    (* Todo: Assert that k >= 2 eta k f *)
    (schedule : seq.seq RndGen) (k : nat) (r : 'I_N_rounds) (c1 c2: BlockChain)  :=
    (* Consider two chains c1 c2 st, len(C2) >= len (C1)*)
    (w' <-$ world_step initWorld schedule;
    r <-
        if w' is Some(current_w) then
        (* if c1 is adopted by an honest party at round r and c2 is adopted or diffused at round r*)
            [&& (adopted_at_round c1 r current_w), 
                (adopted_at_round c2 r current_w) ,
               (* then pruning k blocks from the head of c1 will make it a prefix or equal to c2 and visa versa *) 
               prefix (drop k (BlockChain_unwrap c1)) (BlockChain_unwrap c2) &
               prefix (drop k (BlockChain_unwrap c2)) (BlockChain_unwrap c1) ]
        else 
            false;
    ret r).

Definition p_has_common_prefix_property
    (schedule : seq.seq RndGen) (k : nat) (r : 'I_N_rounds)  (c1 c2: BlockChain)  :=
    evalDist (has_common_prefix_property schedule k r c1 c2 ) true.

Lemma common_prefix: forall 
    (s: seq.seq RndGen) (k : nat) (r : 'I_N_rounds) (c1 c2: BlockChain) ,
    (INR k >= (INR 2) * f_probability_honest_success * Eta_block_to_round * (INR Hash_length_k ) + (INR (2 * delta))) ->

   (valid_schedule s) -> 

    ((length c2 >= length c1)%nat ) ->
     (p_common_prefix_givens s r c1 c2 > R0) ->
    (* Pr( givens_of result_w AND has_chain_quality_property ) / Pr (givens_of result_w ) = *)
    (* Pr (result_w has chain_quality_property, given the givens) *)

    (p_has_common_prefix_property s k r c1 c2 ) = (p_common_prefix_givens s r c1 c2 ) * probability_constant.
    Admitted.
    





(*
- - - - - - - - - - - - - - - - - - - - 
          Unique Round Lemma
- - - - - - - - - - - - - - - - - - - - 
*)

 Definition unique_round_givens (schedule : seq.seq RndGen) (n : nat) (chain : BlockChain) :=
    o_w' <-$ world_step initWorld schedule;
    r <- if o_w' is Some(w) then
        (chain \in (fixlist_unwrap (world_chain_history w))) &&
        (fixlist_length chain > n)%nat &&
        (nth_block_is_honest chain n w) &&
        (nth_block_hashed_in_a_uniquely_successful_round w chain n)

    else false;
    ret r.

 Definition p_unique_round_givens (schedule : seq.seq RndGen) (n : nat) (chain : BlockChain) :=
    evalDist (unique_round_givens schedule n chain) true.

Definition is_unique_round (schedule : seq.seq RndGen) (n : nat) (chain : BlockChain) :=
    o_w' <-$ world_step initWorld schedule;
    r <- if o_w' is Some(w) then
        [&& 
        
        (chain \in (fixlist_unwrap (world_chain_history w))),

        (fixlist_length chain > n)%nat,

        (nth_block_is_honest chain n w) &

        (if (nth_block_hashed_in_a_uniquely_successful_round w chain n) is Some(value) then
            (all (fun other_chain => 
                    if other_chain \in (fixlist_unwrap (world_chain_history w)) then
                        if (fixlist_length other_chain > n)%nat then
                            ((nth_block_is_adversarial w other_chain n) ||
                            (nth_block_equals w other_chain n (nth_block w chain n)))
                        else true
                    else true
                ) (fixlist_unwrap (world_chain_history w)))
        else false)]
    else false;
    ret r.

Definition p_is_unique_round (schedule : seq.seq RndGen) (n : nat) (chain : BlockChain) :=
    evalDist (is_unique_round schedule n chain) true.


Lemma unique_round : forall  (s: seq.seq RndGen) (n : nat) (chain : BlockChain),
   (* Forall schedules, *)
   (* if the schedule is capable of producing worlds satisfying the givens *)
   (valid_schedule s) -> 

    (p_unique_round_givens s n chain > R0) ->

    (* Pr( givens_of result_w AND has_chain_quality_property ) / Pr (givens_of result_w ) = *)
    (* Pr (result_w has chain_quality_property, given the givens) *)

    (p_is_unique_round s n chain) / (p_unique_round_givens s n chain) = probability_constant.
    Admitted.


Definition chain_growth_givens (schedule : seq.seq RndGen) (r l : nat)  :=
    o_w' <-$ world_step initWorld schedule;
    r <- if o_w' is some(w) then
        (* suppose that at round r, an honest party has a chain of length r*)
        (has 
            (* there is an actor, with index actor index*)
            (fun actor_ind => 
                (* such that, *)
                [&&
                (* the actor is honest *)
                (actor_n_is_honest w actor_ind) &
                (* and *)
                (has
                    (* there is a record *)
                    (fun pr => 
                        let: (rec_chain, rec_round, rec_actr)  := pr in 
                       [&&
                         (* adopting a chain of length l *)
                        ((fixlist_length rec_chain)  == l),
                         (* at round r *)
                        (nat_of_ord rec_round == r) &
                        (* by the actor *) 
                        (nat_of_ord rec_actr == actor_ind) ]
                    
                    )
                (fixlist_unwrap (world_adoption_history w)))]
            ) 
            (iota 0 n_max_actors))
         else
         false;
    ret r.
Definition p_chain_growth_givens (schedule : seq.seq RndGen) (r l : nat)  :=
    evalDist (chain_growth_givens schedule r l) true.


Definition chain_growth_property (w : World) (r l s : nat) :=
        (* suppose that at round r, an honest party has a chain of length r*)
        [&& 
            (has 
                (* there is an actor, with index actor index*)
                (fun actor_ind => 
                    (* such that, *)
                    [&&
                    (* the actor is honest *)
                    (actor_n_is_honest w actor_ind) &
                    (* and *)
                    (has
                        (* there is a record *)
                        (fun pr => 
                            let: (rec_chain, rec_round, rec_actr)  := pr in 
                        [&&
                            (* adopting a chain of length l *)
                            ((fixlist_length rec_chain)  == l),
                            (* at round r *)
                            (nat_of_ord rec_round == r) &
                            (* by the actor *) 
                            (nat_of_ord rec_actr == actor_ind) ]
                        
                        )
                    (fixlist_unwrap (world_adoption_history w)))]
                ) 
                (iota 0 n_max_actors)) &
                (* then every honest party has adopted a chain of length
                at least l + sum r to s - delta X'i*)
                let sum_of_delta_rounds := no_bounded_successful_rounds w r (s - delta) in
                (* forall actors *)
                    (* for all rounds from s onwards *)
                        (* every chain adoption*)
                  all_chains_after_round_have_length_ge w s (l + sum_of_delta_rounds )
                                ].


Definition has_chain_growth_property (schedule : seq.seq RndGen) (r l : nat) (s : nat) :=
    o_w' <-$ world_step initWorld schedule;
    r <- if o_w' is some(w) then
            chain_growth_property w r l s
         else false;
    ret r.


Definition p_has_chain_growth_property (schedule : seq.seq RndGen) (r l s : nat)  :=
    evalDist (has_chain_growth_property schedule r l s) true.


Lemma chain_growth: forall (schedule : seq.seq RndGen) (r l s : nat),
    (valid_schedule schedule) ->
    (s >= r + delta - 1)%nat ->

    (p_chain_growth_givens schedule r l > R0) ->

    (p_has_chain_growth_property schedule r l s) / (p_chain_growth_givens schedule r l) = probability_constant.
    Admitted.

Definition comp_no_adversarial_blocks (schedule : seq.seq RndGen) (from to : nat) :=
    o_w' <-$ world_step initWorld schedule;
    r <- if o_w' is some(w) then
            no_adversarial_blocks w from to
        else
            (Ordinal valid_N_rounds_mul_n_max_actors);
    ret r.    

Definition expected_no_adversarial_blocks (schedule : seq.seq RndGen) (from to : nat) :=
    expected_value (comp_no_adversarial_blocks schedule from to).

Definition comp_no_successful_rounds (schedule : seq.seq RndGen) (from to : nat) :=
    o_w' <-$ world_step initWorld schedule;
    r <- if o_w' is some(w) then
            no_successful_rounds w from to
        else
            (Ordinal valid_N_rounds);
    ret r.    


Definition expected_no_successful_rounds (schedule : seq.seq RndGen) (from to : nat) :=
    expected_value (comp_no_successful_rounds schedule from to).

Definition comp_no_bounded_successful_rounds (schedule : seq.seq RndGen) (from to : nat) :=
    o_w' <-$ world_step initWorld schedule;
    r <- if o_w' is some(w) then
            no_bounded_successful_rounds w from to
        else
            (Ordinal valid_N_rounds);
    ret r.    

Definition expected_no_bounded_successful_rounds (schedule : seq.seq RndGen) (from to : nat) :=
    expected_value (comp_no_bounded_successful_rounds schedule from to).

Definition comp_no_bounded_uniquely_successful_rounds (schedule : seq.seq RndGen) (from to : nat) :=
    o_w' <-$ world_step initWorld schedule;
    r <- if o_w' is some(w) then
            no_bounded_uniquely_successful_rounds w from to
        else
            (Ordinal valid_N_rounds);
    ret r.    


Definition expected_no_bounded_uniquely_successful_rounds (schedule : seq.seq RndGen) (from to : nat) :=
    expected_value (comp_no_bounded_uniquely_successful_rounds schedule from to).

Definition unwrap_computation (schedule:seq.seq RndGen) : dist [finType of World] :=
    evalDist (
        o_w' <-$ world_step initWorld schedule;
        r <- if o_w' is some(w) then
                w
            else
                (*should never happen*)
                initWorld;
        ret r).


(* Given a world w, produced by a schedule s, asserts that typical_execution holds *)
Definition typical_execution (w : World) (schedule : seq.seq RndGen) (from to : nat) :=
    (* (R1 - eps) * E[ X'(S) ] < X'(S)*)
    (R1 - Epsilon_concentration_of_blocks) * (expected_no_bounded_successful_rounds schedule from to) < INR (nat_of_ord (no_bounded_successful_rounds w from to)) /\
    (* X(S) < (1 + eps)E[ X(S) ],*)
    INR (nat_of_ord (no_successful_rounds w from to)) < (R1 + Epsilon_concentration_of_blocks) * (expected_no_successful_rounds schedule from to) /\
    (* (1 - eps) * E[ Y'(S) ] < Y'(S) *)
    (R1 - Epsilon_concentration_of_blocks) * (expected_no_bounded_uniquely_successful_rounds schedule from to) < INR (nat_of_ord (no_bounded_uniquely_successful_rounds w from to)) /\
    (* Z (S) < (1 + eps) E[ Z(S) ] *)
    INR (nat_of_ord (no_adversarial_blocks w from to)) < (R1 + Epsilon_concentration_of_blocks) * (expected_no_adversarial_blocks schedule from to) /\
    (* no insertion occurred *)
    ~~ (insertion_occurred w from to) /\
    (* no copies occurred *)
    ~~ (copy_occurred w from to) /\
    (* no predictions occurred *)
    ~~ (prediction_occurred w from to).
    
