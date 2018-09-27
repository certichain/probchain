From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat seq ssrfun eqtype bigop fintype choice . 
From mathcomp.ssreflect
Require Import tuple.

Require Import Reals Fourier FunctionalExtensionality. From infotheo
Require Import proba ssrR Reals_ext logb ssr_ext ssralg_ext bigop_ext Rbigop .

Require Import Nsatz.

Require Import Bvector.


From Probchain Require Import
     ValidSchedule Deterministic Comp Notationv1 BlockChain Protocol
     OracleState BlockMap InvMisc Parameters FixedList FixedMap SubSteps.

Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.ProofIrrelevance.
Require Import Coq.Program.Equality.

Set Implicit Arguments.



Definition schedule_produces_none (s: seq.seq RndGen) :=
    o_w' <-$ world_step initWorld s;
    r <- if o_w' is Some(w) then false else true;
    ret r.

Definition p_schedule_produces_none (s:seq.seq RndGen) :=
    evalDist (world_step initWorld s) None.

Definition executed_rounds (s : seq.seq RndGen) :=
  count (fun evnt => match evnt with
                  | RoundEnd => true
                  | _ => false
                  end) s.



Lemma local_state_base_nth addr : tnth initLocalStates addr = (initLocalState, false).
Proof.
  rewrite (tnth_nth (initLocalState, false)).
  rewrite /initLocalStates.
  destruct addr as [m Hm].
  rewrite /tnth/ncons/ssrnat.iter//=. move: m Hm.
  elim n_max_actors => //=.
  move=> n IHn m .
  case m => //=.
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

Lemma prsum_nge0p {A: finType}  f : 
  (forall a : A, 0 <= f a) -> (forall a : A, ~ (f a  > 0)) -> (forall a, f a = 0).
Proof.
  move=> Hdist Hngt a; move/Rnot_gt_le: (Hngt a) (Hdist a).
  by move=>/Rle_antisym H /H.
Qed.


Lemma prsumr_ge0 (A : finType) f : (forall a : A, (0 <= f a)%R) -> \rsum_(a in A) f a <> 0 <-> (exists a,  f a >b 0)%R.
Proof.
  have HforalleqP : (forall x, f x = 0) -> (forall x, (fun _ => true) x -> f x = 0). by [].
  have HforallgtP : (forall x, 0 <= f x) -> (forall x, (fun _ => true) x -> 0 <= f x). by [].
  move=> Hgt0.
  split.
  move=>/eqP/negP Rsumr0.
  case Heq0: (~~ [exists a, f a >b 0]).
  move/negP/negP:Heq0 => Heq0.
  rewrite negb_exists in Heq0.
  have Hforalleq: (forall x, ~~ (f x >b 0)) -> (forall x, ~ (f x > 0)).
    by move=> Hb x; move/negP: (Hb x) => Hbool; move=>/gtRP .
  move/forallP/Hforalleq: Heq0.
  move=>/(prsum_nge0p _ Hgt0)/HforalleqP; move/HforallgtP: Hgt0.
  by move=>/(@prsumr_eq0P  _ _  _ ) H /H /eqP.
  by move/negP/negP/existsP:Heq0.
  move/HforallgtP: Hgt0 => Hgt0.
  move=>[a /gtRP Ha] /(@prsumr_eq0P _ _ _ Hgt0) Heq0.
  by move: (Heq0 a isT) Ha => -> /Rgt_irrefl .
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
 

(*
  consider delta is 4:
  Message queue:
    [ 0 | 1 | 2 | 3 ]

  if an actor first has a chain of length l within round r, it will broadcast the chain at the end of round r (i.e when world_executed_to_round w r) (world_executed_to_round is true given that a given round r has ended).

  Message queue:
    chain
      v
    [ 0 | 1 | 2 | 3 ]
  at each world_executed_to_round w k', where k' >= r, the chain will be at index (k' - r)
  thus at
      world_executed_to_round w (r + delta.-1) (immediately after the round has ended, the last entry of the queue will contain a given chain)
  Message queue:
                chain
                  v
    [ 0 | 1 | 2 | 3 ]

  thus at world_executed_to_round w (r + delta), (immediately after the round has ended, the messages will be removed and delivered)
  Message queue:
                  |-----> chain (has been placed in message queue of all actors
    [ 0 | 1 | 2 | 3 ]
  but we can't say that all actors have the chain until every actor has been activated and had a chance to update their current chain. t
  thus we need to require that
          world_executed_to_round (r + delta).+1
*)

Definition chain_growth_pred w :=
  [forall r : 'I_N_rounds,
      forall l : 'I_Maximum_blockchain_length,
          forall addr: 'I_n_max_actors,
              (* if there is an actor with a chain of length l at round r *)
              actor_n_has_chain_length_at_round w (nat_of_ord l) (nat_of_ord addr) r
              ==>
              (*then*)
              (* forall rounds *)
              (* if the round is after the current round + delta
                  (Note: we've slightly increased the bounds (used to be s >= curr_r + delta -1) on this one, due to the way
                  world step mechanics operate - (in our case, we only see adoptions at
                  the subseqent activation, and so we can't see the exact moment an actor
                  obtains a chain) *)
              [forall s  : 'I_N_rounds, 
                  (nat_of_ord r + delta <= nat_of_ord s)%nat ==>
                  ((nat_of_ord s + 2)%nat < N_rounds)%nat ==>
                        (* and the world executed to the round *)
                          world_executed_to_round w s.+1 ==>
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



(* contains some common simplifications used repeatedly in most proofs *)
Lemma world_step_honest_mint_simplify x w w' :
  x = HonestMintBlock ->
  0 < P[ world_step_internal w' x === Some w] ->

  exists lclstt iscrpt addr result blk_rcd hash_val hash_value os ltp,
   (honest_activation [w'.state] = Some addr) /\
   (tnth [[w'.state].actors] addr = (lclstt, iscrpt)) /\
   (retrieve_head_link (honest_max_valid (update_transaction_pool addr lclstt [w'.tx_pool]) [w'.oracle]) [w'.oracle] = Some hash_val) /\
  (find_maximal_valid_subset
                  (honest_local_transaction_pool (update_transaction_pool addr lclstt [w'.tx_pool]))
                  (honest_max_valid (update_transaction_pool addr lclstt [w'.tx_pool]) [w'.oracle]) =
                (blk_rcd, ltp)) /\
  (0 < P[ hash (hash_value, hash_val, blk_rcd) [w'.oracle] === (os, result)]) /\
  w = honest_step_world w w' lclstt iscrpt addr result blk_rcd hash_val hash_value os.
Proof.

  move=> -> //=.
  rewrite /evalDist //=.
        case Hhon_activation: (honest_activation _ ) => [addr|]; last first.
          by rewrite /evalDist//=; rewrite /Dist1.f //= => /(Rlt_irrefl 0).
        case Htnth: (tnth _ ) => [lclstt iscrpt ].
        move=>/Rlt_not_eq/nesym/prsumr_ge0 => Hexists.
        case: Hexists.
        move=> hv; rewrite /Rgt_lt/Rlt_0_Rmult_inv; apply Rmult_le_pos; case (evalDist _) =>[[f Hpos_f] Hdist] //=.
        rewrite/DistBind.f//=.
        apply rsumr_ge0 => ow' _.
        apply Rmult_le_pos.
        by exact (Hpos_f ow').
        rewrite/DistBind.f//=.
        apply rsumr_ge0 => t_ow' _.
        apply Rmult_le_pos.
          by case (evalDist _) => [[f' Hposf'] Hdist'].
          by exact (Dist1.f0 _ _).

        move=> hash_value /gtRP/Rgt_lt/Rlt_0_Rmult_inv Hsplit.
        case: Hsplit.
          by case (evalDist _) => [[f Hposf] Hdist].
          by case (DistBind.d _) => [[f Hposf] Hdist].
        rewrite /DistBind.d//=/DistBind.f.
        move=>/Rlt_not_eq/nesym/prsumr_ge0 => Hexists.
        case: Hexists => [hash_range | hash_range].
          apply /Rmult_le_pos.
            by case (Uniform.d _) => [[f Hposf] Hdist].
            by case (Dist1.d _) => [[f Hposf] Hdist].
        move=>/gtRP/Rgt_lt/Rlt_0_Rmult_inv Hexists.
        case: Hexists.
            by case (Uniform.d _) => [[f Hposf] Hdist]. 
            by case (Dist1.d _) => [[f Hposf] Hdist]. 
        rewrite /Uniform.d//=/Uniform.f => Hhash_value_valid.
        rewrite /Dist1.f//= => /ltR0n; rewrite lt0b =>/eqP Hhasheq.
        move=>/Rlt_not_eq/nesym/prsumr_ge0 => Hexists.
        case: Hexists.
        move=> o_chain .
          apply /Rmult_le_pos.
          by case (evalDist _); move=> [pos_f Hdist] .
        apply rsumr_ge0 => o_w' _.
        case o_w' => [t_w''|]; last first.
        have: (INR (eq_op (Some w) None) = 0). by [].
        move=> ->; rewrite mulR0; by exact (Rle_refl 0).
        apply Rmult_le_pos.
          by case (evalDist _); move=> [pos_f Hdist] .
          by case (eq_op (Some w) _); [| exact (Rle_refl 0)].
        
        move=> o_w' /gtRP/Rgt_lt/Rlt_0_Rmult_inv Hexists.
        case: Hexists.
          by case (evalDist _); move=> [pos_f Hdist] .
        apply rsumr_ge0 => t_o_w' _.
        apply Rmult_le_pos.
          by case (evalDist _); move=> [pos_f Hdist] .
          by case (eq_op (Some w) _); [| exact (Rle_refl 0)].
         case: o_w'; last first.
         have: \rsum_(a0 in [finType of option World]) P[ ret None === a0] * INR (eq_op (Some w) a0) = 0.
          apply prsumr_eq0P.
          move=> o_w _.
            apply Rmult_le_pos.
              by case (evalDist _); move=> [f Hpos_f]  Hdist => //=.
              by case (eq_op (Some w) _); [| exact (Rle_refl 0)].
          move=> [t_w| _];last first.
          rewrite /evalDist//=/Dist1.f //=.
          have:((INR 1) * (INR 0) = Rmult (INR 1) (INR 0)). by []. move=> ->.
          by rewrite mulR0.
          move => _ ; rewrite /evalDist/Dist1.f/Dist1.d.
          rewrite /makeDist. rewrite /Dist1.f.
          have:(0 * (INR (eq_op (Some w) (Some t_w))) = Rmult 0 (INR (eq_op (Some w) (Some t_w)))). by []. move=> ->.
          by rewrite mul0R.
        by move=> -> _ /Rlt_irrefl .


      move=> t_w''.
      move=>/Rlt_not_eq/nesym.
      rewrite /honest_attempt_hash//=.
      case Hretrieve_head_link: (retrieve_head_link _) => [hash_val|//=];last first.
      case Hmax_subset: (find_maximal_valid_subset _) => [blk_rcd ltp] //=.
      rewrite /DistBind.f.
      move=>/prsumr_ge0 Hexists.
      case: Hexists => [[os result]].
      apply Rmult_le_pos .
        by case (evalDist _); move=> [f Hpos_f]  Hdist => //=.
        by exact (Dist1.f0 _ _).

      move=> [ os result].
      move=>/gtRP/Rgt_lt/Rlt_0_Rmult_inv Hexists.
      case: Hexists.
        by case (evalDist _); move=> [f Hpos_f]  Hdist => //=.
        by exact (Dist1.f0 _ _).
        rewrite -/evalDist.
        move=> Hhash_val.
        rewrite /Dist1.f//=.
        move=> /ltR0n; rewrite lt0b.
        rewrite -/Dist1.f.
        move=>/eqP [].
        clear Hhash_value_valid.
        rewrite -/hash_step.
        rewrite -/(hash_step w w' lclstt addr result blk_rcd hash_val hash_value os).
        move=> Hhash_step.

        rewrite -/honest_attempt_hash.
      move=>/Rlt_not_eq/nesym/prsumr_ge0 Hexists.
      case: Hexists.
      move=> t_o_w'.
      case (eq_op  t_o_w' _); last first.
      by rewrite mul0R; exact (Rle_refl 0).
      case (eq_op _  _); last first.
      by rewrite mulR0; exact (Rle_refl 0).
      by left ; rewrite -mult_INR //=.
      move=> n_w /gtRP/Rgt_lt.
      case Hweq: (eq_op (Some w) n_w); last first.
      by rewrite mulR0 => /(Rlt_irrefl 0).
      destruct n_w ; last first.
      by rewrite mul0R => /(Rlt_irrefl 0).
      move/eqP: Hweq => [] <-.
      clear s.
      rewrite mulR1.
      move=>/ltR0n.
      rewrite lt0b => /eqP [].
      rewrite Hhash_step.
      rewrite -/(honest_step_world w w' lclstt iscrpt addr result blk_rcd hash_val hash_value os).
      move=> Hhonest_step.
      by exists lclstt; exists iscrpt; exists addr; exists result; exists blk_rcd; exists hash_val; exists hash_value; exists os; exists ltp; split.
Qed.


Open Scope seq_scope.
Lemma world_stepP (P : World -> seq.seq RndGen -> Prop) sc w:
  P initWorld [::] ->
  (* transaction gen step *)
  (forall lcl corrupt addr tx w' xs, P w' xs ->
  0 < P[ world_step initWorld xs === Some w'] ->
  tnth (global_local_states (world_global_state w')) addr = (lcl, corrupt) ->
  Transaction_valid tx (BlockChain_unwrap (honest_current_chain lcl)) = true ->
  P (transaction_gen_step w' tx) ((HonestTransactionGen (tx, addr)) :: xs)) ->

  (* transaction gen increment *)
  (forall lcl corrupt addr tx w' xs, P w' xs ->
  0 < P[ world_step initWorld xs === Some w'] ->
  tnth (global_local_states (world_global_state w')) addr = (lcl, corrupt) ->
  Transaction_valid tx (BlockChain_unwrap (honest_current_chain lcl)) = false ->
  P w' ((HonestTransactionGen (tx, addr)) :: xs)) ->



  (* transaction drop step *)
  (forall rem_ind msg w' xs, P w' xs ->
  0 < P[ world_step initWorld xs === Some w'] ->
  fixlist_get_nth (world_transaction_pool w') (nat_of_ord rem_ind) = Some msg ->
  P (transaction_drop_step w' rem_ind) ((TransactionDrop rem_ind)::xs)) ->

  (* transaction drop incr *)
  (forall rem_ind w' xs, P w' xs ->
  0 < P[ world_step initWorld xs === Some w'] ->
  fixlist_get_nth (world_transaction_pool w') (nat_of_ord rem_ind) = None ->
  P w' ((TransactionDrop rem_ind)::xs)) ->


  (* honest mint block step *)
  (forall iscrpt os hash_value hash_vl blc_rcd addr lclstt result ltp  w' xs, P w' xs ->
  0 < P[ world_step initWorld xs === Some w'] ->
  (honest_activation [w'.state] = Some addr) ->
  (tnth [[w'.state].actors] addr = (lclstt, iscrpt)) ->
  (retrieve_head_link
    (honest_max_valid (update_transaction_pool addr lclstt [w'.tx_pool]) [w'.oracle]) [w'.oracle] = Some hash_vl) ->
  (find_maximal_valid_subset
                       (honest_local_transaction_pool (update_transaction_pool addr lclstt [w'.tx_pool]))
                       (honest_max_valid (update_transaction_pool addr lclstt [w'.tx_pool]) [w'.oracle]) =
                       (blc_rcd, ltp)) ->
   (0 < P[ hash (hash_value, hash_vl, blc_rcd) [w'.oracle] === (os, result)]) ->
  P
    (honest_mint_step iscrpt os hash_value hash_vl blc_rcd addr lclstt result w')
    (HonestMintBlock :: xs)) ->

  (* adversary player step *)
  (forall oracle_state old_adv_state blc_rcd nonce hash hash_res w' xs, P w' xs ->
  0 < P[ world_step initWorld xs === Some w'] ->
  adversary_activation (world_global_state w') = true ->
  update_adversary_state w' = (old_adv_state, (nonce, hash, blc_rcd)) ->
  0 < P[
          Deterministic.hash
            (nonce, hash, blc_rcd) (world_hash w') === (oracle_state, hash_res)
        ] ->
  P
    (adversary_mint_player_step oracle_state old_adv_state blc_rcd nonce hash hash_res w')
    (AdvMintBlock :: xs))
  ->

  (* adversary global step *)
  (forall adv_state w' xs, P w' xs ->
  0 < P[ world_step initWorld xs === Some w'] ->
  adversary_activation (world_global_state w') = true ->
  (adversary_last_hashed_round (global_adversary (world_global_state w')) <
  global_current_round (world_global_state w'))%nat = false ->
  (isSome (Addr_to_index (global_currently_active (world_global_state w'))) = true ) ->
  0 < P[
        adversary_attempt_hash
          (update_adversary_transaction_pool (global_adversary (world_global_state w'))
                                             (world_transaction_pool w'))
          (world_inflight_pool w')
          (world_hash w') === adv_state
        ] ->
  P (adversary_mint_global_step adv_state w')
    (AdvMintBlock :: xs))
  ->

  (* adversary corrupt step *)
  (forall addr actr w' xs, P w' xs ->
  0 < P[ world_step initWorld xs === Some w'] ->
  adversary_activation (world_global_state w') = true ->
  tnth (global_local_states (world_global_state w')) addr = (actr, false) ->
  (no_corrupted_players (world_global_state w') < t_max_corrupted)%nat = true ->
  P (adversary_corrupt_step actr addr w')
    ((AdvCorrupt addr) :: xs)) ->

  (* broadcast step *)
  (forall nwadvst chain addrlist w' xs,
  P w' xs ->
  0 < P[ world_step initWorld xs === Some w'] ->
  adversary_activation (world_global_state w') &&
          (world_adversary_message_quota w' < Adversary_max_Message_sends - 1)%nat = true ->
  finfun.FunFinfun.fun_of_fin (adversary_send_chain (global_adversary (world_global_state w')))
           (adversary_state (global_adversary (world_global_state w'))) = (nwadvst, chain) ->
  P (broadcast_step nwadvst chain addrlist w')
    ((AdvBroadcast addrlist) :: xs))  ->

  (* adversary transaction gen *)
  (forall adv_state tx addrlist w' xs, P w' xs ->
   0 < P[ world_step initWorld xs === Some w'] ->
   (world_adversary_transaction_quota w' < Adversary_max_Transaction_sends - 1)%nat = true ->
   finfun.FunFinfun.fun_of_fin (adversary_send_transaction (global_adversary (world_global_state w')))
           (adversary_state (global_adversary (world_global_state w'))) = (adv_state, tx, addrlist) ->
   P
     (adversary_transaction_step adv_state tx addrlist w') (AdvTransactionGen :: xs))  ->


  (* round end step *)
  (forall msgs new_pool w' xs, P w' xs ->
  0 < P[ world_step initWorld xs === Some w'] ->
  (round_ended w') ->
  update_message_pool_queue (world_message_pool w') (world_inflight_pool w') = (msgs, new_pool) ->
  P (round_end_step msgs new_pool w') (RoundEnd :: xs)) ->


  (* adversary end step *)
  (forall w' xs,  
   P w' xs ->
   0 < P[ world_step initWorld xs === Some w'] ->
   adversary_activation (world_global_state w') = true ->
   P (adversary_end_step w') (AdversaryEnd :: xs)) ->

  (P[ world_step initWorld sc === Some w] <> 0) ->
  P w sc.
Proof.
  move=> Hinitial
          Htxgen Htxgenincr
          Htxdrop Htxdropincr
          Hhongen
          Hadvplyr
          Hadvglbl
          Hcrrpt
          Hbrdcst
          Hadvtxgen
          Hrndended
          Hadvend.
  move: w.
  elim :sc => //=.
  move=> w.
  rewrite /Dist1.f.
  case H: (eq_op (Some w) (Some initWorld)) => //= _.
  by move/eqP: H => [] -> //=.

  move=> x xs IHn w.
    move=>/prsumr_ge0 [] o_w.
       by apply Rmult_le_pos; case (evalDist _); move=> [pos_f Hdist].
    move=>/gtRP/Rgt_lt/Rlt_0_Rmult_inv Hexist.
    case: Hexist.
      by case (evalDist _); move=> [pos_f Hdist] .
      by case (evalDist _); move=> [pos_f Hdist] .
    destruct o_w  as [w'|]; last first .
      (* It is an absurdity for the immediately prior world to be none*)
      by rewrite /Dist1.f//= => _ /ltR0n.
    move=> Hpr_w'; move: (Hpr_w').
    move=> /Rlt_not_eq/nesym/IHn Hw'.
    move=> Hpr_wstep; move: (Hpr_wstep).
    case_eq x .
     (* if x is a transaction gen *)
       - move=> //= [tx addr] Heq.
        case (_ < _)%nat => //=; last first.
        by rewrite /Dist1.f//= => /ltR0n.
        destruct (tnth _ addr) as [lcl corrupt] eqn: H; case corrupt => //=.
        by rewrite /Dist1.f//= => /ltR0n.
        case Htxvld: (Transaction_valid _); rewrite /evalDist//= /Dist1.f ltR0n lt0b =>/eqP o_w'; case: o_w' => -> //=.
        rewrite -/(transaction_gen_step w' tx ).
        by apply (Htxgen lcl corrupt addr tx w' xs).
        by apply (Htxgenincr lcl corrupt addr tx w' xs).
    (* if x is a transaction drop *)
       - move=> //= tp_len Heq.
        case Htxmsg: (fixlist_get_nth _) => [txMsg|]; rewrite /evalDist//= /Dist1.f ltR0n lt0b =>/eqP [] -> //=.
        rewrite -/(transaction_drop_step w' tp_len).
        by apply (Htxdrop tp_len txMsg w' xs).
        by apply (Htxdropincr tp_len w' xs).
    (* if x is a honest mint*)
        move=> //= Heqq.
        move=> _.
        move:(@world_step_honest_mint_simplify x w w' Heqq Hpr_wstep) => [lclstt [iscrpt [addr [result [blc_rcd [hash_vl [hash_value [os [ltp]]]]]]]]] => [[Hhon_activation [Htnth [Hretrieve_hlink [Hfind_max_subset [Hpr_hash ->]]]]]].
        rewrite /honest_step_world //=.
        rewrite -/(honest_mint_step iscrpt os hash_value hash_vl blc_rcd addr lclstt result w').
        by apply (Hhongen _) with (ltp0 := ltp).

    (* if x is an adversary mint operation *)
        move=> //= Heqq.
        case Hadv: (adversary_activation _); last first .
          (* obviously invalid for the prior world to be none *)
          by rewrite /evalDist //=; rewrite /Dist1.f //= => /(Rlt_irrefl 0).
        case Hlt: (_ < _)%nat => //=.
        rewrite /DistBind.f//=.
        move=> /Rlt_not_eq/nesym/prsumr_ge0//= Hexists.
        case: Hexists => //= [[[adv os] bl]].
          apply /Rmult_le_pos.
            by case (evalDist _) => [[f hposf] hdist].
            by exact (Dist1.f0 _ _).
          move=>  adv_state /gtRP/Rgt_lt/Rlt_0_Rmult_inv Hexists.
          case: Hexists.
            by case (evalDist _) => [[f hposf] hdist].
            by exact (Dist1.f0 _ _).
          move=> /Rlt_not_eq/nesym .
          rewrite /adversary_attempt_hash//=.
          rewrite -/(update_adversary_state w').
          case Hadv_state :
            (update_adversary_state w') => [old_adv_state [[nonce hash] blc_rcd]] //=.
          rewrite /DistBind.f//= => /prsumr_ge0 Hexists.
          case: Hexists. move => [oracle_state hash_res].
             apply /Rmult_le_pos.
             by case (evalDist _) => [[f hposf] hdist].
             by exact (Dist1.f0 _ _).
          move => [oracle_state hash_res].
          move=>  /gtRP/Rgt_lt/Rlt_0_Rmult_inv Hexists.
          case: Hexists.
             by case (evalDist _) => [[f hposf] hdist].
             by exact (Dist1.f0 _ _).
          move=> Hhash_res.
          rewrite /Dist1.f.
          case Heqn: (eq_op adv_state _) ;last first.
          have: INR false = 0. by []. by move => -> /(Rlt_irrefl 0).
          move=> _.
          move/eqP: Heqn => ->.

          case Heqn: (eq_op (Some w) _); last first.
          have: INR false = 0. by []. by move => -> /(Rlt_irrefl 0).
          move=> _.
          move/eqP: Heqn => [] ->.
          rewrite -/(adversary_mint_player_step oracle_state old_adv_state blc_rcd nonce hash hash_res w').
          by apply (Hadvplyr oracle_state old_adv_state blc_rcd nonce hash hash_res w' xs).

          case Hissome: (isSome _) => //=; last first.
              rewrite /Dist1.f.
              have: (eq_op (Some w) None) = false. by []. by move=> -> => /(Rlt_irrefl 0).

          rewrite/DistBind.f//=.
          move=> /Rlt_not_eq/nesym/prsumr_ge0 Hexists.
          case: Hexists => adv_state.
          apply /Rmult_le_pos.
            by case (evalDist _) => [[f hposf] hdist].
            by exact (Dist1.f0 _ _).
         move=>/gtRP/Rgt_lt/Rlt_0_Rmult_inv Hexists.
         case: Hexists.
            by case (evalDist _) => [[f hposf] hdist].
            by exact (Dist1.f0 _ _).
         move=> Hadv_state.
         rewrite/Dist1.f.
         case Heqn: (eq_op (Some _) (Some _)); last first.
             by move=> /(Rlt_irrefl 0).
         move=> _. move/eqP: Heqn => [] ->.
         rewrite -/(adversary_mint_global_step adv_state w').
         by apply (Hadvglbl adv_state w' xs).

    (* if x is a corruption operation*)
       - move=> //= addr Heqq.
        case Hadv: (adversary_activation _); last first .
          (* obviously invalid for the prior world to be none *)
          by rewrite /evalDist //=; rewrite /Dist1.f //= => /(Rlt_irrefl 0).
          rewrite -/(retrieve_address addr w').
        case Htnth : (tnth _ addr) => [actr iscrpt].
        case Hiscrpt: iscrpt => //=.
          (* obviously invalid for the prior world to be none *)
          by rewrite /evalDist //=; rewrite /Dist1.f //= => /(Rlt_irrefl 0).
        case Hnocorrupt: (no_corrupted_players _ < _)%nat ;last first.
          (* obviously invalid for the prior world to be none *)
          by rewrite /evalDist //=; rewrite /Dist1.f //= => /(Rlt_irrefl 0).
 
        rewrite /evalDist //=; rewrite /Dist1.f => /ltR0n; rewrite lt0b => /eqP [] -> //=.
        rewrite -/(adversary_corrupt_step actr addr w').
        by apply (Hcrrpt addr actr w' xs) => //=; rewrite Htnth Hiscrpt.
     (* if x is a broadcast operation *)
        - move=> //= addrlist Heqq.
        case Hcond: ( _ && _); last first.
          (* obviously invalid for the prior world to be none *)
          by rewrite /evalDist //=; rewrite /Dist1.f //= => /(Rlt_irrefl 0).
        case Hfun :(finfun.FunFinfun.fun_of_fin _) => [nwadvst chain] //=.
        rewrite/Dist1.f => /ltR0n; rewrite lt0b =>/eqP [] -> //=.
        rewrite -/(broadcast_step nwadvst chain addrlist w').
        by apply (Hbrdcst nwadvst chain addrlist w' xs).

     (* if x is a adversary transaction gen *)
        move=> //= Heqq.
        case Hcond: ( _ < _)%nat; last first.
          (* obviously invalid for the prior world to be none *)
          by rewrite /evalDist //=; rewrite /Dist1.f //= => /(Rlt_irrefl 0).
        case Hfun :(finfun.FunFinfun.fun_of_fin _) => [[adv_state tx] addrlist] //=.
        rewrite/Dist1.f => /ltR0n; rewrite lt0b =>/eqP [] -> //=.
        rewrite -/(adversary_transaction_step adv_state tx addrlist w').
        by apply (Hadvtxgen adv_state tx addrlist w' xs).
     (* if x is round ended *)
        move=> Heqq.
        rewrite /world_step_internal.
        case Hrndend: (round_ended w'); last first.
          (* obviously invalid for the prior world to be none *)
          by rewrite /evalDist //=; rewrite /Dist1.f //= => /(Rlt_irrefl 0).
        case Hupd: (update_message_pool_queue _) => [msgs new_pool].
        rewrite /evalDist/Dist1.d //=; rewrite/Dist1.f => /ltR0n; rewrite lt0b =>/eqP [] -> .
        rewrite -/(round_end_step msgs new_pool w').
        by apply (Hrndended msgs new_pool w' xs).
     (* if x is an adversary end gen *)
        move=> //= Heqq.
        case Hadv: (adversary_activation _); last first.
          (* obviously invalid for the prior world to be none *)
          by rewrite /evalDist //=; rewrite /Dist1.f //= => /(Rlt_irrefl 0).
        rewrite/evalDist//=.
        rewrite/Dist1.f => /ltR0n; rewrite lt0b =>/eqP [] -> //=.
        rewrite -/(adversary_end_step w').
        by apply (Hadvend w' xs).
Qed.


Lemma honest_mint_stepP (P : World -> Prop) w iscrpt os hash_value hash_vl blc_rcd addr lclstt result ltp : 

          (honest_activation [w.state] = Some addr) ->
          (tnth [[w.state].actors] addr = (lclstt, iscrpt)) ->
          (retrieve_head_link
             (honest_max_valid
                (update_transaction_pool addr lclstt [w.tx_pool]) [w.oracle]) [w.oracle] = Some hash_vl) ->
          (find_maximal_valid_subset
                              (honest_local_transaction_pool (update_transaction_pool addr lclstt [w.tx_pool]))
                              (honest_max_valid (update_transaction_pool addr lclstt [w.tx_pool]) [w.oracle]) =
                              (blc_rcd, ltp)) ->
          (0 < P[ hash (hash_value, hash_vl, blc_rcd) [w.oracle] === (os, result)]) ->


          (forall iscrpt addr lclstt os blc_rcd result hash_value hash_vl ltp,

              (nat_of_ord [[w.state].#active] = nat_of_ord addr) ->
              (tnth [[w.state].actors] addr = (lclstt, iscrpt)) ->
              (retrieve_head_link (honest_max_valid (update_transaction_pool addr lclstt [w.tx_pool]) [w.oracle])
                                  [w.oracle] = Some hash_vl) ->
              (find_maximal_valid_subset
                          (honest_local_transaction_pool (update_transaction_pool addr lclstt [w.tx_pool]))
                          (honest_max_valid (update_transaction_pool addr lclstt [w.tx_pool]) [w.oracle]) = 
                        (blc_rcd, ltp)) ->
              (0 < P[ hash (hash_value, hash_vl, blc_rcd) [w.oracle] === (os, result)]) ->

              (eq_op
                  (honest_max_valid
                    (update_transaction_pool addr lclstt (world_transaction_pool w)) (world_hash w))
                  (honest_current_chain (update_transaction_pool addr lclstt (world_transaction_pool w)))) ->
              (eq_op
                 (nat_of_ord (global_currently_active (world_global_state w)))
                 n_max_actors.+1) ->
              P (honest_mint_failed_no_update iscrpt addr lclstt os w
                                              (global_currently_active (world_global_state w)) )) ->
          (forall
              iscrpt addr lclstt os blc_rcd result hash_value hash_vl ltp
              (Hlt : ((nat_of_ord (global_currently_active (world_global_state w))).+1 < n_max_actors + 2)%nat),

              nat_of_ord [[w.state].#active] = nat_of_ord addr ->
              tnth [[w.state].actors] addr = (lclstt, iscrpt) ->
              retrieve_head_link
                (honest_max_valid
                   (update_transaction_pool addr lclstt [w.tx_pool]) [w.oracle]) [w.oracle] = Some hash_vl ->
              find_maximal_valid_subset
                (honest_local_transaction_pool
                   (update_transaction_pool addr lclstt [w.tx_pool]))
                (honest_max_valid
                   (update_transaction_pool addr lclstt [w.tx_pool]) [w.oracle]) = (blc_rcd, ltp) ->
              0 < P[ hash (hash_value, hash_vl, blc_rcd) [w.oracle] === (os, result)] ->
              (eq_op
                 (honest_max_valid (update_transaction_pool addr lclstt (world_transaction_pool w)) (world_hash w))
                  (honest_current_chain (update_transaction_pool addr lclstt (world_transaction_pool w)))) ->
              P
              (honest_mint_failed_no_update iscrpt addr lclstt os w
        (Ordinal (n:=n_max_actors + 2) (m:=(global_currently_active (world_global_state w)).+1) Hlt))) ->

          (forall iscrpt  addr  lclstt  os blc_rcd result hash_value hash_vl ltp,
              nat_of_ord [[w.state].#active] = nat_of_ord addr ->
              tnth [[w.state].actors] addr = (lclstt, iscrpt) ->
              retrieve_head_link
                (honest_max_valid
                   (update_transaction_pool addr lclstt [w.tx_pool]) [w.oracle]) [w.oracle] = Some hash_vl ->
              find_maximal_valid_subset
                (honest_local_transaction_pool
                   (update_transaction_pool addr lclstt [w.tx_pool]))
                (honest_max_valid
                   (update_transaction_pool addr lclstt [w.tx_pool]) [w.oracle]) = (blc_rcd, ltp) ->
              0 < P[ hash (hash_value, hash_vl, blc_rcd) [w.oracle] === (os, result)] ->

              (eq_op
                 (honest_max_valid (update_transaction_pool addr lclstt (world_transaction_pool w)) (world_hash w))
                 (honest_current_chain (update_transaction_pool addr lclstt (world_transaction_pool w)))) = false ->
              (eq_op (nat_of_ord (global_currently_active (world_global_state w))) n_max_actors.+1) ->
              P
                (honest_mint_failed_update
                   iscrpt addr lclstt os w
                   (global_currently_active (world_global_state w)))) ->

          (forall iscrpt addr lclstt os blc_rcd result hash_value hash_vl ltp
              (Hlt : ((nat_of_ord (global_currently_active (world_global_state w))).+1 < n_max_actors + 2)%nat),
              nat_of_ord [[w.state].#active] = nat_of_ord addr ->
              tnth [[w.state].actors] addr = (lclstt, iscrpt) ->
              retrieve_head_link
                (honest_max_valid
                   (update_transaction_pool addr lclstt [w.tx_pool]) [w.oracle]) [w.oracle] = Some hash_vl ->
              find_maximal_valid_subset
                (honest_local_transaction_pool
                   (update_transaction_pool addr lclstt [w.tx_pool]))
                (honest_max_valid
                   (update_transaction_pool addr lclstt [w.tx_pool]) [w.oracle]) = (blc_rcd, ltp) ->
              0 < P[ hash (hash_value, hash_vl, blc_rcd) [w.oracle] === (os, result)] ->
              (eq_op
                 (honest_max_valid (update_transaction_pool addr lclstt (world_transaction_pool w)) (world_hash w))
                 (honest_current_chain (update_transaction_pool addr lclstt (world_transaction_pool w)))) = false ->
              P
                (honest_mint_failed_update iscrpt addr lclstt os w
                  (Ordinal (n:=n_max_actors + 2) (m:=(global_currently_active (world_global_state w)).+1) Hlt))) ->


          (forall iscrpt  addr  lclstt  os hash_value  hash_vl  blc_rcd  result ltp,
            nat_of_ord [[w.state].#active] = nat_of_ord addr ->
            tnth [[w.state].actors] addr = (lclstt, iscrpt) ->
            retrieve_head_link
              (honest_max_valid
                 (update_transaction_pool addr lclstt [w.tx_pool]) [w.oracle]) [w.oracle] = Some hash_vl ->
            find_maximal_valid_subset
              (honest_local_transaction_pool
                 (update_transaction_pool addr lclstt [w.tx_pool]))
              (honest_max_valid (update_transaction_pool addr lclstt [w.tx_pool]) [w.oracle]) = (blc_rcd, ltp) ->
            0 < P[ hash (hash_value, hash_vl, blc_rcd) [w.oracle] === (os, result)] ->
            (result < T_Hashing_Difficulty)%nat = true ->
            (eq_op (nat_of_ord (global_currently_active (world_global_state w))) n_max_actors.+1) = true ->
            P
              (honest_mint_succeed_update iscrpt addr lclstt os blc_rcd hash_vl hash_value
              (global_currently_active (world_global_state w)) w)) ->

          (forall iscrpt addr  lclstt  os hash_value  hash_vl  blc_rcd  result ltp
             (Hlt : ((nat_of_ord (global_currently_active (world_global_state w))).+1 < n_max_actors + 2)%nat),
          nat_of_ord [[w.state].#active] = nat_of_ord addr ->
          tnth [[w.state].actors] addr = (lclstt, iscrpt) ->
          retrieve_head_link
            (honest_max_valid
               (update_transaction_pool addr lclstt [w.tx_pool]) [w.oracle]) [w.oracle] = Some hash_vl ->
          find_maximal_valid_subset
            (honest_local_transaction_pool
               (update_transaction_pool addr lclstt [w.tx_pool]))
            (honest_max_valid
               (update_transaction_pool addr lclstt [w.tx_pool]) [w.oracle]) = (blc_rcd, ltp) ->
          0 < P[ hash (hash_value, hash_vl, blc_rcd) [w.oracle] === (os, result)] ->

              (result < T_Hashing_Difficulty)%nat ->
              (eq_op (nat_of_ord (global_currently_active (world_global_state w))) n_max_actors.+1) = false ->
            P
              (honest_mint_succeed_update iscrpt addr lclstt os blc_rcd hash_vl hash_value
              (Ordinal (n:=n_max_actors + 2) (m:=(global_currently_active (world_global_state w)).+1) Hlt) w)) ->

          P (honest_mint_step iscrpt os hash_value  hash_vl blc_rcd addr lclstt result w).
                              (*hash_value*)(*hash_vl*)

Proof.
  move=> Hhon; move: (Hhon) => /honest_activation_simplify Hactive Htnth Hhlnk Hmxsubs Hprhash.
  move=> H_fail_no_update_last H_fail_no_update H_fail_update_last
                              H_fail_update Hsuccess_update_last Hsuccess_update.

  rewrite /honest_mint_step.
  case Hltn: (_ < _ )%nat; last first.
  case Hmxvld: (eq_op _). move: (elimTF _ ).
  move: (introN _ ).
  move: (erefl _).
  move: (round_in_range _).
  case Heqlstact: (eq_op (nat_of_ord (global_currently_active (world_global_state w))) n_max_actors.+1) =>   //=.
  move=> _ _ _ _.
  rewrite -/(honest_mint_failed_no_update iscrpt addr lclstt os w _).
    by apply H_fail_no_update_last with
       (result := result) (blc_rcd := blc_rcd) (ltp := ltp)
                          (hash_value:=hash_value) (hash_vl:=hash_vl) => //=.

  move=> Hror.
  move: (Hror isT) => Hlt.
  rewrite /ssr_suff => e introN elimTF .
  rewrite (proof_irrelevance _ ((Hror (introN (elimTF e)))) Hlt).

  rewrite -/(honest_mint_failed_no_update
               iscrpt
               addr
               lclstt
               os
               w
               _).

  clear Hhon.
  clear Hltn.
  by apply H_fail_no_update  with
       (result := result) (blc_rcd := blc_rcd) (ltp := ltp)
                          (hash_value:=hash_value) (hash_vl:=hash_vl) => //=.

  move: (elimTF _ ).
  move: (introN _ ).
  move: (erefl _).
  move: (round_in_range _).
  case Heqlstact: (eq_op (nat_of_ord (global_currently_active (world_global_state w))) n_max_actors.+1) =>   //=.
  rewrite -/(honest_mint_failed_update iscrpt addr lclstt os w _) => _ _ _ _.
  clear Hhon.
  clear Hltn.
  by apply H_fail_update_last with
       (result := result) (blc_rcd := blc_rcd) (ltp := ltp)
                          (hash_value:=hash_value) (hash_vl:=hash_vl) => //=.

  move=> Hror.
  move: (Hror isT) => Hlt.
  rewrite /ssr_suff => e introN elimTF .
  rewrite (proof_irrelevance _ ((Hror (introN (elimTF e)))) Hlt).

  rewrite -/(honest_mint_failed_update
               iscrpt
               addr
               lclstt
               os
               w
               _).

  clear Hhon.
  clear Hltn.

  by apply H_fail_update with
       (result := result) (blc_rcd := blc_rcd) (ltp := ltp)
                          (hash_value:=hash_value) (hash_vl:=hash_vl) => //=.
  move: (elimTF _ ).
  move: (introN _ ).
  move: (erefl _).
  move: (round_in_range _).
  case Heqlstact: (eq_op (nat_of_ord (global_currently_active (world_global_state w))) n_max_actors.+1) =>   //=.
  move=> _ _ _ _.
  rewrite -/(honest_mint_succeed_update iscrpt addr lclstt os  _ _ _ _ _).

  move: Hltn Heqlstact.
  clear Hhon.
  by apply Hsuccess_update_last with
       (result := result) (blc_rcd := blc_rcd) (ltp := ltp)
                          (hash_value:=hash_value) (hash_vl:=hash_vl) => //=.
  move=> Hror.
  move: (Hror isT) => Hlt.
  rewrite /ssr_suff => e introN elimTF .
  rewrite (proof_irrelevance _ ((Hror (introN (elimTF e)))) Hlt).
  rewrite -/(honest_mint_succeed_update iscrpt addr lclstt os  _ _ _ _ _).

  move: Hltn Heqlstact.
  clear Hhon.
  by apply Hsuccess_update with
       (result := result) (blc_rcd := blc_rcd) (ltp := ltp)
                          (hash_value:=hash_value) (hash_vl:=hash_vl)  => //=.
Qed.





Lemma world_step_adoption_history_top_heavy sc w :
  (P[ world_step initWorld sc === Some w] <> 0) ->
    fixlist_is_top_heavy (world_adoption_history w).
Proof.
  move=> Hb.
  apply /(world_stepP (fun w _ => fixlist_is_top_heavy (world_adoption_history w)) sc w) => //=.
  - (* base case *)
    by exact (fixlist_empty_is_top_heavy _ _).
  - (* honest mint case *)
    move=> iscrpt os hash_value hash_link blc_rcd addr lclstt result ltp w' xs Hth_base Hpr.
    move=> Hhon Htnth Hretr Hfind Hhash_pr.
    rewrite /honest_mint_step//=.
    case: (result < _)%nat => //=.
    case (global_currently_active ) as [tm Htmvld] eqn: Hteq => //= .
    case:(fixlist_enqueue _) => chain block //=.
    by apply fixlist_insert_preserves_top_heavy.
    case (honest_max_valid _) => //= blck Hblk.
    by case (eq_op _ (honest_current_chain (update_transaction_pool addr lclstt _))) ;
    apply fixlist_insert_preserves_top_heavy.
  - (* adversary mint - player case *)
    move=> os old_adv_state blc_rcd nonce hash hash_res w' xs Hth_base Hpr Hadv Hupd Hpract.
    rewrite /adversary_mint_player_step//=.
    by case (_ < _)%nat => //=.

  - (* adversary mint - global case *)
    move=> [[adv_state] os] blk w' xs Hth_base Hpr Hadv Hcond Haddr Hpract.
    by rewrite/adversary_mint_global_step//=.
Qed. 


Lemma world_step_global_current_round sc w : 
  (P[ world_step initWorld sc === Some w] <> 0) ->
    (nat_of_ord (global_current_round (world_global_state w)) = (count (fun x => if x is RoundEnd then true else false ) sc))%nat.
Proof.
  move=> Hb.
  apply /(world_stepP
            (fun w xs =>
               nat_of_ord (global_current_round (world_global_state w)) =
               (count (fun x => if x is RoundEnd then true else false ) xs)) sc w) => //=.
  - (* if x is a honest mint*)
    move=> iscrpt os hash_value hash_link blc_rcd addr lclstt result ltp w' xs Hth_base Hpr.
    move=> Hhon Htnth Hretr Hfind Hhash_pr.
    rewrite /honest_mint_step//=.
    case: (result < _)%nat => //=.

        case:(fixlist_enqueue _) => chain block //=.

        move: Hth_base.
        move: ((global_currently_active (world_global_state w'))) => tm.
        (* move:(erefl (eq_op (nat_of_ord (global_currently_active (world_global_state w'))) n_max_actors.+1)). *)
        move:(erefl (eq_op (nat_of_ord (global_currently_active (world_global_state w'))) n_max_actors.+1)).
        by move: (elimTF eqP); move: (introN eqP); move: (round_in_range _);
           move: ((@eq_op nat_eqType tm (S n_max_actors))); case.

        by move: (introN eqP); move: (elimTF eqP);move: (round_in_range _);
          case: (eq_op _ _); 
          case (eq_op _ _ ) => //=.


    (* if x is an adversary mint player operation *)
      move=> os old_adv_state blc_rcd nonce hash hash_res w' xs Hth_base Hpr Hadv Hupd Hpract.
      by rewrite /adversary_mint_player_step //=; case (_ < _)%nat.
         
    (* if x is a adversary mint global operation*)
      move=> [[adv_state] os] blk w' xs Heq Hpr Hadvact Hhashed Hind Hpract.
      by rewrite /adversary_mint_global_step.
    (* if x is a world end step *) 
      move=> msgs new_pool w' xs Hth_base Hpract.
      rewrite /next_round//=.
      move=> Heq.
      admit.
      (* todo - solve this *)
      
    (* if x is a adversary end step *)
      move=> w' xs Heq Hpract.
      rewrite /update_round//=.
      move: Heq.
      destruct w' => //=.
      destruct world_global_state => //=.
      by move: (erefl (eq_op (nat_of_ord global_currently_active) n_max_actors.+1));
      move: (introN _); move: (elimTF _); move: (round_in_range _); case (eq_op _  _).
Admitted.










Lemma world_step_round_count sc w : 
  (P[ world_step initWorld sc === Some w] <> 0) ->
    (world_executed_to_max_round w <= (count (fun x => if x is RoundEnd then true else false ) sc))%nat.
Proof.
  move=> Hb.
  apply /(world_stepP
            (fun w xs =>
               (world_executed_to_max_round w <=
                (count (fun x => if x is RoundEnd then true else false ) xs))%nat) sc w) => //=.



  (* base case *)
  by move: (fixlist_empty_is_empty [eqType of BlockChain * 'I_N_rounds * 'I_n_max_actors] (n_max_actors * N_rounds));
  rewrite /world_executed_to_max_round //=/initWorld/initWorldAdoptionHistory;
  rewrite /fixlist_is_empty => /eqP -> //=.

  (* if x is a honest mint*)
    admit.
  (* if x is an adversary mint player operation *)
    move=> os old_adv_state blc_rcd nonce hash hash_res w' xs Hth_base Hpr Hadv Hupd Hpract.
    by rewrite /adversary_mint_player_step //=; case (_ < _)%nat.

  (* if x is a adversary mint global operation*)
    move=> [[adv_state] os] blk w' xs Heq Hpr Hadvact Hhashed Hind Hpract.
    by rewrite /adversary_mint_global_step.
  (* if x is a world end step *) 
    move=> msgs new_pool w' xs Hth_base Hpract Hrndend Hupd.
    move: Hth_base.
    rewrite /round_end_step//=.
    rewrite /world_executed_to_max_round//=.
    rewrite -/world_executed_to_max_round//=.
    rewrite leq_eqVlt => /orP [/eqP ->|] //=.
    move=>/(ltn_addl 1) => Hlt1.
    by rewrite leq_eqVlt; apply/orP; right.
Admitted.



 
  

Lemma world_step_adoption_history_overflow_safe sc w :
  (P[ world_step initWorld sc === Some w] <> 0) ->
    (fixlist_length (world_adoption_history w) < (n_max_actors * N_rounds)%nat)%nat.
Proof.
  move=> Hb.
  apply /(world_stepP
            (fun w' _ =>
              (fixlist_length (world_adoption_history w') < (n_max_actors * N_rounds)%nat)%nat
            ) sc w) => //=.


  (* base case *)
   rewrite /initWorldAdoptionHistory /fixlist_length.
    move:
      (@fixlist_empty_is_empty
         [eqType of BlockChain * 'I_N_rounds * 'I_n_max_actors]
         (n_max_actors * N_rounds)).
    rewrite /fixlist_is_empty =>/eqP ->; rewrite muln_gt0.
    by apply/andP; split; [exact valid_n_max_actors | exact valid_N_rounds].
    
   (* if x is a honest mint*)
    admit.
    (* TODO(Kiran): solve these *)
   (* if x is an adversary mint player operation *)
    move=> os old_adv_state blc_rcd nonce hash hash_res w' xs Hth_base Hpr Hadv Hupd Hpract.
    by rewrite /adversary_mint_player_step //=; case (hash_res < _)%nat => //= .
   (* if x is a adversary mint global operation*)
    move=> [[adv_state] os] blk w' xs Heq Hpr Hadvact Hhashed Hind Hpract.
    by rewrite /adversary_mint_global_step.

Admitted.






Lemma world_executed_to_weaken sc w s Hs'valid Hsvalid:
  (P[ world_step initWorld sc === Some w] <> 0) ->
  world_executed_to_round w (Ordinal (n:=N_rounds) (m:=s.+1) Hsvalid) ->
  world_executed_to_round w (Ordinal (n:=N_rounds) (m:=s) Hs'valid).
Proof.

  move=> Hb.
  by rewrite /world_executed_to_round //=; rewrite -addn1 => /ltn_weaken.
Qed.


(* if an actor has a chain of length at least l at round l,
  then they will also have a chain of length l for all subsequent rounds *)
Lemma  actor_has_chain_length_ext' sc w l o_addr s' s :
  (nat_of_ord s' < nat_of_ord s)%nat ->
  (P[ world_step initWorld sc === Some w] <> 0) ->
  actor_n_has_chain_length_ge_at_round w l o_addr s' ->
  actor_n_has_chain_length_ge_at_round w l o_addr s.
Proof.
  move=> Hpflt.

  move=> Hb.
  apply /(world_stepP
            (fun w _ =>
               (actor_n_has_chain_length_ge_at_round w l o_addr s' ->
  actor_n_has_chain_length_ge_at_round w l o_addr s)
            ) sc w) => //=.
  
  (* base case *)
    rewrite/actor_n_has_chain_length_ge_at_round /initWorldAdoptionHistory.
    move:(fixlist_empty_is_empty [eqType of BlockChain * 'I_N_rounds * 'I_n_max_actors] (n_max_actors * N_rounds)).
    by rewrite /fixlist_is_empty => /eqP -> //=.

  (* honest mint case *)
    move=> iscrpt os hash_value hash_link blc_rcd addr lclstt result ltp w' xs Hth_base Hpr.
    move=> Hhon Htnth Hretr Hfind Hhash_pr.
    rewrite /honest_mint_step.
    move/Rlt_not_eq/nesym: Hpr => Hpr_wbase.
    case (_ < _)%nat => //=.
    case (fixlist_enqueue _) => ls blck .
    move: Hth_base.
    rewrite /actor_n_has_chain_length_ge_at_round//=.
    move=> Hth_base.
    rewrite {1}fixlist_insert_rewrite => //=.
    rewrite has_rcons =>/orP ; case; last first.
    rewrite {1}fixlist_insert_rewrite => //= .
    by move=> Heq; apply/orP; right.
    by exact (world_step_adoption_history_top_heavy xs w' Hpr_wbase).
    by exact (world_step_adoption_history_overflow_safe xs w' Hpr_wbase).
    move=>/orP []; last first.
    move=>/(@or_introl _ (is_true (eq_op l 0%nat)%nat))/orP/Hth_base/orP [ Hb' | Heq0] ; last first.
    by apply/orP; right.
    apply/orP; left.
    (* move=> /Hth_base  Hb'. *)
    rewrite {1}fixlist_insert_rewrite => //=.
    by rewrite has_rcons; apply /orP; right.
    by exact (world_step_adoption_history_top_heavy xs w' Hpr_wbase).
    by exact (world_step_adoption_history_overflow_safe xs w' Hpr_wbase).
    (* by exact (world_step_adoption_history_top_heavy xs w' Hpr_wbase). *)
    (* by exact (world_step_adoption_history_overflow_safe xs w' Hpr_wbase). *)
    (* TODO (Kiran): Refactor this into a neater form *)
    move=>/andP[Hltls /andP [H_gcrlts /eqP Heqadr]].
    rewrite {1}fixlist_insert_rewrite => //=.
    rewrite has_rcons; apply/orP; left; apply/orP; left.
    apply/andP;split => //=. apply/andP; split => //=.
    apply (@leq_trans s') => //=.
    by apply ltnW => //=.
    by rewrite Heqadr.
    by exact (world_step_adoption_history_top_heavy xs w' Hpr_wbase).
    by exact (world_step_adoption_history_overflow_safe xs w' Hpr_wbase).
    by exact (world_step_adoption_history_top_heavy xs w' Hpr_wbase).
    by exact (world_step_adoption_history_overflow_safe xs w' Hpr_wbase).
    move: Hth_base.
    rewrite /actor_n_has_chain_length_ge_at_round//=.
    move=> Hth_base.
    case (eq_op _ _) => //=.
    move=>/orP [ | Heq0]; last first. by apply/orP; right.
    rewrite {1}fixlist_insert_rewrite => //=.
    rewrite has_rcons =>/orP ; case; last first.
    rewrite {1}fixlist_insert_rewrite => //=.
    move=> /(@or_introl _ (is_true (eq_op l 0)%nat))/orP/Hth_base/orP [ Hb' | Heq0]; last first. by apply/orP; right.
    apply/orP; left.
    by rewrite has_rcons; apply /orP; right.
    by exact (world_step_adoption_history_top_heavy xs w' Hpr_wbase).
    by exact (world_step_adoption_history_overflow_safe xs w' Hpr_wbase).


    move=>/andP[Hltls /andP [H_gcrlts /eqP Heqadr]].
    rewrite {1}fixlist_insert_rewrite => //=.
    rewrite has_rcons; apply/orP; left; apply/orP; left.
    apply/andP;split => //=. apply/andP; split => //=.
    apply (@leq_trans s') => //=.
    by apply ltnW => //=.
    by rewrite Heqadr.
    by exact (world_step_adoption_history_top_heavy xs w' Hpr_wbase).
    by exact (world_step_adoption_history_overflow_safe xs w' Hpr_wbase).
    by exact (world_step_adoption_history_top_heavy xs w' Hpr_wbase).
    by exact (world_step_adoption_history_overflow_safe xs w' Hpr_wbase).

    move=> /orP [ | Heq0]; last first. by apply/orP; right.
    rewrite {1}fixlist_insert_rewrite => //=.
    rewrite has_rcons =>/orP ; case; last first.
    rewrite {1}fixlist_insert_rewrite => //=.
    move=> /(@or_introl _ (is_true (eq_op l 0)%nat))/orP/Hth_base/orP [Hb' | Heq0]; last first. by apply/orP; right.
    by rewrite has_rcons; apply /orP; left; apply/orP; right.
    by exact (world_step_adoption_history_top_heavy xs w' Hpr_wbase).
    by exact (world_step_adoption_history_overflow_safe xs w' Hpr_wbase).
    move=>/andP[Hltls /andP [H_gcrlts /eqP Heqadr]].
    rewrite {1}fixlist_insert_rewrite => //=.
    rewrite has_rcons; apply/orP; left; apply/orP; left.
    apply/andP;split => //=. apply/andP; split => //=.
    apply (@leq_trans s') => //=.
    by apply ltnW => //=.
    by rewrite Heqadr.
    by exact (world_step_adoption_history_top_heavy xs w' Hpr_wbase).
    by exact (world_step_adoption_history_overflow_safe xs w' Hpr_wbase).
    by exact (world_step_adoption_history_top_heavy xs w' Hpr_wbase).
    by exact (world_step_adoption_history_overflow_safe xs w' Hpr_wbase).
  (* if x is an adversary mint operation *)
    move=> os old_adv_state blc_rcd nonce hash hash_res w' xs Hth_base Hpr Hadv Hupd Hpract.
    by rewrite /adversary_mint_player_step //=; case (hash_res < _)%nat => //= .
  (* if x is a adversary mint global operation*)
    move=> [[adv_state] os] blk w' xs Heq Hpr Hadvact Hhashed Hind Hpract.
    by rewrite /adversary_mint_global_step.
Qed.

Lemma  actor_has_chain_length_ext sc w l o_addr s' s :
  (nat_of_ord s' <= nat_of_ord s)%nat ->
  (P[ world_step initWorld sc === Some w] <> 0) ->
  actor_n_has_chain_length_ge_at_round w l o_addr s' ->
  actor_n_has_chain_length_ge_at_round w l o_addr s.
Proof.
  move: s' s => [s' Hs'vld] [s Hsvld].
  rewrite leq_eqVlt => /orP [/eqP //= Hs'eq | Hlt ] Hpr.
    by move: Hs'vld; rewrite Hs'eq => Hs'vld ; rewrite (proof_irrelevance _ Hs'vld Hsvld).
  by move=> Hvld; apply:(actor_has_chain_length_ext' sc  w l o_addr (Ordinal Hs'vld)) => //=.
Qed.

Lemma deliver_messages_preserves_honest w a msgs : forall prf,
  ~~
  (let
   '(_, is_corrupted) :=
    tnth (global_local_states (deliver_messages msgs (next_round (world_global_state w))))
      (Ordinal (n:=n_max_actors) (m:=a) prf) in is_corrupted) ->
  ~~
  (let
   '(_, is_corrupted) :=
    tnth (global_local_states (world_global_state w))
      (Ordinal (n:=n_max_actors) (m:=a) prf) in is_corrupted).
Proof.
  (* TODO (Kiran): Prove this *)

Admitted.


Lemma update_round_preserves_honest w a : forall prf,
  ~~
  (let
   '(_, is_corrupted) :=
    tnth (global_local_states (update_round (world_global_state w)))
      (Ordinal (n:=n_max_actors) (m:=a) prf) in is_corrupted) ->
  ~~
  (let
   '(_, is_corrupted) :=
    tnth (global_local_states (world_global_state w))
      (Ordinal (n:=n_max_actors) (m:=a) prf) in is_corrupted).
Proof.
  (* TODO (Kiran): Prove this *)
Admitted.


Lemma deliver_messages_update_round_preserves_round gs msgs :
[deliver_messages msgs gs.#round] = [gs.#round].
Proof.
Admitted.



Lemma bounded_success_impl_exec sc w s :
  (P[ world_step initWorld sc === Some w] <> 0) ->
  bounded_successful_round w s -> 
  world_executed_to_round w s.
Proof.
Admitted.
Print world_executed_to_round.

Lemma actor_n_has_chain_refl sc w o_addr :
  (P[ world_step initWorld sc === Some w] <> 0) ->
  actor_n_has_chain_length_ge_at_round w (actor_n_chain_length w o_addr) o_addr [[w.state].#round] .
Proof.
Admitted.







Lemma no_bounded_successful_rounds_lt w' r s s' : 
  (s <= s')%nat ->
(no_bounded_successful_rounds w' r s <= no_bounded_successful_rounds w' r s' )%nat.
  Proof.
    (* TODO: Solve this *)
Admitted.

Lemma update_round_preserves_current_chain o_addr stt tpool: 
    honest_current_chain (update_transaction_pool o_addr stt tpool) = honest_current_chain stt.
Proof.
Admitted.

(* when the round is current, the expressions can be rewritten in terms of the world *)
Lemma actor_n_has_chain_at_round_current w sc o_addr l :
    P[ world_step initWorld sc === Some w] <> 0 ->
    (l <= actor_n_chain_length w o_addr)%nat ->
    actor_n_has_chain_length_ge_at_round w l o_addr [[w.state].#round].
Proof.
  (* TODO: Solve this *)
  move=> Hpr.

  apply/(world_stepP (fun w _ =>
                        (l <= actor_n_chain_length w o_addr)%nat ->
                        actor_n_has_chain_length_ge_at_round w l o_addr [[w.state].#round]

                     ) sc w ) => //= [ |
                          iscrpt  os  hash_value active_hash_link blc_rcd active_addr  active_state result
                          active_transaction_pool w'  xs  |
                          oracle_state  old_adv_state  blc_rcd nonce hash hash_res  w'  xs |
                          adv_state  w' xs |
                          addr0  actr  w'  xs |
                          msgs new_pool w' xs |
                          w'  xs ] .
  (* base case *)
  rewrite/actor_n_chain_length //= local_state_base_nth //= /initBlockChain -fixlist_length_unwrap_ident.
  move/eqP: (fixlist_empty_is_empty [eqType of Block] Maximum_blockchain_length)=> -> //=.
  by rewrite leqn0 => /eqP ->; rewrite /actor_n_has_chain_length_ge_at_round; apply/orP; right.
  (* honest mint case *)
    move: o_addr => [o_addr Ho_addr].
    move=> Hbase Hth_pr Hhonest_activation Hactive_state Ha_head_link Ha_txpool Hhash_pr .

    move/Rlt_not_eq/nesym: Hth_pr => Hth_base.
    move: (world_step_adoption_history_top_heavy xs w' Hth_base) => Hfith.
    move:(world_step_adoption_history_overflow_safe xs w' Hth_base) => Hos.
    apply /(@honest_mint_stepP (fun w =>
        (l <=
          actor_n_chain_length w (Ordinal (n:=n_max_actors) (m:=o_addr) Ho_addr))%nat ->
          actor_n_has_chain_length_ge_at_round w l (Ordinal (n:=n_max_actors) (m:=o_addr) Ho_addr)
            [[w.state].#round] 
          ) w' iscrpt os hash_value active_hash_link
                               blc_rcd active_addr active_state
                               result active_transaction_pool) => //=;

    clear  Hhonest_activation Hactive_state Ha_head_link Ha_txpool iscrpt ;
    clear result os hash_value active_hash_link blc_rcd active_addr active_state Hhash_pr active_transaction_pool;
    move=> a_crpt a_addr  a_stt new_os a_block a_result a_hash_res a_hl a_tp;
    [ | move=> Hlt |  |  move=> Hlt |  | move=>Hlt ] => Ha_addr Ha_stt Ha_hl Htp Hhash_pr Hmaxvld;
    [  move=> Hlast | |    move=> Hlast |   | move=> Hlast | move=>Hlast  ];

    rewrite !actor_n_has_chain_length_ge_at_round_internalP //=;
    (* automatically dispose of any cases considering non actors *)
    try (by move: Hlast (a_addr) Ha_addr Ha_stt  => /eqP Hlast [a_addr' Ha_addr] //= Hfls;
    move:  (Ha_addr) (Ha_addr); rewrite -{1}Hfls Hlast -(addn1 n_max_actors)//=;
    move=>/ltn_weaken; rewrite ltnn).
   (* failed no update case  *)
    rewrite /honest_mint_failed_no_update/actor_n_chain_length//= => Hlen.
    rewrite/actor_n_has_chain_length_ge_at_round_internal fixlist_insert_rewrite //= has_rcons -orb_assoc.
    apply/orP; right; apply/Hbase.
    move: a_addr Ha_addr Ha_stt Ha_hl Htp Hmaxvld Hlen => [a_addr Ha_addr] Heqn.
    rewrite Heqn; move=>   Ha_stt Ha_hl Htp Hmaxvld .
    case Haddreqn: (eq_op o_addr a_addr ).
      rewrite tnth_set_nth_eq => //=.
      move: Ha_addr Heqn Ha_stt Ha_hl Htp Hmaxvld.
      rewrite /actor_n_chain_length.
      move/eqP: Haddreqn => <- Htmp; rewrite (proof_irrelevance _ Htmp Ho_addr); clear Htmp.
      by move=> Ha_addr Heqn Ha_stt Ha_hl Htp; rewrite Heqn update_round_preserves_current_chain. 
    by rewrite tnth_set_nth_neq => //=; move/negP/negP:Haddreqn.
  (* failed update case *)
    rewrite /honest_mint_failed_update/actor_n_chain_length//= => Hlen.
    rewrite/actor_n_has_chain_length_ge_at_round_internal fixlist_insert_rewrite //= has_rcons -orb_assoc.
    apply/orP; right; apply/Hbase.
    move: a_addr Ha_addr Ha_stt Ha_hl Htp Hmaxvld Hlen => [a_addr Ha_addr] Heqn.
    rewrite Heqn; move=>   Ha_stt Ha_hl Htp Hmaxvld .
    case Haddreqn: (eq_op o_addr a_addr ).
      rewrite tnth_set_nth_eq => //=.
      move: Ha_addr Heqn Ha_stt Ha_hl Htp Hmaxvld.
      rewrite /actor_n_chain_length.
      move/eqP: Haddreqn => <- Htmp; rewrite (proof_irrelevance _ Htmp Ho_addr); clear Htmp.
      move=> Ha_addr Heqn Ha_stt Ha_hl Htp.
      (* provable by showing that max valid always preserves the length *)
      admit.
    by rewrite tnth_set_nth_neq => //=; move/negP/negP:Haddreqn.
   (* succeed update case *)


  admit.
  (* adversary mint player case *)
  admit.
  (* adversary mint global case *)
  admit.
  (* corrupt case *)
  move: o_addr addr0 => [o_addr Ho_addr] [a_addr Ha_addr] .
  move=> IHn Hprw' Hadv Hact Hltn.
  rewrite /adversary_corrupt_step//=/actor_n_chain_length//= => Hvld.
  rewrite !actor_n_has_chain_length_ge_at_round_internalP //=;
  rewrite -!actor_n_has_chain_length_ge_at_round_internalP //=.
  apply IHn; move: Hvld; rewrite /actor_n_chain_length.
  have: (eq_op (a_addr) (Ordinal Ha_addr)). by [].
  move=> /eqP ->.
  case Heqn: (eq_op o_addr a_addr).
    rewrite tnth_set_nth_eq //=.
    by move: Ha_addr Hact; move/eqP: Heqn => <- Htmp; rewrite (proof_irrelevance _ Htmp Ho_addr) => ->.
  rewrite tnth_set_nth_neq //=.
  by move/negP/negP:Heqn.
  (* round end case *)
  move: o_addr => [o_addr Ho_addr]  .
  move=> IHn Hprw' Hrndend Hupd.
  rewrite /round_end_step//=/actor_n_chain_length//= => Hvld.
  rewrite !actor_n_has_chain_length_ge_at_round_internalP //=;
  rewrite -!actor_n_has_chain_length_ge_at_round_internalP //=.
  rewrite deliver_messages_update_round_preserves_round.
  move: Hrndend; rewrite /round_ended => /andP [Hrndend Hrvld]; rewrite /next_round.
  case Hwstate: [w'.state] => [gls ga gca gcr] //=.
  move: (erefl (eq_op _ _)).
  move: Hrndend; rewrite Hwstate //= addn1 => -> _.
  move: Hrvld (erefl _).
  rewrite Hwstate //= addn1 => {2 3}-> Hrvld.
  rewrite !actor_n_has_chain_length_ge_at_round_internalP //=.
  rewrite -!actor_n_has_chain_length_ge_at_round_internalP //=.
  apply actor_has_chain_length_ext with (sc:= xs) (s':=gcr) => //=.
    by move/Rlt_not_eq/nesym: Hprw'.
  move: IHn; rewrite Hwstate //= => IHn.
  apply IHn => //=.
  move: Hvld.
  rewrite /actor_n_chain_length//=.
  (* show that deliver messages preserves the lenght of the current chain *)
  admit.
  (* adversary end case *)
  admit.


Admitted.







(* ==================================================

                      Hard proofs

 ====================================================*)


Lemma no_bounded_successful_rounds_ext sc w r s : 
  (P[ world_step initWorld sc === Some w] <> 0) ->
        (~~ bounded_successful_round w s) ->
          no_bounded_successful_rounds w r s = no_bounded_successful_rounds w r s.+1.
Proof.
  move=> _.
  by move=> /no_bounded_successful_rounds_excl. (* Not so hard now, eh??? *)
Qed.



(* TODO: (move to invmisc *)
Lemma ltn_leq_trans (a b c : nat) : (a < b)%nat -> (b <= c)%nat -> (a <= c)%nat.
Proof.
  by move=>/ltnW/leq_trans H /H.
Qed.

(* contains the main meat of the chain growth weak lemma *)
Lemma chain_growth_weak_internal 
  (l : nat) (r' : 'I_N_rounds) (o_addr active_addr known_addr : 'I_n_max_actors)
  (active_iscrpt : bool) (new_os : OracleState) (active_pow  active_head_link active_hash_result  : 'I_Hash_value.+1)
  (active_new_block : BlockRecord) (active_actor_state : LocalState) (new_active_txpool : local_TransactionPool) (w' : World)
  (xs : seq.seq RndGen) :

  (actor_n_has_chain_length_at_round w' l known_addr r' ->
   actor_n_is_honest w' o_addr ->
   actor_n_is_honest w' known_addr ->

   forall s r : 'I_N_rounds,
   (r' <= r)%nat ->
   (r + delta )%nat = s -> world_executed_to_round w' s.+1 -> actor_n_has_chain_length_ge_at_round w' l o_addr s) ->

    0 < P[ world_step initWorld xs === Some w'] ->
    honest_activation [w'.state] = Some active_addr ->
    tnth [[w'.state].actors] active_addr = (active_actor_state, active_iscrpt) ->

    retrieve_head_link
      (honest_max_valid
         (update_transaction_pool active_addr active_actor_state [w'.tx_pool]) [w'.oracle]) [w'.oracle] =
          Some active_head_link ->
    find_maximal_valid_subset
      (honest_local_transaction_pool
         (update_transaction_pool active_addr active_actor_state [w'.tx_pool]))
      (honest_max_valid
         (update_transaction_pool active_addr active_actor_state [w'.tx_pool]) [w'.oracle]) =
            (active_new_block, new_active_txpool) ->
    0 < P[ hash (active_pow, active_head_link, active_new_block) [w'.oracle] === (new_os, active_hash_result)] ->
    actor_n_has_chain_length_at_round
      (honest_mint_step active_iscrpt new_os active_pow
                        active_head_link active_new_block
                        active_addr active_actor_state
                        active_hash_result w')
    l known_addr r' ->

    actor_n_is_honest (honest_mint_step active_iscrpt new_os active_pow
                                        active_head_link active_new_block
                                        active_addr active_actor_state
                                        active_hash_result w') o_addr ->
    actor_n_is_honest (honest_mint_step active_iscrpt new_os active_pow
                                        active_head_link active_new_block
                                        active_addr active_actor_state
                                        active_hash_result w') known_addr ->
  forall s r : 'I_N_rounds,
  (r' <= r)%nat ->
  (r + delta )%nat = s ->
  world_executed_to_round (honest_mint_step active_iscrpt new_os active_pow active_head_link active_new_block active_addr active_actor_state active_hash_result w') s.+1 ->
  actor_n_has_chain_length_ge_at_round
    (honest_mint_step active_iscrpt new_os active_pow active_head_link active_new_block active_addr active_actor_state active_hash_result w') l o_addr s.
Proof.







    move: o_addr known_addr active_addr  => [o_addr Ho_addr] [known_addr Hknown_addr] [active_addr Hactive_addr].
    (* honest mint case  *)
    move=> IHw' Hprw' .
    move/Rlt_not_eq/nesym: (Hprw') => Hprw''.
    move: (world_step_adoption_history_top_heavy _ _ Hprw'') => Hithw'.
    move: (world_step_adoption_history_overflow_safe _ _ Hprw'') => Hosw'.

    move=> Hhon Htnth Hretr Hfind Hhash_pr.
    move=> Hhaschain; rewrite /actor_n_is_honest //=; move: (erefl _); rewrite {2 3}Ho_addr => Htmp.
    rewrite (proof_irrelevance _ Htmp Ho_addr); clear Htmp; move: (erefl _); rewrite {2 3}Hknown_addr => Htmp.
    rewrite (proof_irrelevance _ Htmp Hknown_addr). move: Hhaschain; clear Htmp.
    apply:(@honest_mint_stepP (fun w =>
              actor_n_has_chain_length_at_round w l (Ordinal Hknown_addr) r' ->
              ~~ actor_n_is_corrupt w  (Ordinal Ho_addr) ->
              ~~ actor_n_is_corrupt w  (Ordinal Hknown_addr) ->
              forall s r : 'I_N_rounds,
                (r' <= r)%nat ->
                (r + delta )%nat = s ->
                world_executed_to_round w s.+1 ->
                actor_n_has_chain_length_ge_at_round w l o_addr s)
                              w' active_iscrpt new_os  active_pow  active_head_link active_new_block
                              (Ordinal Hactive_addr) active_actor_state  active_hash_result  new_active_txpool
                   Hhon Htnth Hretr Hfind Hhash_pr
          );
    clear Hhash_pr Hfind Hhon Htnth Hretr;
    clear active_pow active_head_link active_hash_result
          active_new_block active_actor_state active_iscrpt
          active_addr Hactive_addr new_os new_active_txpool;
    move => //= a_iscrpt a_addr a_state new_os a_block a_hash_result a_pow a_head_link a_txpool;
             [ | move=> Hprf_ltn | | move=> Hprf_ltn | | move=> Hprf_ltn ] =>
    Hwactive Hactive_state_eq Hactive_hlink Hnew_blockcontents Hhash_pr
    ;[ move=> Hmaxvld Hactiveaddr | move=> Hmaxvld | move=> Hmaxvld Hactiveaddr |
       move=> Hmaxvld | move=> Hresult Hactiveaddr | move=> Hresult Hactiveaddr];
      move: IHw';
      rewrite /actor_n_has_chain_length_ge_at_round/world_executed_to_round/actor_n_has_chain_length_at_round;
      rewrite /actor_n_is_honest/actor_n_is_corrupt;
      move:  (erefl _) => //=; rewrite {2 3}Ho_addr => Htmp; rewrite (proof_irrelevance _ Htmp Ho_addr); clear Htmp;
    move: (erefl _); rewrite {2 3} Hknown_addr => Htmp; rewrite (proof_irrelevance _ Htmp Hknown_addr); clear Htmp;
    (* we can easily eliminate all cases that consider the active index being the last actor *)
    (try by destruct a_addr as [a_addr Ha_addr]; move: Hactiveaddr  Hwactive (Ha_addr) (Ha_addr) => /eqP -> //= <-; rewrite -{1}addn1=>/ltn_weaken;rewrite ltnn); move=> IHw'.



    (* failed attempt with non-last entry and no update *)
      move=> H_has_chain_length_l_at_r' Hhonother Hhonknown.
      move=> s r Hr_is_valid Hs_eq_rdelta Hexecuted_to_s.
      move: Hwactive Hprf_ltn H_has_chain_length_l_at_r' Hhonother Hhonknown.

      (* we need to do some rewrite to neaten things up. *)
(*          first let's eradicate a_addr, and replace all instaces with w_addr *)
      case Hcurr_round_value: ([[w'.state].#active])
      => [w_state_active Hw_state_prf] //= Haddr_eq.
      move: a_addr Haddr_eq Hactive_state_eq Hactive_hlink Hnew_blockcontents Hmaxvld
                            Hexecuted_to_s => [a_addr Ha_addr] //= Haddr_eq.
      move: Ha_addr; rewrite -Haddr_eq; clear a_addr  Haddr_eq => Hwstate.
      move=> Hactive_state_eq Hactive_hlink Hnew_blockcontents Hmaxvld Hwexec Hincr Hhaschain.
      move=> HoaddrHon HkaddrHon; move: Hhaschain.
      case Hw_round_eq: ([[w'.state].#round]) => [w_state_round Hwstatrnd] //=.
      (* finally we're ready to rumble *)
      (* first, lets' solve the case when the length is 0 *)
      (* to prove the goal, we need to consider 2 cases of our assumption. *)
(*          1. where the newly inserted record meets the conditions - i.e *)
(*                the current chain's length is equal to l *)
(*                the current round is r' *)
(*                the  currently active node is the known addr's actor *)
(*          2. where somewhere in the contents of the world chain history there is a *)
(*             record of a chain of length l, being adopted at round r' by the known_addr's actor*)
      rewrite fixlist_insert_rewrite //=
              !has_rcons -orb_assoc
      => /orP [/andP [/eqP Hlen /andP [/eqP Hround /eqP Hwstateeq] ] | Ho_has_chain]; last first.
      rewrite -orb_assoc; apply/orP; right.
      apply:(IHw' _ _ _ s r) => //=.
      move: HoaddrHon.
      have: w_state_active = Ordinal Hwstate. by [].
      move=>{2}->.
      case Heq: (eq_op o_addr w_state_active ).
        rewrite tnth_set_nth_eq //= => Hncrpt.
        by move: (Ho_addr); move/eqP: Heq -> => Htmp; rewrite (proof_irrelevance _ Htmp Hwstate);
        rewrite Hactive_state_eq.
        rewrite tnth_set_nth_neq => //=.
        by move/negP/negP:Heq.
      move: HkaddrHon.
      have: w_state_active = Ordinal Hwstate. by [].
      move=>{2}->.
      case Heq: (eq_op known_addr w_state_active ).
        rewrite tnth_set_nth_eq //= => Hncrpt.
        by move: (Hknown_addr); move/eqP: Heq -> => Htmp; rewrite (proof_irrelevance _ Htmp Hwstate);
        rewrite Hactive_state_eq.
        rewrite tnth_set_nth_neq => //=.
        by move/negP/negP:Heq.
      (* case where the new record meets the conditions *)
        (* we know that as r' <= r and r' == current round, the current_round <= r *)
        (* we also know that we have executed to round s - i.e s <= current_round *)
        (* we also know that r <= s, as s = r + delta *)

        move: Hr_is_valid; rewrite -Hround //=.
        have Hrlts: (r <= s)%nat.
          rewrite -Hs_eq_rdelta.
          by apply leq_addr.

        move: Hwexec. rewrite Hw_round_eq//=.
        move=>/(ltn_addr 2); rewrite addn2 -{1}(addn1 s) -{1}(addn1 _.+1) ltn_add2r ltnS.

      (* this all means that r == s, *)
          move=> /leq_trans H /H; clear H; move: (Hrlts);
                  move=> /ltnSn_eq H /H; clear H => /eqP Hseqr.

        (* however r + delta == s, thus delta must be 0 *)
        move: Hs_eq_rdelta; rewrite Hseqr => /eqP/addn_eq0/eqP Hdlta //=.

        (* hoever, we are operating within the bounded delay model, which requires that delta must be *)
(*           greater than 0 *)
        by move: delta_valid; rewrite Hdlta ltnn.



     (* another unsuccessful case (but this time, the actor changes it's chain) - uses the same logic as above *)
      move=> H_has_chain_length_l_at_r' Hhonother Hhonknown.
      move=> s r Hr_is_valid Hs_eq_rdelta Hexecuted_to_s.
      move: Hwactive Hprf_ltn H_has_chain_length_l_at_r' Hhonother Hhonknown.
      case Hcurr_round_value: ([[w'.state].#active])
      => [w_state_active Hw_state_prf] //= Haddr_eq.
      move: a_addr Haddr_eq Hactive_state_eq Hactive_hlink Hnew_blockcontents Hmaxvld
                            Hexecuted_to_s => [a_addr Ha_addr] //= Haddr_eq.
      move: Ha_addr; rewrite -Haddr_eq; clear a_addr  Haddr_eq => Hwstate.
      move=> Hactive_state_eq Hactive_hlink Hnew_blockcontents Hmaxvld Hwexec Hincr Hhaschain.
      move=> HoaddrHon HkaddrHon; move: Hhaschain.
      case Hw_round_eq: ([[w'.state].#round]) => [w_state_round Hwstatrnd] //=.
      rewrite fixlist_insert_rewrite //=
              !has_rcons -orb_assoc
      => /orP [/andP [/eqP Hlen /andP [/eqP Hround /eqP Hwstateeq] ] | Ho_has_chain]; last first.
      rewrite -orb_assoc; apply/orP; right.
      apply:(IHw' _ _ _ s r) => //=.
      move: HoaddrHon.
      have: w_state_active = Ordinal Hwstate. by [].
      move=>{2}->.
      case Heq: (eq_op o_addr w_state_active ).
        rewrite tnth_set_nth_eq //= => Hncrpt.
        by move: (Ho_addr); move/eqP: Heq -> => Htmp; rewrite (proof_irrelevance _ Htmp Hwstate);
        rewrite Hactive_state_eq.
        rewrite tnth_set_nth_neq => //=.
        by move/negP/negP:Heq.
      move: HkaddrHon.
      have: w_state_active = Ordinal Hwstate. by [].
      move=>{2}->.
      case Heq: (eq_op known_addr w_state_active ).
        rewrite tnth_set_nth_eq //= => Hncrpt.
        by move: (Hknown_addr); move/eqP: Heq -> => Htmp; rewrite (proof_irrelevance _ Htmp Hwstate);
        rewrite Hactive_state_eq.
        rewrite tnth_set_nth_neq => //=.
        by move/negP/negP:Heq.
        move: Hr_is_valid; rewrite -Hround //=.
        have Hrlts: (r <= s)%nat.
          rewrite -Hs_eq_rdelta.
          by apply leq_addr.
        move: Hwexec. rewrite Hw_round_eq//=.
        move=>/(ltn_addr 2); rewrite addn2 -{1}(addn1 s) -{1}(addn1 _.+1) ltn_add2r ltnS.
          move=> /leq_trans H /H; clear H; move: (Hrlts);
                  move=> /ltnSn_eq H /H; clear H => /eqP Hseqr.
        move: Hs_eq_rdelta; rewrite Hseqr => /eqP/addn_eq0/eqP Hdlta //=.
        by move: delta_valid; rewrite Hdlta ltnn.



   (* successful attempt with non-last entry *)

      rewrite/honest_mint_succeed_update.
      case Hhon_max_valid: (honest_max_valid _) => [chain_pool Hchain_pool] //=.
      case Hupdated_chain: (fixlist_enqueue _ ) => [new_chain old_block] //=.
      move=> Hhaschain Hhoaddrhon Hcorrupt.
      move=> s r Hr_is_valid Hs_eq_rdelta Hexecuted_to_s.
      move: Hhaschain Hhoaddrhon Hcorrupt Hexecuted_to_s Hwactive Hprf_ltn.


      (* now - let's eradicate a_addr, and replace all instaces with w_addr *)
      case Hcurr_round_value: ([[w'.state].#active])
      => [w_state_active Hw_state_prf] //= Haddr_eq.
      move: Hactive_state_eq Hactive_hlink Hnew_blockcontents  Haddr_eq Hhon_max_valid.
      case: a_addr => [a_addr Ha_addr] //= .
      move=> Hactive_state_eq Hactive_hlink Hnew_blockcontents  Haddr_eq Hhon_max_valid.
      move=> Hknaddrhon Hhoaddrhon Hcorrupt Hexecuted_to_s Hactiveincr.
      move: Haddr_eq.
      rewrite fixlist_insert_rewrite //= !has_rcons -!orb_assoc => /orP [ /andP [] | Ho_has_chain]; last first.
      (* Inductive hypothesis case*)
      have Hwsteq: (w_state_active = (Ordinal Ha_addr)). by rewrite Hexecuted_to_s//=.
      apply/orP;right; apply IHw' with (r := r) => //=.
      move: Hknaddrhon ; rewrite Hwsteq.
      case Haddreq: (eq_op o_addr a_addr ).
        rewrite tnth_set_nth_eq //=.
        move: (Ho_addr); move/eqP: Haddreq => -> Htmp; rewrite (proof_irrelevance _ Htmp Ha_addr); clear Htmp.
        by rewrite Hactive_state_eq.
        rewrite tnth_set_nth_neq //=.
        by move/negP/negP: Haddreq.
      move: Hhoaddrhon ; rewrite Hwsteq.
      case Haddreq: (eq_op known_addr a_addr ).
        rewrite tnth_set_nth_eq //=.
        move: (Hknown_addr); move/eqP: Haddreq => -> Htmp; rewrite (proof_irrelevance _ Htmp Ha_addr); clear Htmp.
        by rewrite Hactive_state_eq.
        rewrite tnth_set_nth_neq //=.
        by move/negP/negP: Haddreq.
      (* non inductive case *)
      move=>/eqP Hlen /andP [/eqP Hstround Haddr].

      move: Hr_is_valid; rewrite -Hstround .
      move: Hcorrupt => /(ltn_addr 2); rewrite addn2 -{1}(addn1 s) -{1}(addn1 _.+1) ltn_add2r ltnS.
      move=>/leq_trans H /H; clear H.
      have Hrlts: (r <= s)%nat.
        rewrite -Hs_eq_rdelta.
        by apply leq_addr.
      move: (Hrlts); move=> /ltnSn_eq H /H; clear H => /eqP Hseqr.
      move: Hs_eq_rdelta ; rewrite Hseqr => /eqP/addn_eq0/eqP Hdlta //=.
      by move: delta_valid; rewrite Hdlta ltnn.
Qed.




Definition queued_message_pool_contains_chain_of_length o_msgs l :=
  match o_msgs with
  | Some msgs => message_pool_contains_chain_of_length msgs l
  | None => false || (eq_op l 0%nat)
  end.


(* knowing an actor has a chain of length isn't particularly helpful. we'd ideally like to deal primarily
   with the first time an actor has a chain of a particular length *)
Lemma has_chain_length_exists_first sc w r  l  o_addr :
  (P[ world_step initWorld sc === Some w] <> 0) ->
  actor_n_is_honest w o_addr ->
  actor_n_has_chain_length_ge_at_round w l o_addr r ->
  exists (r' : 'I_N_rounds), (r' <= r)%nat &&
                actor_n_first_has_chain_length_ge_at_round w l o_addr r'.
Proof.
  move=> Hpr Hhon.
  rewrite /actor_n_first_has_chain_length_at_round.
  case: r => [r ]; elim: r => //= [ | r IHr] .
    move=> prf0 Hhasch; exists (Ordinal valid_N_rounds).
    by apply/andP; split => //=; apply/andP; split => //=.
  move=> Hprf Hashchn.
  case Hall: (all (fun round : nat => ~~ actor_n_has_chain_length_ge_at_round_nat w l o_addr round)
          (iota 0 r.+1)) .
    by exists (Ordinal Hprf) ; apply/andP; split => //=; apply/andP; split => //=; apply/andP; split => //=.
    
  move/allPn: Hall =>  [r0].
  rewrite mem_iota add0n ltnS (leq_eqVlt r0) negb_involutive => /andP [  Hr0vld  /orP Hltn] Hchnln.
  move: Hltn =>  [/eqP Hr0r' | Hrltr'].
  move: Hchnln; rewrite /actor_n_has_chain_length_ge_at_round_nat Hr0r'.
    move: (Hprf); rewrite -{1}(addn1 r) => /(ltn_weaken) Hltnr; move: (erefl _).
    rewrite {2 3}Hltnr => Htmp; rewrite (proof_irrelevance _ Htmp Hltnr); clear Htmp => Hchnln.
    move: (IHr Hltnr Hchnln) => [x /andP [Hxrng Hhaschainlen]].
    exists x; apply/andP; split => //=.
    by move: Hxrng; rewrite -(ltnS x r) -(ltnS x r.+1) -{1}(addn1 r.+1) => /(ltn_addr 1).
  move: (Hprf); rewrite -{1}(addn1 r) => /(ltn_weaken) Hltnr.
  move: Hchnln; rewrite /actor_n_has_chain_length_ge_at_round_nat; case: {2 3}(r0 < _)%nat (erefl _) => //= Hrvld.
  move=> Hhashchn.
  have Hchl: actor_n_has_chain_length_ge_at_round w l o_addr (Ordinal Hltnr).
    by apply actor_has_chain_length_ext with (sc:= sc) (s' := (Ordinal Hrvld)) => //=; apply ltnW.
  move: (IHr Hltnr Hchl) => [x /andP [Hxlen Hhaschn]].
  exists x; apply/andP;split => //=.
  by move: Hxlen; rewrite -(ltnS x r) -(ltnS x r.+1) -{1}(addn1 r.+1) => /(ltn_addr 1).
Qed.

(* if an we have a record of an actor obtaining a message first at a particular round, this means
   that the actor must have broadcast the message at that round (so it'll turn up in the message queue
   for the next round *)
Lemma first_has_chain_length_implies_broadcast sc w (r: 'I_N_rounds)  l  o_addr :
  (P[ world_step initWorld sc === Some w] <> 0) ->
  (world_executed_to_round w  r.+1) ->
  actor_n_is_honest w o_addr ->
  (* if an honest actor first has a chain greater than a length at a particular round, by the protocol
   used by the nodes, it MUST broadcast out the message to all parties - hence *)
  actor_n_first_has_chain_length_ge_at_round w l o_addr r ->
  message_pool_contains_chain_of_length_ge ((world_message_queue_at_round w r.+1).1).1  l.
Admitted.

(* if the nth entry in the fixlist queue contains a message of length l, then by the next round,
    the n.+1th entry contains a message of length l*)
Lemma broadcast_propagates sc w r l o_addr n : 
  (P[ world_step initWorld sc === Some w] <> 0) ->
  (world_executed_to_round w  (nat_of_ord r + n).+1) ->
  (n < delta)%nat ->
  actor_n_first_has_chain_length_ge_at_round w l o_addr r ->
  (* then the bin which at round r + k contains a chain of length l*)
  o_message_pool_contains_chain_of_length_ge
    (fixlist_get_nth
       ((world_message_queue_at_round w (r + n)).1).2
       n)  l.
Admitted.

(* if a message reaches the end of the queue  then every actor will have a chain greater than it's length *)
Lemma broadcast_terminates sc w r l : 
  (P[ world_step initWorld sc === Some w] <> 0) ->
  (world_executed_to_round w  (r + delta)) ->
  o_message_pool_contains_chain_of_length_ge
    (fixlist_get_nth
       ((world_message_queue_at_round w (r + delta.-1)).1).2
       (delta.-1))  l ->
      forall (o_addr : 'I_n_max_actors) (prf: (r + delta < N_rounds)%nat),
          (* all actors, if honest *)
          (actor_n_is_honest w o_addr) ->
            (* have a chain of length of at least
              l  *)
              actor_n_has_chain_length_ge_at_round
                    w
                    l
                    o_addr
                    (Ordinal prf).



  
Admitted.




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
   actor_n_is_honest w addr && 
  (nat_of_ord k <= nat_of_ord r)%nat && actor_n_has_chain_length_at_round w l addr k) ->
  (* then at r + delta - 1, every actor would have broadcasted a chain of length at least l*)
  (* we're using this forall quantification here to allow creating a ordinal type without having to use dependant types*)
  forall s,
     (eq_op (r + delta)%nat (nat_of_ord s)) ->
      (* and the world executed to the round *)
      world_executed_to_round w s.+1 ->
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
  move=> Hpr [addr [r' /andP [/andP [Hhonaddr Hr'ltr ] Hacthaschain]]] s /eqP Hreqs wexec o_addr Hhon.
  move:  Hacthaschain Hhon Hhonaddr  s r Hr'ltr  Hreqs wexec.

  apply /(world_stepP
            (fun w _ =>
              actor_n_has_chain_length_at_round w l addr r' ->
              actor_n_is_honest w o_addr ->
              actor_n_is_honest w addr ->
              forall s r : 'I_N_rounds, (r' <= r)%nat ->
              (r + delta)%nat = s -> world_executed_to_round w s.+1 -> actor_n_has_chain_length_ge_at_round w l o_addr s
            ) sc w) => //=  [
                              iscrpt  os  hash_value hash_vl  blc_rcd addr0  lclstt  result  ltp w'  xs  |
                              oracle_state  old_adv_state  blc_rcd nonce hash hash_res  w'  xs |
                              adv_state  w' xs |
                              addr0  actr  w'  xs |
                              msgs new_pool w' xs |
                              w'  xs ] //=.
  (* base case *)
  (* move=> Hacthaschain Hhon  s. *)
  (* case: s => [s ]. *)
  (* elim: s => //= [Hlt0  ]. *)
  (*   move=> [[//=|//=]] Hrlr' => /eqP. *)
  (*   rewrite subn0 add0n => _ Hdlta0. *)
  (*   move: delta_valid. *)
  (*   by rewrite Hdlta0 ltnn. *)

  (* honest mint case *)
  (* this one ends up being the longest and contains the real "logic" steps, so it has been refactored out *)
  by apply chain_growth_weak_internal  => //=.

  (* adversary mint case *)
    move=> IHw' Hprw' Hacthaschain Hhon s.
    rewrite /adversary_mint_player_step/actor_n_has_chain_length_ge_at_round/actor_n_has_chain_length_at_round//=.
    (* trivially true - it doesn't matter whether the adversary succeeds in hashing or not, as either way, *)
  (*      the adoption history is not changed*)
    by case: (hash_res < T_Hashing_Difficulty)%nat => //=.

  (* global adversary case *)
    move=> IHw' Hprw' Hacthaschain Hhon  s Hpradv.
    rewrite /adversary_mint_global_step/actor_n_has_chain_length_ge_at_round.
    rewrite /actor_n_has_chain_length_at_round//=.
    (* once again trivially true *)
    by move: adv_state Hpradv => [[stt os] blk] //=.
  
  (* adversary corrupt case *)
    move=> IHw' Hprw' Hacthaschain Hhon  s Hpradv Hhonw' Hhonaddr  s0 r0 Hr0gtr' Heqn .
    rewrite /adversary_corrupt_step/actor_n_has_chain_length_ge_at_round.
    rewrite /actor_n_has_chain_length_at_round//=.
    rewrite /world_executed_to_round//= -/world_executed_to_round => Hwrld.
    apply IHw' with (r := r0) => //=.
    move: Hhonw'.
    rewrite/actor_n_is_honest/actor_n_is_corrupt //=.
    move: (erefl _) => //=; move: (xpred0) => //= .
    case Hgt: ((o_addr >= n_max_actors)%nat).
    move: Hgt; rewrite leqNgt => /negP/eqP/eqP/ not_true_is_false Hwrong.
    by rewrite {3 4  7 }Hwrong => //=.
    move/negP/negP: (Hgt); rewrite -ltnNge => Hprf.
    rewrite {3 4  7 }Hprf => //= _ Hprfltn.
    destruct ((global_local_states (world_global_state w'))) as [ls Hls].

    move: Hhon IHw' Hpradv Hgt Hprf Hprfltn.
    move: o_addr addr0 Hhonaddr => [addr0 Haddr0] [o_addr H_o_addr] Hhonaddr.
    move=> Hhon IHw' Hpradv Hgt Hprf Hprfltn.
    case Haddreqn: (eq_op o_addr addr0).
    rewrite tnth_set_nth_eq => //=.
    by apply/eqP; symmetry; apply/eqP.
    by rewrite tnth_set_nth_neq => //=; apply/eqP/not_eq_sym; move/negP/negP/eqP: Haddreqn.
    move: Hhonaddr.
    rewrite/actor_n_is_honest/actor_n_is_corrupt //=.
    destruct addr as [addr Haddr] => //=; move: (erefl _).
    rewrite {2 3 7}Haddr => Htmp; rewrite (proof_irrelevance _ Htmp Haddr) //=; clear Htmp.
    destruct addr0 as [addr0 Haddr0].
    case Haddr_eqn : (eq_op addr addr0).
      by rewrite tnth_set_nth_eq.
      by rewrite tnth_set_nth_neq => //=; move/negP/negP: Haddr_eqn.
  (* round end case *)
    move=> IHw' Hprw' Hrndend Hacthaschain Hhon Hhonaddr s [new_round Hnew_round].
    move: o_addr IHw' Hhonaddr s  => [o_addr Ho_addr] IHw' Hhonaddr s.
    (* if r + delta <= [[w'.state].#round] we can just use the induction hypothesis to prove the goal*)
    case Hltn: (new_round.+1 < nat_of_ord [[w'.state].#round])%nat.
      rewrite !actor_n_has_chain_length_ge_at_round_internalP.
      rewrite /round_end_step/world_executed_to_round//=.
      rewrite deliver_messages_update_round_preserves_round//=.
      move=> [r Hr_valid] Hrltr' Hrdlta Hnewltn.

      move: Hacthaschain Hhon s; move: Hrndend Hnewltn; rewrite/round_ended addn1 /next_round.
      case Hw_state: [w'.state] => //= [gact gadv gca gcr] //= /andP [Hgca_eqn Hrvld].
      move: (erefl (eq_op _ _)); rewrite Hgca_eqn => _.
      move: Hrvld; rewrite addn1 => Hrvld.
      move: (erefl _); rewrite {2 3}Hrvld => Htmp; rewrite (proof_irrelevance _ Htmp Hrvld); clear Htmp.
      rewrite ltnS => Hnrgcr.
      rewrite !actor_n_has_chain_length_at_round_internalP.
      rewrite -!actor_n_has_chain_length_at_round_internalP.
      rewrite -!actor_n_has_chain_length_ge_at_round_internalP.
      rewrite !actor_n_is_honest_internalP.
      move=> Hupd Hhaschn Hhon.
      apply IHw' with (r:=(Ordinal Hr_valid)) (s:=(Ordinal Hnew_round)) => //=; last first.
        move: Hhon; rewrite/round_end_step /actor_n_is_honest /actor_n_is_honest_internal
                          /actor_n_is_corrupt /actor_n_is_corrupt_internal //=.
        destruct addr as [addr Haddr] => //=; move: (erefl _).
        rewrite {2 3 7}Haddr => Htmp; rewrite (proof_irrelevance _ Htmp Haddr) //=; clear Htmp.
        by move=> /deliver_messages_preserves_honest.
        move: Hhonaddr; rewrite !actor_n_is_honest_internalP/actor_n_is_honest_internal //=.
        move: (erefl _) ; rewrite {2 3 7}Ho_addr => Htmp; rewrite (proof_irrelevance _ Htmp Ho_addr).
        by clear Htmp => /deliver_messages_preserves_honest.
    (* this means that r + delta >= current round *)
    move/negP/negP:Hltn. rewrite -ltnNge => Hltn.
      move=> //= [r Hr_valid] //= Hrltr' Hrdlta ;
      rewrite/world_executed_to_round//= deliver_messages_update_round_preserves_round.
      move: Hacthaschain Hhon s; move: Hltn Hrndend ; rewrite/round_ended addn1 ;
      case Hw_state: [w'.state] => //= [gact gadv gca gcr] //= Hnexec /andP [Hgca_eqn Hrvld] Hupd .
      rewrite Hgca_eqn => //=; move: Hrvld (erefl _); rewrite addn1 => {2 3}-> //= prf Hchl Hhon.
    move: (Hnexec); rewrite leq_eqVlt => /orP []; last first.
    (* if r + delta > gcr, we obtain a contradiction  *)
      by rewrite (ltnS gcr.+1 new_round.+1) => /leq_ltn_trans H /H; rewrite ltnn.
    move=>/eqP [] Hgcr_eqn Hltn.
    (* thus the current round is equal to (r + delta).+1 *)
    move: (Hchl); rewrite !actor_n_has_chain_length_at_round_internalP
                         {1}/round_end_step //= -!actor_n_has_chain_length_at_round_internalP
    => /actor_has_chain_length_generalize.
    move/Rlt_not_eq/nesym: Hprw' => Hprw'.
    move=>/(has_chain_length_exists_first xs w' _ l _ Hprw') [].
    move: addr IHw' Hchl Hhon => [addr Haddr] Ihw' Hchl Hhon.
    move: Hhon; rewrite /actor_n_is_honest; move: (erefl _); rewrite {2 3 7}Haddr => Htmp.
    rewrite (proof_irrelevance _ Htmp Haddr); clear Htmp.
    by rewrite /actor_n_is_corrupt //= => /deliver_messages_preserves_honest.
    move=> r0 /andP [ Hr0ltr' Hfirst ].
    have Hrprev : (r0 + delta <= r + delta)%nat.
      by rewrite leq_add2r; apply leq_trans with (n:= r') => //=.
    have Hr0dlt : (r0 + delta < N_rounds)%nat.
      apply leq_ltn_trans with (n:=new_round) => //=.
      by rewrite -Hrdlta.
    move: Hnew_round; rewrite -Hrdlta => H_rdlta.
    apply:(actor_has_chain_length_ext (xs) w' l o_addr (Ordinal Hr0dlt)) => //=.

    move: Hhonaddr; rewrite  !actor_n_is_honest_internalP/actor_n_is_honest_internal //=.
    move: (erefl _); rewrite {2 3}Ho_addr => Htmp; rewrite (proof_irrelevance _ Htmp Ho_addr); clear Htmp.
    rewrite /actor_n_is_corrupt_internal => /deliver_messages_preserves_honest Hhonaddr.
    apply: (broadcast_terminates  xs w' r0 l Hprw' _ _ (Ordinal Ho_addr)) => //=; first last .
      move: Hhonaddr; rewrite/actor_n_is_honest; move: (erefl _); rewrite {2 3}Ho_addr => Htmp.
      by rewrite (proof_irrelevance _ Htmp Ho_addr) /actor_n_is_corrupt; clear Htmp => //=.
    apply: (broadcast_propagates xs w' r0 l addr) => //=.
      rewrite /world_executed_to_round Hw_state //=.
      by rewrite Hgcr_eqn -addnS prednK //=; [rewrite -Hrdlta | exact delta_valid].
      by case: delta delta_valid => //=.
    by rewrite/world_executed_to_round Hw_state //= Hgcr_eqn -Hrdlta.


  (* adversary end case *)
    move=> IHw' Hprw' Hact Hacthaschain Hhonaddr  Hhon s .
    rewrite /adversary_end_step/actor_n_has_chain_length_ge_at_round.
    rewrite /actor_n_has_chain_length_at_round/world_executed_to_round//=.
    move=> r Hrltr Hreqdls Hhas.
    apply IHw' with (r:= r) => //=.
    move: Hhonaddr.
    rewrite /actor_n_is_honest/adversary_end_step//=.
    move: (erefl _).
    case Hltn: ((o_addr >= n_max_actors)%nat).
      move: Hltn; rewrite leqNgt => /negP/eqP/eqP/not_true_is_false Hwrong.
      by rewrite { 2 3  7}Hwrong.
    move/negP/negP: Hltn; rewrite -{1}ltnNge => Hltn.
    rewrite { 2 3 7 }Hltn => prf'.
    rewrite /actor_n_is_corrupt //=.
    by move=> /update_round_preserves_honest.
    move: Hhon.
    rewrite /actor_n_is_honest//=; move: (erefl _).
    destruct addr as [addr Haddr] => //=; rewrite {2 3 7}Haddr => Htmp.
    rewrite (proof_irrelevance _ Htmp Haddr); clear Htmp.
    by rewrite /actor_n_is_corrupt/adversary_end_step//= => /update_round_preserves_honest.
    move: Hhas; rewrite /update_round/world_executed_to_round.
    case: [w'.state] => [gls ga gca gr].
    by case: {2 3}(eq_op _ _) (erefl _) => Htmp //=.
Qed.



(* the following is a lemma that is implicitly used in the chain growth proof.
    if at round s,
      all honest parties have a chain length greater than (l + no_bounded_successful_rounds r k),
    then, at round s - delta,
      all honest parties have a chain length greater than (l + no_bounded_successful_rounds r (k - delta + 1))
 *)
Lemma chain_growth_implicit_weaken sc w l (r : 'I_N_rounds) s : forall Hsvalid Hsvddelta,
    (* if the world is valid *) 
  (P[ world_step initWorld sc === Some w] <> 0) ->
    (* and round s was a bounded successful round*) 
  bounded_successful_round w (s - delta) ->
  (* and at round s,
            every actor has a chain longer than l + sum_{s - delta} *) 
  (forall o_addr : 'I_n_max_actors,
  actor_n_is_honest w o_addr ->
  actor_n_has_chain_length_ge_at_round w (l + no_bounded_successful_rounds w r (s - delta)) o_addr
    (Ordinal (n:=N_rounds) (m:=s) Hsvalid)) ->
  (*  this means that at round s - delta,
            every actor must have had a chain longer than l + sum{s - 2 * delta + 1)*)
  (forall o_addr : 'I_n_max_actors,
  actor_n_is_honest w o_addr ->
  actor_n_has_chain_length_ge_at_round w (l + no_bounded_successful_rounds w r (s.+1 - 2 * delta )) o_addr
    (Ordinal (n:=N_rounds) (m:=s - delta) Hsvddelta)).
Proof.
  move=> Hsvalid Hsvddelta Hpr.
  move=> Hbound Hbase o_addr Hhon.
  move: Hbound Hhon (Hbase o_addr Hhon) .
  clear Hbase.
  (* just neaten up the proof first to the form,
     if s is a bounded successful round, and an actor a is honest with a chain length greater than
     s - delta at round s, then the actor has a chain length greater than s.+1 - 2 * delta at
     round s - delta.
    (* potentially if we need it, we can reintroduce the fact that every other honest actor
       at round s also has a chain of length s *)
   *)
  

  apply/(world_stepP (fun w _ =>
  bounded_successful_round w (s - delta) ->
  actor_n_is_honest w o_addr ->
  actor_n_has_chain_length_ge_at_round
    w (l + no_bounded_successful_rounds w r (s - delta)) o_addr
    (Ordinal (n:=N_rounds) (m:=s) Hsvalid) ->
  actor_n_has_chain_length_ge_at_round
    w (l + no_bounded_successful_rounds w r (s.+1 - 2 * delta))
    o_addr (Ordinal (n:=N_rounds) (m:=s - delta) Hsvddelta)
                     ) sc w ) => //= [ |
                          iscrpt  os  hash_value active_hash_link blc_rcd active_addr  active_state result
                          active_transaction_pool w'  xs  |
                          oracle_state  old_adv_state  blc_rcd nonce hash hash_res  w'  xs |
                          adv_state  w' xs |
                          addr0  actr  w'  xs |
                          msgs new_pool w' xs |
                          w'  xs ] .
  (* base case *)
    by rewrite !no_bounded_successful_rounds_init addn0;
    rewrite /actor_n_has_chain_length_ge_at_round//=/initWorldAdoptionHistory//=;
    move: (fixlist_empty_is_empty [eqType of BlockChain * 'I_N_rounds * 'I_n_max_actors] (n_max_actors * N_rounds));
    rewrite /fixlist_is_empty =>/eqP -> //=.
  (* honest mint case *)
    move: o_addr => [o_addr Ho_addr].
    move=> Hbase Hth_pr Hhonest_activation Hactive_state Ha_head_link Ha_txpool Hhash_pr .

    move/Rlt_not_eq/nesym: Hth_pr => Hth_base.
    move: (world_step_adoption_history_top_heavy xs w' Hth_base) => Hfith.
    move:(world_step_adoption_history_overflow_safe xs w' Hth_base) => Hos.
    apply /(@honest_mint_stepP (fun w =>

  bounded_successful_round w (s - delta) ->
  actor_n_is_honest w (Ordinal (n:=n_max_actors) (m:=o_addr) Ho_addr) ->
  actor_n_has_chain_length_ge_at_round
   w (l + no_bounded_successful_rounds w r (s - delta))
   (Ordinal (n:=n_max_actors) (m:=o_addr) Ho_addr)
    (Ordinal (n:=N_rounds) (m:=s) Hsvalid) ->
  actor_n_has_chain_length_ge_at_round
    w (l + no_bounded_successful_rounds w r (s.+1 - 2 * delta))
    (Ordinal (n:=n_max_actors) (m:=o_addr) Ho_addr)
    (Ordinal (n:=N_rounds) (m:=s - delta) Hsvddelta)
          ) w' iscrpt os hash_value active_hash_link
                               blc_rcd active_addr active_state
                               result active_transaction_pool) => //=;
    clear  Hhonest_activation Hactive_state Ha_head_link Ha_txpool iscrpt ;
    clear result os hash_value active_hash_link blc_rcd active_addr active_state Hhash_pr active_transaction_pool;
    move=> a_crpt a_addr  a_stt new_os a_block a_result a_hash_res a_hl a_tp;
    [ | move=> Hlt |  |  move=> Hlt |  | move=>Hlt ] => Ha_addr Ha_stt Ha_hl Htp Hhash_pr Hmaxvld;
    [  move=> Hlast | |    move=> Hlast |   | move=> Hlast | move=>Hlast  ]; 

    rewrite !actor_n_has_chain_length_ge_at_round_internalP //=;
    rewrite !actor_n_is_honest_internalP //=;
    rewrite !actor_n_is_honest_unwrapP //=;
    rewrite !bounded_successful_round_internalP//=;
    rewrite -!bounded_successful_round_internalP//=;
    rewrite !no_bounded_successful_rounds_internalP //=;
    rewrite -!no_bounded_successful_rounds_internalP //=;

    (* automatically dispose of any cases considering non actors *)
    try (by move: Hlast (a_addr) Ha_addr Ha_stt  => /eqP Hlast [a_addr' Ha_addr] //= Hfls;
    move:  (Ha_addr) (Ha_addr); rewrite -{1}Hfls Hlast -(addn1 n_max_actors)//=;
    move=>/ltn_weaken; rewrite ltnn).

    (* failed no update *)
      move=> Hbound Hhon.
      rewrite /actor_n_has_chain_length_ge_at_round_internal fixlist_insert_rewrite //=.
      rewrite has_rcons -orb_assoc => /orP [ | Hhas_base]; last first.
        (* inductive hypothesis case *)
        rewrite has_rcons -orb_assoc; apply/orP; right.
        apply Hbase => //=.
        move: Hhon; rewrite /actor_n_is_honest/actor_n_is_honest_internal_unwrap//=.
        move: (erefl _ ); rewrite {2 3 7}Ho_addr => //= Htmp.
        rewrite (proof_irrelevance _ Htmp Ho_addr); clear Htmp.
        rewrite /actor_n_is_corrupt/actor_n_is_corrupt_internal_unwrap//=.
        move: a_addr Ha_addr Ha_stt Ha_hl Htp Hmaxvld
        => [a_addr Ha_addr] Haddr_eqn.
        rewrite Haddr_eqn; move=> Ha_stt Ha_hl Htp Hmaxvld.
        case Haddreqn: (eq_op (Ordinal   Ho_addr) (Ordinal   Ha_addr)).
          by move/eqP: (Haddreqn) => ->; rewrite Ha_stt tnth_set_nth_eq //=.
          by rewrite tnth_set_nth_neq //=; move/negP/negP:Haddreqn.
      move=>/andP [HlenLt /andP [ Hsltrnd /eqP Haddr ]].
      (* let's get rid of a_addr *)
      move:  a_addr Haddr Ha_addr Ha_stt Ha_hl Htp Hmaxvld Hhon => [tmp_addr Htmp_addr] Heqn.
      have Haddreqn: (tmp_addr = o_addr). by move: Heqn => //=.
      clear Heqn; move: Htmp_addr. rewrite Haddreqn => Htmp; rewrite (proof_irrelevance _ Htmp Ho_addr); clear Htmp.
      clear tmp_addr Haddreqn => Ho_addr_is_active Ho_addr_stt _ _ _.
      (* now, let's simplify actor n is honest *)
      have Hoddr : (o_addr = Ordinal Ho_addr). by [].
      rewrite Ho_addr_is_active { 3}Hoddr ; clear Hoddr.
      rewrite /actor_n_is_honest_internal_unwrap; move: (erefl _); rewrite {2 3}Ho_addr => Htmp.
      rewrite (proof_irrelevance _ Htmp Ho_addr); clear Htmp.
      rewrite/actor_n_is_corrupt_internal_unwrap  tnth_set_nth_eq //= => Hncorrupt.
      (* Now, let's just rewrite our goal into a form better for applying the inductive hypothesis*)
      rewrite has_rcons -orb_assoc; apply/orP.
      move: Hsltrnd; rewrite leq_eqVlt =>/orP [ Hround_eq | Hnround_eq ]; right.
        (* if the current round is s then we can use the IHS to prove the stateemnt *)
        apply Hbase => //=.
        rewrite /actor_n_is_honest; move: (erefl _); rewrite {2 3}Ho_addr => Htmp.
        rewrite (proof_irrelevance _ Htmp Ho_addr); clear Htmp; rewrite /actor_n_is_corrupt.
        by rewrite Ho_addr_stt.
        (* if the current round is s then we have the requirements to prove this true*)
        clear Hbase.
        move: Hsvalid .
        move/eqP: Hround_eq => {1  3}<- Hprf.
        have: (Ordinal (n:=N_rounds) (m:=[[w'.state].#round]) Hprf) = [[w'.state].#round]. 
          by case: [[w'.state].#round] Hprf => //= t Ht Ht'; rewrite (proof_irrelevance _ Ht Ht').
        move=> ->; clear Hprf.
        apply/ (actor_n_has_chain_at_round_current w' xs (Ordinal Ho_addr)) => //=.
        by rewrite /actor_n_chain_length Ho_addr_stt.

      (* if the current round is less than s *)
      apply Hbase => //=.
      rewrite/actor_n_is_honest; move: (erefl _); rewrite {2 3}Ho_addr => Htmp.
      rewrite (proof_irrelevance _ Htmp Ho_addr); clear Htmp; rewrite /actor_n_is_corrupt.
      by rewrite Ho_addr_stt.
      apply actor_has_chain_length_ext with (sc:= xs) (s':= [[w'.state].#round]) => //=.
      apply/ (actor_n_has_chain_at_round_current w' xs (Ordinal Ho_addr)) => //=.
      by rewrite /actor_n_chain_length Ho_addr_stt.

    (* failed no update *)
      move=> Hbound Hhon.
      rewrite /actor_n_has_chain_length_ge_at_round_internal fixlist_insert_rewrite //=.
      rewrite has_rcons -orb_assoc => /orP [ | Hhas_base]; last first.
        (* inductive hypothesis case *)
        rewrite has_rcons -orb_assoc; apply/orP; right.
        apply Hbase => //=.
        move: Hhon; rewrite /actor_n_is_honest/actor_n_is_honest_internal_unwrap//=.
        move: (erefl _ ); rewrite {2 3 7}Ho_addr => //= Htmp.
        rewrite (proof_irrelevance _ Htmp Ho_addr); clear Htmp.
        rewrite /actor_n_is_corrupt/actor_n_is_corrupt_internal_unwrap//=.
        move: a_addr Ha_addr Ha_stt Ha_hl Htp Hmaxvld
        => [a_addr Ha_addr] Haddr_eqn.
        rewrite Haddr_eqn; move=> Ha_stt Ha_hl Htp Hmaxvld.
        case Haddreqn: (eq_op (Ordinal   Ho_addr) (Ordinal   Ha_addr)).
          by move/eqP: (Haddreqn) => ->; rewrite Ha_stt tnth_set_nth_eq //=.
          by rewrite tnth_set_nth_neq //=; move/negP/negP:Haddreqn.
      move=>/andP [HlenLt /andP [ Hsltrnd /eqP Haddr ]].
      (* let's get rid of a_addr *)
      move:  a_addr Haddr Ha_addr Ha_stt Ha_hl Htp Hmaxvld Hhon => [tmp_addr Htmp_addr] Heqn.
      have Haddreqn: (tmp_addr = o_addr). by move: Heqn => //=.
      clear Heqn; move: Htmp_addr. rewrite Haddreqn => Htmp; rewrite (proof_irrelevance _ Htmp Ho_addr); clear Htmp.
      clear tmp_addr Haddreqn => Ho_addr_is_active Ho_addr_stt _ _ _.
      (* now, let's simplify actor n is honest *)
      have Hoddr : (o_addr = Ordinal Ho_addr). by [].
      rewrite Ho_addr_is_active { 3}Hoddr ; clear Hoddr.
      rewrite /actor_n_is_honest_internal_unwrap; move: (erefl _); rewrite {2 3}Ho_addr => Htmp.
      rewrite (proof_irrelevance _ Htmp Ho_addr); clear Htmp.
      rewrite/actor_n_is_corrupt_internal_unwrap  tnth_set_nth_eq //= => Hncorrupt.
      (* Now, let's just rewrite our goal into a form better for applying the inductive hypothesis*)
      rewrite has_rcons -orb_assoc; apply/orP.
      move: Hsltrnd; rewrite leq_eqVlt =>/orP [ Hround_eq | Hnround_eq ]; right.
        (* if the current round is s then we can use the IHS to prove the stateemnt *)
        apply Hbase => //=.
        rewrite /actor_n_is_honest; move: (erefl _); rewrite {2 3}Ho_addr => Htmp.
        rewrite (proof_irrelevance _ Htmp Ho_addr); clear Htmp; rewrite /actor_n_is_corrupt.
        by rewrite Ho_addr_stt.
        (* if the current round is s then we have the requirements to prove this true*)
        clear Hbase.
        move: Hsvalid .
        move/eqP: Hround_eq => {1  3}<- Hprf.
        have: (Ordinal (n:=N_rounds) (m:=[[w'.state].#round]) Hprf) = [[w'.state].#round]. 
          by case: [[w'.state].#round] Hprf => //= t Ht Ht'; rewrite (proof_irrelevance _ Ht Ht').
        move=> ->; clear Hprf.
        apply/ (actor_n_has_chain_at_round_current w' xs (Ordinal Ho_addr)) => //=.
        by rewrite /actor_n_chain_length Ho_addr_stt.

      (* if the current round is less than s *)
      apply Hbase => //=.
      rewrite/actor_n_is_honest; move: (erefl _); rewrite {2 3}Ho_addr => Htmp.
      rewrite (proof_irrelevance _ Htmp Ho_addr); clear Htmp; rewrite /actor_n_is_corrupt.
      by rewrite Ho_addr_stt.
      apply actor_has_chain_length_ext with (sc:= xs) (s':= [[w'.state].#round]) => //=.
      apply/ (actor_n_has_chain_at_round_current w' xs (Ordinal Ho_addr)) => //=.
      by rewrite /actor_n_chain_length Ho_addr_stt.
   (* honest mint succeed case *)

    admit.
  (* adversary player mint case *)
    move=> IHw' Hprw' Hacthaschain Hhon  Hhash_pr .

    admit.
  (* adversary global mint case *)
    admit.

  (* adversary corrupt case *)
    move=> IHw' Hprw' Hacthaschain Hlast_hashed_round Haddr_to_index.
    move: o_addr IHw' => [o_addr Ho_addr] IHw'.
    rewrite /adversary_corrupt_step //=.
    rewrite !bounded_successful_round_internalP //=.
    rewrite !actor_n_is_honest_internalP //=.
    rewrite !actor_n_has_chain_length_ge_at_round_internalP //=.
    rewrite !no_bounded_successful_rounds_internalP //=.
    rewrite -!no_bounded_successful_rounds_internalP //=.
    rewrite -!actor_n_has_chain_length_ge_at_round_internalP //=.
    rewrite -!bounded_successful_round_internalP //=.
    move=> Hbound Hhon Hgtlen; apply/IHw' => //=.
    move: Hhon; rewrite /actor_n_is_honest/actor_n_is_honest_internal//=.
    move: (erefl _); rewrite {2 3 7}Ho_addr => Htmp;
    rewrite (proof_irrelevance _ Htmp Ho_addr) => //=; clear Htmp.
    rewrite /actor_n_is_corrupt_internal/actor_n_is_corrupt//=.
    move: addr0 Hlast_hashed_round => [a_addr Ha_addr] Hlast_hashed_round.
    case Heqn: (eq_op o_addr a_addr).
      by rewrite tnth_set_nth_eq.
      rewrite tnth_set_nth_neq => //=.
      by move/negP/negP: Heqn.
  (* round end case *)
    move: o_addr => [o_addr Ho_addr].
    move=> IHw' Hprw' Hroundend Hupd.
    rewrite /round_end_step //=.
    rewrite !bounded_successful_round_internalP //=.
    rewrite !actor_n_is_honest_internalP //=.
    try rewrite !actor_n_has_chain_length_ge_at_round_internalP //=.
    rewrite !no_bounded_successful_rounds_internalP //=.
    rewrite -!no_bounded_successful_rounds_internalP //=.
    rewrite -!actor_n_has_chain_length_ge_at_round_internalP //=.
    rewrite -!bounded_successful_round_internalP //=.
    move=> Hbound Hhon Hchl.
    apply IHw' => //=.
    move: Hhon; rewrite /actor_n_is_honest/actor_n_is_honest_internal//=.
    move: (erefl _); rewrite {2 3 7}Ho_addr => //= Htmp.
    rewrite (proof_irrelevance _ Htmp Ho_addr); clear Htmp.
    rewrite /actor_n_is_corrupt/actor_n_is_corrupt_internal//=.
    by move=>/deliver_messages_preserves_honest.
  (* adversary end case *)
    move: o_addr => [o_addr Ho_addr].
    move=> IHw' Hprw' Hactiv.
    rewrite /round_end_step //=.
    rewrite !bounded_successful_round_internalP //=.
    rewrite !actor_n_is_honest_internalP //=.
    rewrite !actor_n_has_chain_length_ge_at_round_internalP //=.
    rewrite !no_bounded_successful_rounds_internalP //=.
    rewrite -!no_bounded_successful_rounds_internalP //=.
    rewrite -!actor_n_has_chain_length_ge_at_round_internalP //=.
    rewrite -!bounded_successful_round_internalP //=.
    move=> Hbound Hhon Hchl.
    apply IHw' => //=.
    move: Hhon; rewrite /actor_n_is_honest/actor_n_is_honest_internal//=.
    move: (erefl _); rewrite {2 3 7}Ho_addr => //= Htmp.
    rewrite (proof_irrelevance _ Htmp Ho_addr); clear Htmp.
    rewrite /actor_n_is_corrupt/actor_n_is_corrupt_internal//=.
    by move=>/update_round_preserves_honest.

Admitted.





Lemma chain_growth_direct_weaken sc w l (r : 'I_N_rounds) s : forall Hsvddelta Hsvd,
    (* if the world is valid *) 
  (P[ world_step initWorld sc === Some w] <> 0) ->
    (* and round s was a bounded successful round*) 
  bounded_successful_round w (s - delta) ->
  (* and at round s - delta,
            every part actor has a chain longer than l + sum_{r .. s - 2 * delta + 1} *) 
  (forall o_addr : 'I_n_max_actors,
  actor_n_is_honest w o_addr ->
  actor_n_has_chain_length_ge_at_round w (l + no_bounded_successful_rounds w r (s.+1 - 2 * delta)) o_addr
    (Ordinal (n:=N_rounds) (m:=s - delta) Hsvddelta)) ->

  (*  then by round s.+1, every actor has a chain longer than l + sum_{r + s - 2 * delta + 1} + 1
      (as the only Xi in the range r to s - delta + 1, is the event at s - delta, thus plus 1
   *)
  (forall o_addr : 'I_n_max_actors,
  actor_n_is_honest w o_addr ->
  actor_n_has_chain_length_ge_at_round w (l + no_bounded_successful_rounds w r (s.+1 - 2 * delta ) + 1) o_addr
    (Ordinal (n:=N_rounds) (m:=s.+1) Hsvd)).
Proof.
  (* first let's simplify a bit *)
  move=> //= Hsdlta HSs Hpr Hbound Hall o_addr Hhon.
  move: (Hall o_addr Hhon).
  move: Hbound Hhon; clear Hall .
 (* now we have it in a nicer form:
    if a round is bounded successful (s - delta), and a node has a chain of length l + some value,
    at that round (s - delta0,
    then by round s.+1,  the node will have a chain length of at least l + some value + 1.
  *)
 apply /(@world_stepP
            (fun w _ =>

          bounded_successful_round w (s - delta) ->
          actor_n_is_honest w o_addr ->
          actor_n_has_chain_length_ge_at_round w (l + no_bounded_successful_rounds w r (s.+1 - 2 * delta))
            o_addr (Ordinal (n:=N_rounds) (m:=s - delta) Hsdlta) ->
          actor_n_has_chain_length_ge_at_round w
            (l + no_bounded_successful_rounds w r (s.+1 - 2 * delta) + 1) o_addr
            (Ordinal (n:=N_rounds) (m:=s.+1) HSs)
            ) sc w) => //= [ |
                          iscrpt  os  hash_value active_hash_link blc_rcd active_addr  active_state result
                          active_transaction_pool w'  xs  |
                          oracle_state  old_adv_state  blc_rcd nonce hash hash_res  w'  xs |
                          adv_state  w' xs |
                          addr0  actr  w'  xs |
                          msgs new_pool w' xs |
                          w'  xs ] //=.
  (* initial world case *)
    rewrite/initWorld  !bounded_successful_round_internalP //=;
    rewrite/BlockMap_new/bounded_successful_round_internal/unsuccessful_round_internal//= => /andP [_ ];
    rewrite/successful_round_internal/BlockMap_records/fixmap_empty//=.
    by move: (@fixlist_empty_is_empty  [eqType of Block * (bool * 'I_N_rounds)] BlockHistory_size);
    rewrite/fixlist_is_empty//= => /eqP-> //=. 

  (* honest mint case *)
    move: o_addr => [o_addr Ho_addr].
    move=> Hbase Hth_pr Hhonest_activation Hactive_state Ha_head_link Ha_txpool Hhash_pr Hbounded_success .
    move: Hbounded_success.

    move/Rlt_not_eq/nesym: Hth_pr => Hth_base.
    move: (world_step_adoption_history_top_heavy xs w' Hth_base) => Hfith.
    move:(world_step_adoption_history_overflow_safe xs w' Hth_base) => Hos.
    apply /(@honest_mint_stepP (fun w =>

  bounded_successful_round w (s - delta) ->
  actor_n_is_honest w (Ordinal (n:=n_max_actors) (m:=o_addr) Ho_addr) ->
  actor_n_has_chain_length_ge_at_round w 
    (l + no_bounded_successful_rounds w r (s.+1 - 2 * delta))
    (Ordinal (n:=n_max_actors) (m:=o_addr) Ho_addr)
    (Ordinal (n:=N_rounds) (m:=s - delta) Hsdlta) ->
  actor_n_has_chain_length_ge_at_round
    w 
    (l +
     no_bounded_successful_rounds w r (s.+1 - 2 * delta) + 1)
    (Ordinal (n:=n_max_actors) (m:=o_addr) Ho_addr)
    (Ordinal (n:=N_rounds) (m:=s.+1) HSs)
          ) w' iscrpt os hash_value active_hash_link
                               blc_rcd active_addr active_state
                               result active_transaction_pool) => //=;
    clear  Hhonest_activation Hactive_state Ha_head_link Ha_txpool iscrpt ;
    clear result os hash_value active_hash_link blc_rcd active_addr active_state Hhash_pr active_transaction_pool;
    move=> a_crpt a_addr  a_stt new_os a_block a_result a_hash_res a_hl a_tp;
    [ | move=> Hlt |  |  move=> Hlt |  | move=>Hlt ] => Ha_addr Ha_stt Ha_hl Htp Hhash_pr Hmaxvld;
    [  move=> Hlast | |    move=> Hlast |   | move=> Hlast | move=>Hlast  ]; 

    rewrite !actor_n_has_chain_length_ge_at_round_internalP //=;
    rewrite !actor_n_is_honest_internalP //=;
    rewrite !actor_n_is_honest_unwrapP //=;
    rewrite !bounded_successful_round_internalP//=;
    rewrite -!bounded_successful_round_internalP//=;
    rewrite !no_bounded_successful_rounds_internalP //=;
    rewrite -!no_bounded_successful_rounds_internalP //=;

    (* automatically dispose of any cases considering non actors *)
    try (by move: Hlast (a_addr) Ha_addr Ha_stt  => /eqP Hlast [a_addr' Ha_addr] //= Hfls;
    move:  Ha_addr (Ha_addr); rewrite -{1}Hfls Hlast -(addn1 n_max_actors)//=;
    move=>/ ltn_weaken; rewrite ltnn).

    (* Failed no update *)
      move=> Hbound.
      rewrite /actor_n_is_honest_internal_unwrap //=.
      move: (erefl _); rewrite {2 3}Ho_addr => Htmp; rewrite (proof_irrelevance _ Htmp Ho_addr).
      clear Htmp.
      rewrite /actor_n_is_corrupt_internal_unwrap //=.
      rewrite Ha_addr => Hhon (* to be dealt with later *).
      rewrite {1}/actor_n_has_chain_length_ge_at_round_internal fixlist_insert_rewrite //=.
      rewrite has_rcons -orb_assoc => /orP [ | Hhas]; last first.
        (* inductive hypothesis case *)
        rewrite {1}/actor_n_has_chain_length_ge_at_round_internal fixlist_insert_rewrite //=.
        rewrite has_rcons -orb_assoc; apply/orP; right.
        move: Hbase; rewrite /actor_n_has_chain_length_ge_at_round => IHw.
        apply IHw => //=.
        move: Hhon; rewrite /actor_n_is_honest; move: (erefl _); rewrite { 2 3 }Ho_addr => Htmp.
        rewrite (proof_irrelevance _ Htmp Ho_addr); clear Htmp; rewrite /actor_n_is_corrupt.
        case Ho_addr_eqn: (eq_op (Ordinal Ho_addr) a_addr).
        rewrite tnth_set_nth_eq //=.
        by move/eqP: (Ho_addr_eqn) => ->; rewrite Ha_stt.
        by rewrite tnth_set_nth_neq //=; move/negP/negP: Ho_addr_eqn => //=.
      move=>/andP [ Hlen /andP [Hround Haddr] ].
      rewrite /actor_n_has_chain_length_ge_at_round_internal //= fixlist_insert_rewrite //= has_rcons.

      move: Hhon; rewrite tnth_set_nth_eq //=; [ | by move/eqP:Haddr ->] => /negP/eqP Hncrpt.
      move: a_addr Haddr Ha_stt Ha_hl Htp Hhash_pr Hmaxvld Ha_addr => [a_addr Ha_addr] //= /eqP Heqn.
      move: Ha_addr; rewrite Heqn => //= Htmp; rewrite (proof_irrelevance _ Htmp Ho_addr); clear Htmp.
      clear a_addr Heqn.
      move=> Ha_stt Ha_hl Htp Hhash_pr Hmaxvld Ha_addr .
      move: Hlen; rewrite leq_eqVlt => /orP [/eqP Hleneq | ].
        rewrite -orb_assoc. apply/orP; right.
        move: Hbase; rewrite /actor_n_has_chain_length_ge_at_round Hleneq => IHw.
        apply IHw => //=.
          rewrite /actor_n_is_honest; move: (erefl _); rewrite { 2 3 }Ho_addr => Htmp.
          rewrite (proof_irrelevance _ Htmp Ho_addr); clear Htmp.
          by rewrite /actor_n_is_corrupt Ha_stt; move/eqP/negP: Hncrpt.
        move: (actor_n_has_chain_refl xs w' (Ordinal Ho_addr) Hth_base).
        rewrite /actor_n_has_chain_length_ge_at_round.
        move: (Hbound) => /(bounded_success_impl_exec xs w' ) => Hwexec'.
        move: (Hwexec' Hth_base) => Hwexec; clear Hwexec'.
        move: Hround Hwexec.
        rewrite /world_executed_to_round.
        by move=>/leq_ltn_trans H /H; rewrite ltnn.
      rewrite {1 2}addn1 => Hlen; apply/orP; left; apply/orP; left; apply/andP; split=>//=;[apply/andP;split => //=].
      by apply/(leq_trans Hround); rewrite -ltnS; apply /subn_ltn_pr.

   (* failed update casee *)
      move=> Hbound.
      rewrite /actor_n_is_honest_internal_unwrap //=.
      move: (erefl _); rewrite {2 3}Ho_addr => Htmp; rewrite (proof_irrelevance _ Htmp Ho_addr); clear Htmp.
      rewrite /actor_n_is_corrupt_internal_unwrap //= Ha_addr => Hhon (* to be dealt with later *).
      (* put in IHw here *)
      rewrite {1}/actor_n_has_chain_length_ge_at_round_internal fixlist_insert_rewrite //=.
      rewrite has_rcons -orb_assoc => /orP [ | Hhas]; last first.
        (* inductive hypothesis case *)
        rewrite {1}/actor_n_has_chain_length_ge_at_round_internal fixlist_insert_rewrite //=.
        rewrite has_rcons -orb_assoc; apply/orP; right.
        move: Hbase; rewrite /actor_n_has_chain_length_ge_at_round => IHw.
        apply IHw => //=.
        move: Hhon; rewrite /actor_n_is_honest; move: (erefl _); rewrite { 2 3 }Ho_addr => Htmp.
        rewrite (proof_irrelevance _ Htmp Ho_addr); clear Htmp; rewrite /actor_n_is_corrupt.
        case Ho_addr_eqn: (eq_op (Ordinal Ho_addr) a_addr).
        rewrite tnth_set_nth_eq //=.
        by move/eqP: (Ho_addr_eqn) => ->; rewrite Ha_stt.
        by rewrite tnth_set_nth_neq //=; move/negP/negP: Ho_addr_eqn => //=.
      move=>/andP [ Hlen /andP [Hround Haddr] ].
      rewrite /actor_n_has_chain_length_ge_at_round_internal //= fixlist_insert_rewrite //= has_rcons.

      move: Hhon; rewrite tnth_set_nth_eq //=; [ | by move/eqP:Haddr ->] => /negP/eqP Hncrpt.
      move: a_addr Haddr Ha_stt Ha_hl Htp Hhash_pr Hmaxvld Ha_addr => [a_addr Ha_addr] //= /eqP Heqn.
      move: Ha_addr; rewrite Heqn => //= Htmp; rewrite (proof_irrelevance _ Htmp Ho_addr); clear Htmp.
      clear a_addr Heqn.
      move=> Ha_stt Ha_hl Htp Hhash_pr Hmaxvld Ha_addr .
      move: Hlen; rewrite leq_eqVlt => /orP [/eqP Hleneq | ].
        rewrite -orb_assoc. apply/orP; right.
        move: Hbase; rewrite /actor_n_has_chain_length_ge_at_round Hleneq => IHw.
        apply IHw => //=.
          rewrite /actor_n_is_honest; move: (erefl _); rewrite { 2 3 }Ho_addr => Htmp.
          rewrite (proof_irrelevance _ Htmp Ho_addr); clear Htmp.
          by rewrite /actor_n_is_corrupt Ha_stt; move/eqP/negP: Hncrpt.
        move: (actor_n_has_chain_refl xs w' (Ordinal Ho_addr) Hth_base).
        rewrite /actor_n_has_chain_length_ge_at_round.
        move: (Hbound) => /(bounded_success_impl_exec xs w' ) => Hwexec'.
        move: (Hwexec' Hth_base) => Hwexec; clear Hwexec'.
        move: Hround Hwexec.
        rewrite /world_executed_to_round.
        by move=> /leq_ltn_trans H /H; rewrite ltnn.
      rewrite {1 2}addn1 => Hlen; apply/orP; left; apply/orP; left; apply/andP; split=>//=;[apply/andP;split => //=].
      by apply/(leq_trans Hround); rewrite -ltnS; apply /subn_ltn_pr.
    (* success case *)

      move=> Hbound.
      rewrite /actor_n_is_honest_internal_unwrap //=.
      move: (erefl _); rewrite {2 3}Ho_addr => Htmp; rewrite (proof_irrelevance _ Htmp Ho_addr).
      clear Htmp Htp Hhash_pr.
      move: Hbound.
      rewrite /honest_mint_succeed_update//=.
      case Hhon_max_valid: (honest_max_valid _) => [chain_pool Hchain_pool] //=.
      case Hupdated_chain: (fixlist_enqueue _ ) => [new_chain old_block] //=.
      rewrite !bounded_successful_round_internalP //=.
      rewrite !no_bounded_successful_rounds_internalP //= => Hbound_succ Hcorrupt.
      move: (Hbound_succ).
      rewrite /bounded_successful_round_internal => /andP [ ].
      rewrite/unsuccessful_round_internal/successful_round_internal //= => [].
      move=> /allP Hall .
      rewrite -length_sizeP /BlockMap_records size_filter -has_count fixlist_insert_rewrite //= .
      move=>/hasP [ [ block_iscrpt block_round] Heqn /andP [Heq_round Hcrpt]].
      rewrite /no_bounded_successful_rounds_internal.
      move: Heqn; rewrite map_rcons //= -cats1 mem_cat => /orP [ | //=]; last first.
      (* because we just inserted a block, there are 2 cases - either
          - when there was a previous round which was bounded successful
          - when the current round is s - delta
        *)
      (* when the current round is s - delta *)
        rewrite /mem //= /in_mem //= => /orP [] //= .
        move=>/eqP [/negP/negP Hflse Hround].
        rewrite Hround in Heq_round.
        rewrite {1}/actor_n_has_chain_length_ge_at_round_internal fixlist_insert_rewrite //= has_rcons => /orP [].
        admit.
        admit.
        admit.
        admit.
        admit.

  (* adversary player mint case *)
    move=> IHw' Hprw' Hadv Hupd Hhash_pr .
    rewrite /adversary_mint_player_step.
    rewrite !bounded_successful_round_internalP !actor_n_is_honest_internalP.
    rewrite !actor_n_has_chain_length_ge_at_round_internalP !no_bounded_successful_rounds_internalP //=.
    rewrite !actor_n_is_honest_unwrapP //= .
    case Hdiff : (hash_res < T_Hashing_Difficulty)%nat ; last first.
      by case: (isSome _) => //=.
    case: (isSome _) => //= Hbs;
    rewrite -!actor_n_is_honest_unwrapP -!actor_n_is_honest_internalP //= => Hhon.
    admit. admit.
  (* adversary global mint case *)
    move: adv_state => [[adv_state os] oblock].
    move=> IHw' Hprw' Hadv Hupd Hhash_pr Hattempt.
    rewrite /adversary_mint_global_step.
    rewrite !bounded_successful_round_internalP !actor_n_is_honest_internalP.
    rewrite !actor_n_has_chain_length_ge_at_round_internalP !no_bounded_successful_rounds_internalP //=.
    rewrite !actor_n_is_honest_unwrapP //= .
    case: oblock Hattempt => //= block Hattmept.

    admit.
  (* adversary corrupt case*)
    move=> IHw' Hprw' Hacthaschain Hlast_hashed_round Haddr_to_index.
    move=> Hbound  Hhon .
    move: o_addr Hhon IHw' => [o_addr Ho_addr] Hhon IHw'; move: Hhon.
    rewrite /actor_n_is_honest.
    move: (erefl _).
    rewrite {2 3}Ho_addr => //= Htemp. rewrite (proof_irrelevance _ Htemp Ho_addr); clear Htemp.
    rewrite {1}/adversary_corrupt_step/actor_n_is_corrupt//=.
    case Hcorrupt_addr: (eq_op ( Ordinal (n:=n_max_actors) (m:=o_addr) Ho_addr) addr0).
      by rewrite tnth_set_nth_eq //=.
    move/negP/negP: Hcorrupt_addr => Hcorrupt_addr.
    rewrite tnth_set_nth_neq //= => Hnotcorrupt.
    rewrite /adversary_corrupt_step//=.
    rewrite !actor_n_has_chain_length_ge_at_round_internalP //=.
    rewrite !no_bounded_successful_rounds_internalP//=.
    rewrite -!actor_n_has_chain_length_ge_at_round_internalP //=.
    rewrite -!no_bounded_successful_rounds_internalP//= => Hchain_ge.
    apply IHw' => //=.
    move: Hnotcorrupt; rewrite /actor_n_is_honest/actor_n_is_corrupt//=; move: (erefl _).
    by rewrite {2 3}Ho_addr => prf; rewrite (proof_irrelevance _ prf Ho_addr).
  (* round end case*)
    move=> IHw' Hprw Hrndend Hupd .
    move: o_addr IHw' => [o_addr Ho_addr] IHw'.
    rewrite /round_end_step//=.
    rewrite !bounded_successful_round_internalP//=.
    rewrite -!bounded_successful_round_internalP //= => /IHw' IHw; clear IHw'.
    rewrite !actor_n_is_honest_internalP //= => Hhon.
    rewrite !actor_n_has_chain_length_ge_at_round_internalP//=.
    rewrite !no_bounded_successful_rounds_internalP //=.
    rewrite -!actor_n_has_chain_length_ge_at_round_internalP//=.
    rewrite -!no_bounded_successful_rounds_internalP //= => Hact_has_chain.
    apply IHw => //=.
    move: Hhon; rewrite /actor_n_is_honest/actor_n_is_honest_internal/actor_n_is_corrupt.
    rewrite/actor_n_is_corrupt_internal//=.
    move: (erefl _) => //=.
    rewrite {2 3 7}Ho_addr => //= Htmp; rewrite (proof_irrelevance _ Htmp Ho_addr); clear Htmp.
    by move=>/deliver_messages_preserves_honest.
  (* adversary end case*)
    move=> IHw' Hprw Hadvact.
    rewrite /adversary_end_step//=.
    rewrite bounded_successful_round_internalP//= -bounded_successful_round_internalP //=.
    move=> /IHw' IHw; clear IHw'.
    rewrite !actor_n_is_honest_internalP //= => Hhon;
    rewrite !actor_n_has_chain_length_ge_at_round_internalP//=;
    rewrite !no_bounded_successful_rounds_internalP //=;
    rewrite -!actor_n_has_chain_length_ge_at_round_internalP//= => Hact_has_chain.
    apply IHw => //=.
    move: Hhon; rewrite /actor_n_is_honest/actor_n_is_honest_internal.
    clear Hact_has_chain IHw.
    move: o_addr => [o_addr Ho_addr] => //=.
    move: (erefl _) => //=; rewrite {2 3 7}Ho_addr => Htmp.
    rewrite /actor_n_is_corrupt_internal/actor_n_is_corrupt //=.
    by move=>/update_round_preserves_honest.
  (* TODO: Complete this proof *)
Admitted.


(*
  if round s - delta is bounded successful, then ~~ Xi for i in (s - 2 * delta,....s - delta - 1),
  thus 
      no_bounded_successful_rounds w r (s - delta) =
      no_bounded_successful_rounds w r (s - 2 * delta + 1) + 1.
 *)
Lemma bounded_successful_exclusion sc w r s (l: nat) :
  (r <= s - delta)%nat ->
  (delta <= s)%nat ->
  P[ world_step initWorld sc === Some w] <> 0 ->
  bounded_successful_round w (s - delta) ->
                (l + no_bounded_successful_rounds w r (s.+1 - delta))%nat =
                (l + no_bounded_successful_rounds w r (s.+1 - 2 * delta) + 1)%nat.
Proof.
  move=> Hrsdlta Hdlta Hpr Hbnd.
  rewrite no_bounded_successful_rounds_lim //= .
  by rewrite mulnC addnA.
  exact delta_valid.
  (* now we just need to prove that number of bounded successful rounds is always less than N_rounds.+1 *)
  rewrite /no_bounded_successful_rounds'/bounded_successful_round/unsuccessful_round.
  (* TODO(Kiran): Complete this proof *)
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



(* ==================================================

                     Main Theorem

 ====================================================*)
Theorem prob_chain_growth : forall sc,
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
  by rewrite /Dist1.f Hzr //= mul0R  . (* if the world being tested is the initial world... *)
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
  apply/implyP => /andP [/eqP Heqr /eqP Heql]; apply/forallP => [[s Hsvld]].
  apply/implyP.
  by rewrite Heqr //= add0n => Htn0; apply/implyP => Hwexec.
  (* move: (@fixlist_empty_is_empty [eqType of BlockChain * 'I_N_rounds * 'I_n_max_actors] (n_max_actors * N_rounds)%nat). *)
  (* rewrite /fixlist_is_empty/world_executed_to_round/initWorld/initWorldAdoptionHistory//= => /eqP -> //=. *)


  


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
  apply/implyP=>//=Hs'.
  apply/implyP=>H_world_exec.
  apply/forallP=> o_addr.
  apply/implyP=> H_is_honest.

  (* now can be proven in terms of simple logical operations! *) 
  (* now for the main part of the proof *)
  (* use the following tactics at this point in the proof to see the prop formulation of the chain growth lemma *)
  (* move: r c addr H_holds_chain s Hvr o_addr H_is_honest Hwround . *)
  move:    Hs' H_valid_range H_world_exec o_addr H_is_honest .
  destruct s as [s Hsvalid]; destruct r as [r Hrvalid] => //= Hs'.
  induction s ; rewrite leq_eqVlt => /orP; case => //=.
  (* Our induction on s given (s - r - delta + 1 >= 0) has 4 cases
     1. when s is 0, thus (r - delta + 1 == 0) (simple base case)
     1. when s is 0, thus (r - delta + 1 < 0) (simple base case)
     2. when s is s'.+1, and r - delta + 1 == s'.+1 (proven simply by the fact that messages are delivered in delta rounds)
     3. when s is s'.+1 and r - delta + 1 < s'.+1   (the true inductive case) *)
  (* simple base case - r - delta + 1 == 0*)
  case r => //=; rewrite {1}add0n =>/eqP Hdlta; move: delta_valid.
  by  rewrite Hdlta ltnn.
  move=> Hrdelta_eqs; move: (Hrdelta_eqs).
  move=>/eqP {2}<-.
  rewrite -addnBA //= subnn addn0 //= .
  rewrite no_bounded_successful_rounds_eq0 //=. rewrite addn0 => Hwexec.
  move: Hrdelta_eqs.



  suff Hexist: (exists (addr0 : 'I_n_max_actors) (k : 'I_N_rounds),
                   (k <= (Ordinal Hrvalid))%nat && actor_n_has_chain_length_at_round w l addr0 k).

  move=>  Hrdelta_eq1  o_addr Haddr_hon.
  
  apply/(chain_growth_weak (x::xs) w l (Ordinal Hrvalid) Hpr_valid Hexist (Ordinal Hsvalid)) => //=.
  exists addr.
  exists (Ordinal Hrvalid).
  apply/andP;split => //=.
  by right.
  (* true inductive case *)
  move: (Hsvalid)  =>Hsvd.
  move: Hsvalid. rewrite -{1}(addn1 s); move=>/(addr_ltn s 1%nat N_rounds); move=> Hs'valid.
  move=> Hsvald.
  move: (Hsvald).
  rewrite (addnC r) => /leq_addr_weaken Hdlts.
  rewrite subSn //=.

   
  (* As in the bitcoin backbone proof, we consider 2 cases - one when Xi' = 0, and one when not *)
  case Hbsuc: (bounded_successful_round w (s - delta));last first.
  move/negP/negP:Hbsuc=>Hbsuc.

  move=> Hwexec o_addr Hhon.
  rewrite -(no_bounded_successful_rounds_ext (x :: xs) w r (s - delta)) => //= .
  apply:(actor_has_chain_length_ext (x::xs) w (l + no_bounded_successful_rounds w r (s - delta))  o_addr (Ordinal Hs'valid)  (Ordinal (n:=N_rounds) (m:=s.+1) Hsvd)) => //=.

  (* if X'i is false, then the induction hypothesis is enough to prove the statement*)
  apply: (IHs Hs'valid) => //=.
    by move: Hs'; rewrite addSn -{1}(addn1 (_ + _)%nat) => /(ltn_weaken).
  apply: (@world_executed_to_weaken (x::xs) w s.+1 Hsvd ) => //=.
    by move: Hs'; rewrite addSn -{1}(addn1 (_ + _)%nat) => /(ltn_weaken); rewrite addn2.




(* (bounded_successful_round w (s - delta) ->
     (no_bounded_successful_rounds r (s - delta).+1 = no_bounded_successful_rounds r (s - 2 * delta + 1).+1 *)
  move=> Hwexec.
  rewrite -subSn //=.
  rewrite (bounded_successful_exclusion (x::xs) w r s l ) //=.
  apply: (@chain_growth_direct_weaken (x::xs) w l (Ordinal Hrvalid) s) => //=.
  by rewrite subn_ltn_pr.
  move=> Hdelta.
  apply: (@chain_growth_implicit_weaken (x :: xs) w l (Ordinal Hrvalid) s Hs'valid Hdelta Hpr_valid Hbsuc).
  move=> [o_addr Ho_addr] Hhon.
  move: Hs'; rewrite addSn -{1}(addn1 (_ + _)%nat) => /(ltn_weaken) Hltss.
  apply: (@IHs Hs'valid Hltss Hsvald) => //=.
  apply: (world_executed_to_weaken (x :: xs) w s.+1 Hsvd ) => //=.
  by move: Hltss; rewrite addn2.
  move: Hsvald.
  by rewrite addnC -ltn_subRL subSn //=.
Qed.

  (* now to prove the full inductive step *)
  (* if X'(s - delta) is true, *)
  (* then forall  in s - 2 delta,  to s - delta - 1, X'i = 0 *)

  (* this means that
      no_bounded_successful_rounds r (s - delta - 1) =
      no_bounded_successful_rounds r (s - 2 * delta) *)

  (* by inductive hypothesis,
       every actor has a chain of length at least l' by round s - delta ,
        l' = l + no_bounded_successful_rounds r (s - 2 * delta) *)

  (* thus every actor queried the oracle  with a chain of length l' at round delta *)

  (* thus every successful actor at s - delta, must have had a chain of at least l + delta *)

  (* thus by round s  every actor has a chain of length at least l' + 1,*)

  (* l' + 1 = l + no_bounded_successful_rounds r (s - 2 * delta) + 1 = l + no_bounded_successful_rounds r (s.+1 - delta) *)

  (* qed *)











