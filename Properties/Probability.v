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

Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.ProofIrrelevance.
Require Import Coq.Program.Equality.

Set Implicit Arguments.

Variable probability_constant : R.

Lemma addr_ltn a b c:
   (a + b < c)%nat -> (a < c)%nat.
Proof.
    by move=>/(ltn_addr b); rewrite ltn_add2r.
Qed.
Lemma negb_eqn b: b != true -> eq_op b false.
Proof.
  by case b.
Qed.



Lemma ltn1 n : (n < 1)%nat = (n == 0%nat)%bool.
Proof.
  by elim n.
Qed.


Lemma Rleq_eqVlt : forall m n : R, (m <= n) <-> (m = n) \/ (m < n).
Proof.
  split.
  move=>/Rle_lt_or_eq_dec.
  by case=> H; [right|left].
  by case=> [/Req_le | /Rlt_le].
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




Lemma addr2n r : (r - 2 < r)%nat \/ (r == (r - 2%nat)%nat)%bool /\ (r == 0%nat)%bool.
Proof.
  elim r=> //.
  by right; rewrite sub0n.
  move=> n [IHn|IHn].
  case (n > 1)%nat eqn: H.
  by left; rewrite subSn; [rewrite -(addn1 (n - 2%nat)) -(addn1 n) ltn_add2r| ].
  move/negP/negP: H.
  rewrite -leqNgt leq_eqVlt.
  by move=>/orP[/eqP -> | ]; [left; rewrite subnn | rewrite ltn1; move=>/eqP ->; left].
  by destruct IHn as [_ Heq0]; move/eqP:Heq0 -> ; left.
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

(* Subtracts a value from an ordinal value returning another value in the ordinal range *)
Definition ordinal_sub {max : nat} (value : 'I_max) (suband : nat) : 'I_max :=
  ssr_have (value - suband < max)%nat
  match value as o return (o - suband < max)%nat with
  | @Ordinal _ m i =>
      (Hpft <- is_true_true;
       (fun Hpf : (Ordinal (n:=max) (m:=m) i < max)%nat =>
        eq_ind_r [eta is_true] Hpft (subn_ltn_pr (Ordinal (n:=max) (m:=m) i) suband max Hpf))) i
  end [eta Ordinal (n:=max) (m:=value - suband)]
.



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
  rewrite /tnth/ncons/ssrnat.iter//=. move: m Hm.
  elim n_max_actors => //=.
  move=> n IHn m .
  case m => //=.
Qed.



Notation "'P[' a '===' b ']'" := (evalDist a b).
Notation "'P[' a ']'" := (evalDist a true).
Notation "'E[' a ']'" := (expected_value a).
Notation " a '|>' b " := (w_a <-$ a; b w_a) (at level 50).
Notation " w '>>=' a '<&&>' b " := (fun w => ret (a  && b )) (at level 49).
Notation " w '>>=' a '<||>' b " := (fun w => ret (a  || b )) (at level 49).


Lemma add_lt0 x y: (0 < x + y)%nat = ((0 <x)%nat && (0 <= y)%nat) || ((0 <=x)%nat && (0 < y)%nat).
Proof.
    by induction x => //=.
  Qed.


Lemma addRA_rsum  (A : finType) f g : 
  \rsum_(i in A) (f i + g i)%R = (\rsum_(i in A) f i + \rsum_(i in A) g i)%R .
Proof.
  rewrite unlock.
  elim index_enum => //=.
  have H : R0 = 0. (* there's some issues with the types 0 doesn't want to auto-coerce  to R0 *)
    by [].
  move: (addR0   ).
  rewrite /right_id => H'.
  move: (H' R0).
  by rewrite H. 
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

Lemma gtRP (a b : R) : reflect (a > b) (a >b b).
Proof. by rewrite /gtRb /ltRb; apply: (iffP idP); [case Hrlta: (Rlt_dec b a) | case (Rlt_dec b a) ]. Qed.

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

Definition world_executed_to_max_round w :=
  foldl (fun acc x =>
           let: (rec_chain, rec_round, rec_actr) := x in
           max (nat_of_ord rec_round) acc) 0%nat (fixlist_unwrap (world_adoption_history w)).


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


Lemma foldl_rcons (T R : Type) (f : R -> T -> R) (b : R) (x : T) (xs : seq.seq T) : foldl f b (rcons xs x ) = f (foldl f b xs ) x. 
Proof.
  by rewrite -cats1 foldl_cat => //=.
Qed.

 


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
  destruct H as [Heqrs Heq0].
  move/eqP: Heqrs=> <-.
  move/eqP: Heq0=> -> //=.
  suff Hgeq: [eta Ordinal (n:=N_rounds) (m:=0)] = (fun x => Ordinal (n:=N_rounds) (m:=0) valid_N_rounds).
  rewrite Hgeq.
  rewrite valid_N_rounds => //=.
 apply: functional_extensionality=> G.
  by rewrite (proof_irrelevance _ valid_N_rounds G).
Qed. 

Lemma actor_has_chain_length_generalize  w l o_addr s :
  actor_n_has_chain_length_at_round w l o_addr s ->
  actor_n_has_chain_length_ge_at_round w l o_addr s.
Proof.
  have blt0 (x:bool) : (x > 0)%nat = x. by case x.
  rewrite /actor_n_has_chain_length_ge_at_round/actor_n_has_chain_length_at_round !has_count.
  elim (fixlist_unwrap _) => //= [[[c r] addr] xs] IHn.
  rewrite add_lt0; move=>/orP; case => //=.
  by rewrite blt0; move=>/andP; case; [move=>/andP [/eqP -> /andP [/eqP -> /eqP ->]]] => _; rewrite !leqnn eq_refl.
  move=>/IHn Hbase.
  by rewrite add_lt0; apply/orP; right.
Qed.  



Lemma  actor_has_chain_length_weaken w l o_addr s l':
  (l' <= l)%nat ->
  actor_n_has_chain_length_ge_at_round w l o_addr s ->  
  actor_n_has_chain_length_ge_at_round w l' o_addr s.
Proof.
  rewrite /actor_n_has_chain_length_ge_at_round !has_count.
  rewrite leq_eqVlt; move=>/orP[/eqP -> |] //=.
  move=>  Hvalid.  
  induction (fixlist_unwrap _) => //=.
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


Lemma  Rmult_integralP   r1 r2 :  (r1 * r2)%R <> 0%R -> r1 <> 0%R /\ r2 <> 0%R .
Proof.
  case Hr1eq0: (eq_op r1 0).
    by move/eqP: Hr1eq0 => ->; rewrite (Rmult_0_l r2) .
  case Hr2eq0: (eq_op r2 0).
    by move/eqP: Hr2eq0 => ->; rewrite (Rmult_0_r r1) .
  by move/eqP: Hr1eq0 => Hr1neq; move/eqP: Hr2eq0 => Hr2neq.
Qed.

(* Notation "A '-::>' '(' B ')' '{' C '}'" := (fixlist_insert (Tuple (n:=B) (tval:=C) _) A) (at level 50). *)
(* Notation "'`I_{' A '}' '=' B '(' C ')'" := (@Ordinal A B C). *)



Definition hash_step (w w' : World) lclstt addr result blk_rcd hash_val hash_value (os : OracleState) :=
if (result < T_Hashing_Difficulty)%nat
   then
    let
    '(new_chain, _) :=
     fixlist_enqueue (Some {| block_nonce := hash_value; block_link := hash_val; block_records := blk_rcd |})
       (honest_max_valid (update_transaction_pool addr lclstt (world_transaction_pool w')) (world_hash w')) in
     ({|
      honest_current_chain := new_chain;
      honest_local_transaction_pool := fixlist_empty Transaction Honest_TransactionPool_size;
      honest_local_message_pool := fixlist_empty [eqType of BlockChain] Honest_MessagePool_size |},
     Some (BroadcastMsg new_chain), os,
     Some {| block_nonce := hash_value; block_link := hash_val; block_records := blk_rcd |}, 
     Some new_chain)
   else
    if
     honest_max_valid (update_transaction_pool addr lclstt (world_transaction_pool w')) (world_hash w') ==
     honest_current_chain (update_transaction_pool addr lclstt (world_transaction_pool w'))
    then
     ({|
      honest_current_chain := honest_current_chain
                                (update_transaction_pool addr lclstt (world_transaction_pool w'));
      honest_local_transaction_pool := fixlist_empty Transaction Honest_TransactionPool_size;
      honest_local_message_pool := fixlist_empty [eqType of BlockChain] Honest_MessagePool_size |}, None, os, None,
     None)
    else
     ({|
      honest_current_chain := honest_max_valid (update_transaction_pool addr lclstt (world_transaction_pool w'))
                                (world_hash w');
      honest_local_transaction_pool := fixlist_empty Transaction Honest_TransactionPool_size;
      honest_local_message_pool := fixlist_empty [eqType of BlockChain] Honest_MessagePool_size |},
     Some
       (BroadcastMsg
          (honest_max_valid (update_transaction_pool addr lclstt (world_transaction_pool w')) (world_hash w'))),
     os, None, None).



Definition honest_step_world  (w w' : World) lclstt iscrpt addr result blk_rcd hash_val hash_value (os : OracleState) :=
(let
   '(updated_actor, new_message, new_oracle, new_block, new_chain) :=
    hash_step w w' lclstt addr result blk_rcd hash_val hash_value os in
    {|
    world_global_state := (if (eq_op (nat_of_ord (global_currently_active (world_global_state w'))) n_max_actors.+1)%nat as b0
                            return
                              ((eq_op (nat_of_ord (global_currently_active (world_global_state w'))) n_max_actors.+1) = b0 ->
                               GlobalState)
                           then
                            fun _ : (eq_op (nat_of_ord (global_currently_active (world_global_state w'))) n_max_actors.+1) = true =>
                            {|
                            global_local_states := set_tnth (global_local_states (world_global_state w'))
                                                     (updated_actor, iscrpt)
                                                     (global_currently_active (world_global_state w'));
                            global_adversary := global_adversary (world_global_state w');
                            global_currently_active := global_currently_active (world_global_state w');
                            global_current_round := global_current_round (world_global_state w') |}
                           else
                            fun prf : (eq_op (nat_of_ord (global_currently_active (world_global_state w'))) n_max_actors.+1) = false
                            =>
                            ssr_suff ((nat_of_ord (global_currently_active (world_global_state w'))).+1 < n_max_actors + 2)%nat
                              (fun H' : ((global_currently_active (world_global_state w')).+1 < n_max_actors + 2)%nat
                               =>
                               {|
                               global_local_states := set_tnth (global_local_states (world_global_state w'))
                                                        (updated_actor, iscrpt)
                                                        (global_currently_active (world_global_state w'));
                               global_adversary := global_adversary (world_global_state w');
                               global_currently_active := Ordinal (n:=n_max_actors + 2)
                                                            (m:=(global_currently_active (world_global_state w')).+1)
                                                            H';
                               global_current_round := global_current_round (world_global_state w') |})
                              (round_in_range (global_currently_active (world_global_state w'))
                                 (introN eqP (elimTF eqP prf))))
                            (erefl (eq_op (nat_of_ord (global_currently_active (world_global_state w'))) n_max_actors.+1));
    world_transaction_pool := world_transaction_pool w';
    world_inflight_pool := option_insert (world_inflight_pool w') new_message;
    world_message_pool := world_message_pool w';
    world_hash := new_oracle;
    world_block_history := BlockMap_put_honest_on_success new_block (global_current_round (world_global_state w'))
                             (world_block_history w');
    world_chain_history := option_insert (world_chain_history w') new_chain;
    world_adversary_message_quota := world_adversary_message_quota w';
    world_adversary_transaction_quota := world_adversary_transaction_quota w';
    world_honest_transaction_quota := world_honest_transaction_quota w';
    world_adoption_history := record_actor_current_chain (honest_current_chain lclstt) new_chain
                                (global_current_round (world_global_state w')) addr (world_adoption_history w') |}).




(* contains some common simplifications used repeatedly in most proofs *)
Lemma world_step_honest_mint_simplify x w w' :
  x = HonestMintBlock ->
  0 < P[ world_step_internal w' x === Some w] ->

  exists lclstt iscrpt addr result blk_rcd hash_val hash_value os,
  w = honest_step_world w w' lclstt iscrpt addr result blk_rcd hash_val hash_value os.
Proof.

  move=> -> //=.
  rewrite /evalDist //=.
        case: (honest_activation _ ) => [addr|]; last first.
          by rewrite /evalDist//=; rewrite /Dist1.f //= => /(Rlt_irrefl 0).
        case: (tnth _ ) => lclstt iscrpt .
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
      case: (retrieve_head_link _) => [hash_val|//=];last first.
      case: (find_maximal_valid_subset _) => blk_rcd ltp //=.
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
      exists lclstt.
      exists iscrpt.
      exists addr.
      exists result.
      exists blk_rcd.
      exists hash_val.
      exists hash_value.
      exists os.
      by exact Hhonest_step.
Qed.


Definition transaction_gen_step w' tx  := {|
    world_global_state := world_global_state w';
    world_transaction_pool := fixlist_insert (world_transaction_pool w') (BroadcastTransaction tx);
    world_inflight_pool := world_inflight_pool w';
    world_message_pool := world_message_pool w';
    world_hash := world_hash w';
    world_block_history := world_block_history w';
    world_chain_history := world_chain_history w';
    world_adversary_message_quota := world_adversary_message_quota w';
    world_adversary_transaction_quota := world_adversary_transaction_quota w';
    world_honest_transaction_quota := mod_incr Honest_max_Transaction_sends valid_Honest_max_Transaction_sends
                                        (world_honest_transaction_quota w');
    world_adoption_history := world_adoption_history w'
  |}.


Definition transaction_drop_step w' rem_ind:= {|
    world_global_state := world_global_state w';
    world_transaction_pool := fixlist_remove (world_transaction_pool w') rem_ind;
    world_inflight_pool := world_inflight_pool w';
    world_message_pool := world_message_pool w';
    world_hash := world_hash w';
    world_block_history := world_block_history w';
    world_chain_history := world_chain_history w';
    world_adversary_message_quota := world_adversary_message_quota w';
    world_adversary_transaction_quota := world_adversary_transaction_quota w';
    world_honest_transaction_quota := world_honest_transaction_quota w';
    world_adoption_history := world_adoption_history w' |}.

Definition honest_mint_step iscrpt os hash_value hash_vl blc_rcd addr lclstt result w' :=
(let
     '(updated_actor, new_message, new_oracle, new_block, new_chain) :=
      if (result < T_Hashing_Difficulty)%nat
      then
       let
       '(new_chain, _) :=
        fixlist_enqueue (Some {| block_nonce := hash_value; block_link := hash_vl; block_records := blc_rcd |})
          (honest_max_valid (update_transaction_pool addr lclstt (world_transaction_pool w')) (world_hash w')) in
        ({|
         honest_current_chain := new_chain;
         honest_local_transaction_pool := fixlist_empty Transaction Honest_TransactionPool_size;
         honest_local_message_pool := fixlist_empty [eqType of BlockChain] Honest_MessagePool_size |},
        Some (BroadcastMsg new_chain), os,
        Some {| block_nonce := hash_value; block_link := hash_vl; block_records := blc_rcd |}, 
        Some new_chain)
      else
       if
        honest_max_valid (update_transaction_pool addr lclstt (world_transaction_pool w')) (world_hash w') ==
        honest_current_chain (update_transaction_pool addr lclstt (world_transaction_pool w'))
       then
        ({|
         honest_current_chain := honest_current_chain
                                   (update_transaction_pool addr lclstt (world_transaction_pool w'));
         honest_local_transaction_pool := fixlist_empty Transaction Honest_TransactionPool_size;
         honest_local_message_pool := fixlist_empty [eqType of BlockChain] Honest_MessagePool_size |}, None, os,
        None, None)
       else
        ({|
         honest_current_chain := honest_max_valid (update_transaction_pool addr lclstt (world_transaction_pool w'))
                                   (world_hash w');
         honest_local_transaction_pool := fixlist_empty Transaction Honest_TransactionPool_size;
         honest_local_message_pool := fixlist_empty [eqType of BlockChain] Honest_MessagePool_size |},
        Some
          (BroadcastMsg
             (honest_max_valid (update_transaction_pool addr lclstt (world_transaction_pool w')) (world_hash w'))),
        os, None, None) in
      {|
      world_global_state := (if eq_op (nat_of_ord (global_currently_active (world_global_state w'))) n_max_actors.+1 as b0
                              return
                                ((eq_op (nat_of_ord((global_currently_active (world_global_state w')))) n_max_actors.+1) = b0 ->
                                 GlobalState)
                             then
                              fun _ : (eq_op (nat_of_ord (global_currently_active (world_global_state w'))) n_max_actors.+1) = true
                              =>
                              {|
                              global_local_states := set_tnth (global_local_states (world_global_state w'))
                                                       (updated_actor, iscrpt)
                                                       (global_currently_active (world_global_state w'));
                              global_adversary := global_adversary (world_global_state w');
                              global_currently_active := global_currently_active (world_global_state w');
                              global_current_round := global_current_round (world_global_state w') |}
                             else
                              fun
                                prf : (eq_op (nat_of_ord(global_currently_active (world_global_state w'))) n_max_actors.+1) = false
                              =>
                              ssr_suff ((global_currently_active (world_global_state w')).+1 < n_max_actors + 2)%nat
                                (fun
                                   H' : ((global_currently_active (world_global_state w')).+1 < n_max_actors + 2)%nat
                                 =>
                                 {|
                                 global_local_states := set_tnth (global_local_states (world_global_state w'))
                                                          (updated_actor, iscrpt)
                                                          (global_currently_active (world_global_state w'));
                                 global_adversary := global_adversary (world_global_state w');
                                 global_currently_active := Ordinal (n:=n_max_actors + 2)
                                                              (m:=(global_currently_active (world_global_state w')).+1)
                                                              H';
                                 global_current_round := global_current_round (world_global_state w') |})
                                (round_in_range (global_currently_active (world_global_state w'))
                                   (introN eqP (elimTF eqP prf))))
                              (erefl (eq_op (nat_of_ord (global_currently_active (world_global_state w'))) n_max_actors.+1));
      world_transaction_pool := world_transaction_pool w';
      world_inflight_pool := option_insert (world_inflight_pool w') new_message;
      world_message_pool := world_message_pool w';
      world_hash := new_oracle;
      world_block_history := BlockMap_put_honest_on_success new_block
                               (global_current_round (world_global_state w')) (world_block_history w');
      world_chain_history := option_insert (world_chain_history w') new_chain;
      world_adversary_message_quota := world_adversary_message_quota w';
      world_adversary_transaction_quota := world_adversary_transaction_quota w';
      world_honest_transaction_quota := world_honest_transaction_quota w';
      world_adoption_history := record_actor_current_chain (honest_current_chain lclstt) new_chain
                                  (global_current_round (world_global_state w')) addr (world_adoption_history w') |}).


Definition update_adversary_state w':=
  finfun.FunFinfun.fun_of_fin
                 (finfun.FunFinfun.fun_of_fin
                    (adversary_generate_block
                       (update_adversary_transaction_pool (global_adversary (world_global_state w'))
                          (world_transaction_pool w')))
                    (adversary_state
                       (update_adversary_transaction_pool (global_adversary (world_global_state w'))
                          (world_transaction_pool w')))) (world_inflight_pool w').

Definition adversary_mint_player_step
                 (oracle_state : oraclestate_finType) (old_adv_state : adversary_internal_state)
                 (blc_rcd : BlockRecord) (nonce hash:  'I_Hash_value.+1) (hash_res: Hashed) w' :=
    (let
     '(new_adversary, new_oracle, new_block) :=
      if (hash_res < T_Hashing_Difficulty)%nat
      then
       ({|
        adversary_state := finfun.FunFinfun.fun_of_fin
                             (finfun.FunFinfun.fun_of_fin
                                (finfun.FunFinfun.fun_of_fin
                                   (adversary_provide_block_hash_result
                                      (update_adversary_transaction_pool (global_adversary (world_global_state w'))
                                         (world_transaction_pool w'))) old_adv_state) (nonce, hash, blc_rcd))
                             hash_res;
        adversary_state_change := adversary_state_change
                                    (update_adversary_transaction_pool (global_adversary (world_global_state w'))
                                       (world_transaction_pool w'));
        adversary_insert_transaction := adversary_insert_transaction
                                          (update_adversary_transaction_pool
                                             (global_adversary (world_global_state w'))
                                             (world_transaction_pool w'));
        adversary_insert_chain := adversary_insert_chain
                                    (update_adversary_transaction_pool (global_adversary (world_global_state w'))
                                       (world_transaction_pool w'));
        adversary_generate_block := adversary_generate_block
                                      (update_adversary_transaction_pool (global_adversary (world_global_state w'))
                                         (world_transaction_pool w'));
        adversary_provide_block_hash_result := adversary_provide_block_hash_result
                                                 (update_adversary_transaction_pool
                                                    (global_adversary (world_global_state w'))
                                                    (world_transaction_pool w'));
        adversary_send_chain := adversary_send_chain
                                  (update_adversary_transaction_pool (global_adversary (world_global_state w'))
                                     (world_transaction_pool w'));
        adversary_send_transaction := adversary_send_transaction
                                        (update_adversary_transaction_pool
                                           (global_adversary (world_global_state w')) (world_transaction_pool w'));
        adversary_last_hashed_round := adversary_last_hashed_round
                                         (update_adversary_transaction_pool
                                            (global_adversary (world_global_state w'))
                                            (world_transaction_pool w')) |}, oracle_state,
       Some {| block_nonce := nonce; block_link := hash; block_records := blc_rcd |})
      else
       ({|
        adversary_state := finfun.FunFinfun.fun_of_fin
                             (finfun.FunFinfun.fun_of_fin
                                (finfun.FunFinfun.fun_of_fin
                                   (adversary_provide_block_hash_result
                                      (update_adversary_transaction_pool (global_adversary (world_global_state w'))
                                         (world_transaction_pool w'))) old_adv_state) (nonce, hash, blc_rcd))
                             hash_res;
        adversary_state_change := adversary_state_change
                                    (update_adversary_transaction_pool (global_adversary (world_global_state w'))
                                       (world_transaction_pool w'));
        adversary_insert_transaction := adversary_insert_transaction
                                          (update_adversary_transaction_pool
                                             (global_adversary (world_global_state w'))
                                             (world_transaction_pool w'));
        adversary_insert_chain := adversary_insert_chain
                                    (update_adversary_transaction_pool (global_adversary (world_global_state w'))
                                       (world_transaction_pool w'));
        adversary_generate_block := adversary_generate_block
                                      (update_adversary_transaction_pool (global_adversary (world_global_state w'))
                                         (world_transaction_pool w'));
        adversary_provide_block_hash_result := adversary_provide_block_hash_result
                                                 (update_adversary_transaction_pool
                                                    (global_adversary (world_global_state w'))
                                                    (world_transaction_pool w'));
        adversary_send_chain := adversary_send_chain
                                  (update_adversary_transaction_pool (global_adversary (world_global_state w'))
                                     (world_transaction_pool w'));
        adversary_send_transaction := adversary_send_transaction
                                        (update_adversary_transaction_pool
                                           (global_adversary (world_global_state w')) (world_transaction_pool w'));
        adversary_last_hashed_round := adversary_last_hashed_round
                                         (update_adversary_transaction_pool
                                            (global_adversary (world_global_state w'))
                                            (world_transaction_pool w')) |}, oracle_state, None) in
      {|
      world_global_state := {|
                            global_local_states := global_local_states (world_global_state w');
                            global_adversary := if
                                                 isSome
                                                   (Addr_to_index (global_currently_active (world_global_state w')))
                                                then new_adversary
                                                else
                                                 update_adversary_round new_adversary
                                                   (global_current_round (world_global_state w'));
                            global_currently_active := global_currently_active (world_global_state w');
                            global_current_round := global_current_round (world_global_state w') |};
      world_transaction_pool := world_transaction_pool w';
      world_inflight_pool := world_inflight_pool w';
      world_message_pool := world_message_pool w';
      world_hash := new_oracle;
      world_block_history := BlockMap_put_adversarial_on_success new_block
                               (global_current_round (world_global_state w')) (world_block_history w');
      world_chain_history := world_chain_history w';
      world_adversary_message_quota := world_adversary_message_quota w';
      world_adversary_transaction_quota := world_adversary_transaction_quota w';
      world_honest_transaction_quota := world_honest_transaction_quota w';
      world_adoption_history := world_adoption_history w' |}).



Definition adversary_mint_global_step adv_state w' :=
  (let '(new_adversary, new_oracle, new_block) := adv_state in
      {|
      world_global_state := {|
                            global_local_states := global_local_states (world_global_state w');
                            global_adversary := new_adversary;
                            global_currently_active := global_currently_active (world_global_state w');
                            global_current_round := global_current_round (world_global_state w') |};
      world_transaction_pool := world_transaction_pool w';
      world_inflight_pool := world_inflight_pool w';
      world_message_pool := world_message_pool w';
      world_hash := new_oracle;
      world_block_history := BlockMap_put_adversarial_on_success new_block
                               (global_current_round (world_global_state w')) (world_block_history w');
      world_chain_history := world_chain_history w';
      world_adversary_message_quota := world_adversary_message_quota w';
      world_adversary_transaction_quota := world_adversary_transaction_quota w';
      world_honest_transaction_quota := world_honest_transaction_quota w';
      world_adoption_history := world_adoption_history w' |}).


Definition retrieve_address addr w' :=
  (if (addr < n_max_actors)%nat as b
         return ((addr < n_max_actors)%nat = b -> option ('I_n_max_actors * LocalState))
        then
         fun H : (addr < n_max_actors)%nat = true =>
         let (actor, is_corrupt) :=
           tnth (global_local_states (world_global_state w')) (Ordinal (n:=n_max_actors) (m:=addr) H) in
         (if is_corrupt as b return (is_corrupt = b -> option ('I_n_max_actors * LocalState))
          then fun _ : is_corrupt = true => None
          else fun _ : is_corrupt = false => Some (Ordinal (n:=n_max_actors) (m:=addr) H, actor))
           (erefl is_corrupt)
        else fun _ : (addr < n_max_actors)%nat = false => None) (erefl (addr < n_max_actors)%nat).


Definition adversary_corrupt_step  actr addr w' :=
{|
    world_global_state := {|
                          global_local_states := set_tnth (global_local_states (world_global_state w'))
                                                   (actr, true) addr;
                          global_adversary := global_adversary (world_global_state w');
                          global_currently_active := global_currently_active (world_global_state w');
                          global_current_round := global_current_round (world_global_state w') |};
    world_transaction_pool := world_transaction_pool w';
    world_inflight_pool := world_inflight_pool w';
    world_message_pool := world_message_pool w';
    world_hash := world_hash w';
    world_block_history := world_block_history w';
    world_chain_history := world_chain_history w';
    world_adversary_message_quota := world_adversary_message_quota w';
    world_adversary_transaction_quota := world_adversary_transaction_quota w';
    world_honest_transaction_quota := world_honest_transaction_quota w';
    world_adoption_history := world_adoption_history w' |}.


Definition broadcast_step nwadvst chain addrlist w' := {|
    world_global_state := {|
              global_local_states := global_local_states (world_global_state w');
              global_adversary := {|
                                  adversary_state := nwadvst;
                                  adversary_state_change := adversary_state_change
                                                              (global_adversary (world_global_state w'));
                                  adversary_insert_transaction := adversary_insert_transaction
                                                                    (global_adversary
                                                                        (world_global_state w'));
                                  adversary_insert_chain := adversary_insert_chain
                                                              (global_adversary (world_global_state w'));
                                  adversary_generate_block := adversary_generate_block
                                                                (global_adversary
                                                                    (world_global_state w'));
                                  adversary_provide_block_hash_result := adversary_provide_block_hash_result
                                                                          (global_adversary
                                                                          (world_global_state w'));
                                  adversary_send_chain := adversary_send_chain
                                                            (global_adversary (world_global_state w'));
                                  adversary_send_transaction := adversary_send_transaction
                                                                  (global_adversary
                                                                      (world_global_state w'));
                                  adversary_last_hashed_round := adversary_last_hashed_round
                                                                    (global_adversary
                                                                      (world_global_state w')) |};
              global_currently_active := global_currently_active (world_global_state w');
              global_current_round := global_current_round (world_global_state w') |};
    world_transaction_pool := world_transaction_pool w';
    world_inflight_pool := fixlist_insert (world_inflight_pool w') (MulticastMsg addrlist chain);
    world_message_pool := world_message_pool w';
    world_hash := world_hash w';
    world_block_history := world_block_history w';
    world_chain_history := world_chain_history w';
    world_adversary_message_quota := mod_incr Adversary_max_Message_sends valid_Adversary_max_Message_sends
                                       (world_adversary_message_quota w');
    world_adversary_transaction_quota := world_adversary_transaction_quota w';
    world_honest_transaction_quota := world_honest_transaction_quota w';
    world_adoption_history := world_adoption_history w' |}.

Definition adversary_transaction_step adv_state tx addrlist w' :=
{|
    world_global_state := {|
                          global_local_states := global_local_states (world_global_state w');
                          global_adversary := {|
                                              adversary_state := adv_state;
                                              adversary_state_change := adversary_state_change
                                                                          (global_adversary (world_global_state w'));
                                              adversary_insert_transaction := adversary_insert_transaction
                                                                                (global_adversary
                                                                                   (world_global_state w'));
                                              adversary_insert_chain := adversary_insert_chain
                                                                          (global_adversary (world_global_state w'));
                                              adversary_generate_block := adversary_generate_block
                                                                            (global_adversary
                                                                               (world_global_state w'));
                                              adversary_provide_block_hash_result := adversary_provide_block_hash_result
                                                                                      (global_adversary
                                                                                      (world_global_state w'));
                                              adversary_send_chain := adversary_send_chain
                                                                        (global_adversary (world_global_state w'));
                                              adversary_send_transaction := adversary_send_transaction
                                                                              (global_adversary
                                                                                 (world_global_state w'));
                                              adversary_last_hashed_round := adversary_last_hashed_round
                                                                               (global_adversary
                                                                                  (world_global_state w')) |};
                          global_currently_active := global_currently_active (world_global_state w');
                          global_current_round := global_current_round (world_global_state w') |};
    world_transaction_pool := fixlist_insert (world_transaction_pool w') (MulticastTransaction (tx, addrlist));
    world_inflight_pool := world_inflight_pool w';
    world_message_pool := world_message_pool w';
    world_hash := world_hash w';
    world_block_history := world_block_history w';
    world_chain_history := world_chain_history w';
    world_adversary_message_quota := world_adversary_message_quota w';
    world_adversary_transaction_quota := mod_incr Adversary_max_Transaction_sends
                                           valid_Adversary_max_Transaction_sends
                                           (world_adversary_transaction_quota w');
    world_honest_transaction_quota := world_honest_transaction_quota w';
    world_adoption_history := world_adoption_history w' |}.


Definition round_end_step msgs new_pool w' :=
{|
    world_global_state := deliver_messages msgs (next_round (world_global_state w'));
    world_transaction_pool := world_transaction_pool w';
    world_inflight_pool := initMessagePool;
    world_message_pool := new_pool;
    world_hash := world_hash w';
    world_block_history := world_block_history w';
    world_chain_history := world_chain_history w';
    world_adversary_message_quota := Ordinal (n:=Adversary_max_Message_sends) (m:=0)
                                       valid_Adversary_max_Message_sends;
    world_adversary_transaction_quota := Ordinal (n:=Adversary_max_Transaction_sends) (m:=0)
                                           valid_Adversary_max_Transaction_sends;
    world_honest_transaction_quota := Ordinal (n:=Honest_max_Transaction_sends) (m:=0)
                                        valid_Honest_max_Transaction_sends;
    world_adoption_history := world_adoption_history w' |}.

Definition adversary_end_step w' := {|
    world_global_state := update_round (world_global_state w');
    world_transaction_pool := world_transaction_pool w';
    world_inflight_pool := world_inflight_pool w';
    world_message_pool := world_message_pool w';
    world_hash := world_hash w';
    world_block_history := world_block_history w';
    world_chain_history := world_chain_history w';
    world_adversary_message_quota := world_adversary_message_quota w';
    world_adversary_transaction_quota := world_adversary_transaction_quota w';
    world_honest_transaction_quota := world_honest_transaction_quota w';
    world_adoption_history := world_adoption_history w' |}.


Locate "_ :: _".
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
  (forall iscrpt os hash_value hash_vl blc_rcd addr lclstt result w' xs, P w' xs ->
  0 < P[ world_step initWorld xs === Some w'] ->
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
    case_eq x => //=.
     (* if x is a transaction gen *)
       - move=> [tx addr] Heq.
        case (_ < _)%nat => //=; last first.
        by rewrite /Dist1.f//= => /ltR0n.
        destruct (tnth _ addr) as [lcl corrupt] eqn: H; case corrupt => //=.
        by rewrite /Dist1.f//= => /ltR0n.
        case Htxvld: (Transaction_valid _); rewrite /evalDist//= /Dist1.f ltR0n lt0b =>/eqP o_w'; case: o_w' => -> //=.
        rewrite -/(transaction_gen_step w' tx ).
        by apply (Htxgen lcl corrupt addr tx w' xs).
        by apply (Htxgenincr lcl corrupt addr tx w' xs).
    (* if x is a transaction drop *)
       - move=> tp_len Heq.
        case Htxmsg: (fixlist_get_nth _) => [txMsg|]; rewrite /evalDist//= /Dist1.f ltR0n lt0b =>/eqP [] -> //=.
        rewrite -/(transaction_drop_step w' tp_len).
        by apply (Htxdrop tp_len txMsg w' xs).
        by apply (Htxdropincr tp_len w' xs).
    (* if x is a honest mint*)
        move=> Heqq.
        move=> _.
        move:(@world_step_honest_mint_simplify x w w' Heqq Hpr_wstep) => [lclstt [iscrpt [addr [result [blc_rcd [hash_vl [hash_value [os]]]]]]]] => -> //=.
        rewrite /honest_step_world //=.
        rewrite -/(honest_mint_step iscrpt os hash_value hash_vl blc_rcd addr lclstt result w').
        by apply (Hhongen iscrpt os hash_value hash_vl blc_rcd addr lclstt result w' xs).

    (* if x is an adversary mint operation *)
        move=> Heqq.
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
       - move=> addr Heqq.
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
        - move=> addrlist Heqq.
        case Hcond: ( _ && _); last first.
          (* obviously invalid for the prior world to be none *)
          by rewrite /evalDist //=; rewrite /Dist1.f //= => /(Rlt_irrefl 0).
        case Hfun :(finfun.FunFinfun.fun_of_fin _) => [nwadvst chain] //=.
        rewrite/Dist1.f => /ltR0n; rewrite lt0b =>/eqP [] -> //=.
        rewrite -/(broadcast_step nwadvst chain addrlist w').
        by apply (Hbrdcst nwadvst chain addrlist w' xs).

     (* if x is a adversary transaction gen *)
        move=> Heqq.
        case Hcond: ( _ < _)%nat; last first.
          (* obviously invalid for the prior world to be none *)
          by rewrite /evalDist //=; rewrite /Dist1.f //= => /(Rlt_irrefl 0).
        case Hfun :(finfun.FunFinfun.fun_of_fin _) => [[adv_state tx] addrlist] //=.
        rewrite/Dist1.f => /ltR0n; rewrite lt0b =>/eqP [] -> //=.
        rewrite -/(adversary_transaction_step adv_state tx addrlist w').
        by apply (Hadvtxgen adv_state tx addrlist w' xs).
     (* if x is round ended *)
        move=> Heqq.
        case Hrndend: (round_ended w'); last first.
          (* obviously invalid for the prior world to be none *)
          by rewrite /evalDist //=; rewrite /Dist1.f //= => /(Rlt_irrefl 0).
        case Hupd: (update_message_pool_queue _) => [msgs new_pool]//=.
        rewrite/Dist1.f => /ltR0n; rewrite lt0b =>/eqP [] -> //=.
        rewrite -/(round_end_step msgs new_pool w').
        by apply (Hrndended msgs new_pool w' xs).
     (* if x is an adversary end gen *)
        move=> Heqq.
        case Hadv: (adversary_activation _); last first.
          (* obviously invalid for the prior world to be none *)
          by rewrite /evalDist //=; rewrite /Dist1.f //= => /(Rlt_irrefl 0).
        rewrite/evalDist//=.
        rewrite/Dist1.f => /ltR0n; rewrite lt0b =>/eqP [] -> //=.
        rewrite -/(adversary_end_step w').
        by apply (Hadvend w' xs).
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
    move=> iscrpt os hash_value hash_link blc_rcd addr lclstt result w' xs Hth_base Hpr .
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
    move=> iscrpt os hash_value hash_link blc_rcd addr lclstt result w' xs Hth_base Hpr .
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
    move=> msgs new_pool w' xs Hth_base Hpract Hupd.
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
  apply /(world_stepP
            (fun w _ =>
               (world_executed_to_round w (Ordinal (n:=N_rounds) (m:=s.+1) Hsvalid) ->
  world_executed_to_round w (Ordinal (n:=N_rounds) (m:=s) Hs'valid))
            ) sc w) => //=.
  (* base case *)
    rewrite /world_step //= /Dist1.f.
    rewrite /world_executed_to_round !has_count //= /initWorldAdoptionHistory.
    by elim (n_max_actors * N_rounds)%nat => //=.
  (* if x is a honest mint step*)
    move=> iscrpt os hash_value hash_link blc_rcd addr lclstt result w' xs Hth_base Hpr .
    rewrite /honest_mint_step.

    move/Rlt_not_eq/nesym: Hpr => Hpr_wbase.
    case (_ < _)%nat => //=.
    case (fixlist_enqueue _) => ls blck .
    move: Hth_base.
    rewrite /world_executed_to_round//=.
    move=> Hth_base.
    rewrite {1}fixlist_insert_rewrite => //=.
    rewrite has_rcons =>/orP ; case; last first.
    rewrite {1}fixlist_insert_rewrite => //=.
    move=> /Hth_base  Hb'.
    by rewrite has_rcons; apply /orP; right.
    by exact (world_step_adoption_history_top_heavy xs w' Hpr_wbase).
    by exact (world_step_adoption_history_overflow_safe xs w' Hpr_wbase).
    admit. (* tricky case *)
    by exact (world_step_adoption_history_top_heavy xs w' Hpr_wbase).
    by exact (world_step_adoption_history_overflow_safe xs w' Hpr_wbase).
    admit. (* tricky case *)

  (* if x is an adversary mint operation *)
    move=> os old_adv_state blc_rcd nonce hash hash_res w' xs Hth_base Hpr Hadv Hupd Hpract.
    by rewrite /adversary_mint_player_step //=; case (hash_res < _)%nat => //= .
  (* if x is a adversary mint global operation*)
    move=> [[adv_state] os] blk w' xs Heq Hpr Hadvact Hhashed Hind Hpract.
    by rewrite /adversary_mint_global_step.
Admitted.



(* if an actor has a chain of length at least l at round l,
  then they will also have a chain of length l for all subsequent rounds *)
Lemma  actor_has_chain_length_ext sc w l o_addr s' s :
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
    move=> iscrpt os hash_value hash_link blc_rcd addr lclstt result w' xs Hth_base Hpr .
    rewrite /honest_mint_step.
    move/Rlt_not_eq/nesym: Hpr => Hpr_wbase.
    case (_ < _)%nat => //=.
    case (fixlist_enqueue _) => ls blck .
    move: Hth_base.
    rewrite /actor_n_has_chain_length_ge_at_round//=.
    move=> Hth_base.
    rewrite {1}fixlist_insert_rewrite => //=.
    rewrite has_rcons =>/orP ; case; last first.
    rewrite {1}fixlist_insert_rewrite => //=.
    move=> /Hth_base  Hb'.
    by rewrite has_rcons; apply /orP; right.
    by exact (world_step_adoption_history_top_heavy xs w' Hpr_wbase).
    by exact (world_step_adoption_history_overflow_safe xs w' Hpr_wbase).
    (* TODO (Kiran): Refactor this into a neater form *)
    move=>/andP[Hltls /andP [H_gcrlts /eqP Heqadr]].
    rewrite {1}fixlist_insert_rewrite => //=.
    rewrite has_rcons; apply/orP; left.
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
    rewrite {1}fixlist_insert_rewrite => //=.
    rewrite has_rcons =>/orP ; case; last first.
    rewrite {1}fixlist_insert_rewrite => //=.
    move=> /Hth_base  Hb'.
    by rewrite has_rcons; apply /orP; right.
    by exact (world_step_adoption_history_top_heavy xs w' Hpr_wbase).
    by exact (world_step_adoption_history_overflow_safe xs w' Hpr_wbase).


    move=>/andP[Hltls /andP [H_gcrlts /eqP Heqadr]].
    rewrite {1}fixlist_insert_rewrite => //=.
    rewrite has_rcons; apply/orP; left.
    apply/andP;split => //=. apply/andP; split => //=.
    apply (@leq_trans s') => //=.
    by apply ltnW => //=.
    by rewrite Heqadr.
    by exact (world_step_adoption_history_top_heavy xs w' Hpr_wbase).
    by exact (world_step_adoption_history_overflow_safe xs w' Hpr_wbase).
    by exact (world_step_adoption_history_top_heavy xs w' Hpr_wbase).
    by exact (world_step_adoption_history_overflow_safe xs w' Hpr_wbase).

    rewrite {1}fixlist_insert_rewrite => //=.
    rewrite has_rcons =>/orP ; case; last first.
    rewrite {1}fixlist_insert_rewrite => //=.
    move=> /Hth_base  Hb'.
    by rewrite has_rcons; apply /orP; right.
    by exact (world_step_adoption_history_top_heavy xs w' Hpr_wbase).
    by exact (world_step_adoption_history_overflow_safe xs w' Hpr_wbase).
    move=>/andP[Hltls /andP [H_gcrlts /eqP Heqadr]].
    rewrite {1}fixlist_insert_rewrite => //=.
    rewrite has_rcons; apply/orP; left.
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








(* ==================================================

                      Hard proofs

 ====================================================*)


Lemma no_bounded_successful_rounds_ext sc w r s : 
  (P[ world_step initWorld sc === Some w] <> 0) ->
        (~~ bounded_successful_round w s) ->
          no_bounded_successful_rounds w r s = no_bounded_successful_rounds w r s.+1.
Proof.
  move: w.
  elim sc => // [w |x xs IHn w ].
  rewrite /world_step //= /Dist1.f.
  case Hinworld: (Some w == Some initWorld)%bool => //= _.
  move/eqP: Hinworld => Hinworld; injection Hinworld => ->  //=.
  rewrite /no_bounded_successful_rounds /no_bounded_successful_rounds'/bounded_successful_round//=.
  rewrite negb_andb => /orP [] //=.
  move=>/negb_true_iff .


  (* TODO(Kiran): Complete this proof *)
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
  actor_n_has_chain_length_ge_at_round w (l + no_bounded_successful_rounds w r (s - 2 * delta + 1)) o_addr
    (Ordinal (n:=N_rounds) (m:=s - delta) Hsvddelta)).
Proof.
  (* TODO: Complete this proof *)
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
  actor_n_has_chain_length_ge_at_round w (l + no_bounded_successful_rounds w r (s - 2 * delta + 1)) o_addr
    (Ordinal (n:=N_rounds) (m:=s - delta) Hsvddelta)) ->

  (*  then by round s.+1, every actor has a chain longer than l + sum_{r + s - 2 * delta + 1} + 1
      (as the only Xi in the range r to s - delta + 1, is the event at s - delta, thus plus 1
   *)
  (forall o_addr : 'I_n_max_actors,
  actor_n_is_honest w o_addr ->
  actor_n_has_chain_length_ge_at_round w (l + no_bounded_successful_rounds w r (s - 2 * delta + 1) + 1) o_addr
    (Ordinal (n:=N_rounds) (m:=s.+1) Hsvd)).
Proof.
  (* TODO: Complete this proof *)
Admitted.

(*
  if round s - delta is bounded successful, then ~~ Xi for i in (s - 2 * delta,....s - delta - 1),
  thus 
      no_bounded_successful_rounds w r (s - delta) =
      no_bounded_successful_rounds w r (s - 2 * delta + 1) + 1.
 *)
Lemma bounded_successful_exclusion sc w r s (l: nat) :
  P[ world_step initWorld sc === Some w] <> 0 ->
  bounded_successful_round w (s - delta) ->
                (l + no_bounded_successful_rounds w r (s - delta).+1)%nat =
                (l + no_bounded_successful_rounds w r (s - 2 * delta + 1) + 1)%nat.
Proof.

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
  (* Our induction on s given (s - r - delta + 1 >= 0) has 4 cases
     1. when s is 0, thus (r - delta + 1 == 0) (simple base case)
     1. when s is 0, thus (r - delta + 1 < 0) (simple base case)
     2. when s is s'.+1, and r - delta + 1 == s'.+1 (proven simply by the fact that messages are delivered in delta rounds)
     3. when s is s'.+1 and r - delta + 1 < s'.+1   (the true inductive case) *)
  (* simple base case - r - delta + 1 == 0*)
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
  (* simple base case - r - delta + 1 < 0*)
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

  (* Basic Induction case - r - delta + 1 == s'.+1*)
  move:Hsvalid =>Hs'valid.
  move:(Hs'valid) =>Hsvalid.
  move=>/eqP Hrseq H_world_exec o_addr H_is_honest //=.
  move: IHs .
  rewrite -{ 2  }Hrseq.
  rewrite no_bounded_successful_rounds_eq0. rewrite addn0.
  move=> IHs.
  rewrite subnAC -addnBA => //=. rewrite subnn; rewrite addn0.
  rewrite no_bounded_successful_rounds_eq0. rewrite addn0.
  move: Hs'valid; rewrite -{1}(addn1 s); move=>/(addr_ltn s 1%nat N_rounds); move=> Hs'valid.
  move: o_addr H_is_honest.
  apply: (chain_growth_weak (x::xs) w (l) (Ordinal Hrvalid) ) => //= .
  by exists addr; exists (Ordinal Hrvalid) ; apply /andP; split => //=.
  by rewrite Hrseq.
  by case r ; [right | left; rewrite subn1 prednK ].
  move/f_equal_pred: Hrseq.
  have: s.+1.-1 = s.
    by [].
  move=> ->.
  move=> <-.
  rewrite -(subn1 (r + delta -1)).
  rewrite -subnAC.
  have H: (subn (subn (subn (r + delta) 1%nat) delta) 1)%nat = (subn r  2%nat).
  rewrite (subnAC (r + delta)).
  have H a b:(subn (addn a b) b) = a.
    induction a => //=.
    induction b => //=.
    have: addn a.+1  b = (addn a b).+1. by []. move=> ->.
    suff: subn (addn a  b).+1 b = (subn (addn a b) b).+1.
    move=> ->.
    by rewrite IHa.
    by rewrite -addn1 -addnA (addnC b) addnA -!addnBA; [rewrite subnn !addn0 addn1| | ].
    by rewrite -addnBA; [rewrite subnn addn0 -subnDA | ].
  by rewrite H; exact (addr2n r).

  (* true inductive case *)
  move: (Hsvalid)=>Hsvd.
  move: Hsvalid. rewrite -{1}(addn1 s); move=>/(addr_ltn s 1%nat N_rounds); move=> Hs'valid.
  move=> sltvalid.
  (* if the delay is greater than s, this means that r must be 0, and thus the proof is trivial *)
  case (delta <= s)%nat eqn:Hdlts; last first.
    (* note to self - add world exec check to actor has chain length ext *)
    move:(actor_has_chain_length_ext (x::xs) w (l + no_bounded_successful_rounds w r (s - delta)) ).
    move/negP/negP:Hdlts=>Hdlts.
    move/andP: (@ltn_leq_split _ _ _ sltvalid Hdlts) => [/eqP Hds1 /eqP Hr0].
    move: IHs .
    rewrite Hr0 Hds1. rewrite subnn.
    have: (s - s.+1)%nat = 0%nat. by elim s => //=.
    move=>->.
    rewrite no_bounded_successful_rounds_eq0. rewrite addn0.
    move=> IHs.
    move=> Hactor_has_chain_l HwrldExec o_addr' Hhon.
    apply (Hactor_has_chain_l o_addr' (Ordinal Hs'valid)) => //=.
    apply IHs.
    rewrite add0n subn1.
    by rewrite -pred_Sn.
    by apply: (world_executed_to_weaken (x::xs) w s Hs'valid ).
    by exact Hhon.
    by right.
    
  (* As in the bitcoin backbone proof, we consider 2 cases - one when Xi' = 0, and one when not *)
  case Hbsuc: (bounded_successful_round w (s - delta));last first.
  move/negP/negP:Hbsuc=>Hbsuc.

  move=> Hwexec o_addr Hhon.
  rewrite subSn.
  rewrite -(no_bounded_successful_rounds_ext (x :: xs) w r (s - delta)) => //= .
  apply:(actor_has_chain_length_ext (x::xs) w (l + no_bounded_successful_rounds w r (s - delta))  o_addr (Ordinal Hs'valid)  (Ordinal (n:=N_rounds) (m:=s.+1) Hsvd)) => //=.

  (* if X'i is false, then the induction hypothesis is enough to prove the statement*)
  apply: (IHs Hs'valid) => //=.
  move/(world_executed_to_weaken (x::xs) w s Hs'valid) : Hwexec.
  by move=> H'; move/H':Hpr_valid.
  by exact Hdlts.


  rewrite subSn //=.


(* (bounded_successful_round w (s - delta) ->
     (no_bounded_successful_rounds r (s - delta).+1 = no_bounded_successful_rounds r (s - 2 * delta + 1).+1 *)
  move=> Hwexec.
  rewrite (bounded_successful_exclusion (x::xs) w r s l Hpr_valid Hbsuc).
  apply: (chain_growth_direct_weaken (x::xs) w l (Ordinal Hrvalid) s).
  by rewrite subn_ltn_pr.
  by [].
  by [].
  move=> Hdelta.
  apply: (chain_growth_implicit_weaken (x::xs) w l (Ordinal Hrvalid) s Hs'valid Hdelta).
  by [].
  by [].
  apply IHs.
  by [].

  by apply: (world_executed_to_weaken (x::xs) w s Hs'valid Hsvd).

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


Qed.









