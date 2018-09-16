From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype fintype choice ssrfun seq path.

From Probchain
Require Import FixedList.
Set Implicit Arguments.

From mathcomp.ssreflect
Require Import tuple.


Section fixmap.
    Variable K : eqType.
    Variable V : eqType.


    Record fixmap n := FixMap {
        fixmap_key : fixlist K n;
        fixmap_value : fixlist V n;
    }.


    Definition fixmap_empty n : fixmap n := 
        FixMap
            (fixlist_empty K n)
            (fixlist_empty V n).
            
    Definition fixmap_find (k : K) (n : nat) (map : fixmap n) : option V :=
        match (fixlist_index_of k (fixmap_key  map)) with
            | None => None
            | Some index => fixlist_get_nth (fixmap_value  map) index
        end.


    Definition fixmap_put (k : K) (v : V) (n : nat) (map : fixmap n) : fixmap n :=
        match (fixlist_index_of k (fixmap_key  map)) with
            | None => let: keys := (fixlist_insert (fixmap_key  map) k) in
                        match (fixlist_index_of k (fixmap_key  map)) with
                            | None => map (* keys list is full, ignore put *)
                            | Some index => let: values := (fixlist_set_nth (fixmap_value  map) v index) in
                                            FixMap  keys values
                        end
            | Some index => let: keys := (fixlist_insert (fixmap_key  map) k) in
                            let: values := (fixlist_set_nth (fixmap_value  map) v index) in
                                            FixMap  keys values
            end.


    Definition fixmap_is_top_heavy n (fm : fixmap n) :=
      (fixlist_is_top_heavy (fixmap_key fm)) && (fixlist_is_top_heavy (fixmap_value fm)).



    Lemma fixmap__put_top_heavy n (fm : fixmap n) k v : fixmap_is_top_heavy fm ->
                                                    fixmap_is_top_heavy (fixmap_put k v fm).
      Proof.
        rewrite /fixmap_put.
        case Hfind: (fixlist_index_of _) => [ ind] //= .
        rewrite /fixmap_is_top_heavy//= => /andP [Hfm_top_heavy Hfv_top_heavy].
    .

    Lemma fixmap_keys_top_heavy n (fm : fixmap n) : fixlist_is_top_heavy (fixmap_key fm).
    Proof.
      move: fm => [[ls Hls] fm_val].
      rewrite /fixmap_key//=.
      clear fm_val; move: Hls.
      move: n.
      elim: ls => //= [ n | x xs IHx n] Hxs.
        by move: (Hxs); move/eqP: Hxs <-  => //=.
      move: Hxs; case: n => [//=| n Hxs].
      move: (Hxs); move: Hxs => /eqP [] /eqP Heq.
      move: (IHx n Heq) => Histopheavy.
      move=> Hxs.
      rewrite /fixlist_is_top_heavy //=.
      move: (erefl _).

    Lemma fixmap_ident (n : nat) (map : fixmap n) : n > 0 -> forall k v, fixmap_find k  (fixmap_put k v  map) = Some v.
    Proof.
        move=> H.
        (* TODO(Kiran): Complete this proof. *)
    Admitted.


       



End fixmap. 

Section fin_fixmap.
    Variable K : finType.
    Variable V : finType.
    Variable n : nat.

    Definition finmap := fixmap K V n.

    Definition finmap_prod (map : finmap) := (fixmap_key map, fixmap_value map).

    Definition prod_finmap (pair : ((fixlist K n) * (fixlist V n))) : finmap :=  
        let (key, value) := pair in
            FixMap  key value.
 

    Lemma finmap_cancel : cancel finmap_prod prod_finmap.
    Proof.
    rewrite /cancel.
    move=> m.
    destruct m => //=.
    Qed.


    Definition finmap_eqMixin :=
    CanEqMixin finmap_cancel.
    Canonical finmap_eqType :=
    Eval hnf in EqType (finmap) finmap_eqMixin.

    Definition finmap_choiceMixin :=
    CanChoiceMixin finmap_cancel.
    Canonical finmap_choiceType :=
    Eval hnf in ChoiceType (finmap) finmap_choiceMixin.

    Definition finmap_countMixin :=
    CanCountMixin finmap_cancel.
    Canonical finmap_countType :=
    Eval hnf in CountType (finmap) finmap_countMixin.
    Definition finmap_finMixin :=
    CanFinMixin finmap_cancel.
    Canonical finmap_finType :=
    Eval hnf in FinType (finmap) finmap_finMixin.

    Canonical finmap_of_eqType := Eval hnf in [eqType of finmap].
    Canonical finmap_of_choiceType := Eval hnf in [choiceType of finmap].
    Canonical finmap_of_countType := Eval hnf in [countType of finmap].
    Canonical finmap_of_finType := Eval hnf in [finType of finmap].





End fin_fixmap.

