From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype fintype choice ssrfun seq path.

From Probchain
Require Import FixedList.
Set Implicit Arguments.



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


End fin_fixmap.
