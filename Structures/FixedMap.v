From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype fintype choice ssrfun seq path.

From Probchain
Require Import FixedList.



Section fixmap.
    Variable K : eqType.
    Variable V : eqType.

    Record fixmap n := FixMap {
        fixmap_key : fixlist K n;
        fixmap_value : fixlist V n;
    }.


    Definition fixmap_empty n : fixmap n :=
        FixMap
            n
            (fixlist_empty K n)
            (fixlist_empty V n).
            
    Definition fixmap_find (k : K) (n : nat) (map : fixmap n) : option V :=
        match (fixlist_index_of k (fixmap_key n map)) with
            | None => None
            | Some index => fixlist_get_nth (fixmap_value n map) index
        end.


    Definition fixmap_put (k : K) (v : V) (n : nat) (map : fixmap n) : fixmap n :=
        match (fixlist_index_of k (fixmap_key n map)) with
            | None => let: keys := (fixlist_insert (fixmap_key n map) k) in
                        match (fixlist_index_of k (fixmap_key n map)) with
                            | None => map (* keys list is full, ignore put *)
                            | Some index => let: values := (fixlist_set_nth (fixmap_value n map) v index) in
                                            FixMap n keys values
                        end
            | Some index => let: keys := (fixlist_insert (fixmap_key n map) k) in
                            let: values := (fixlist_set_nth (fixmap_value n map) v index) in
                                            FixMap n keys values
            end.

    Lemma fixmap_ident (n : nat) (map : fixmap n) : n > 0 -> forall k v, fixmap_find k n (fixmap_put k v n map) = Some v.
    Proof.
        move=> H.
        (* TODO(Kiran): Complete this proof. *)
    Admitted.

End fixmap. 

