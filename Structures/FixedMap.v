From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat seq ssrfun eqtype choice fintype path.

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
            
    Definition fixmap_find (k : K) (n : nat) (map : fixmap n) : option V.
    Admitted.


    Definition fixmap_put (k : K) (v : V) (n : nat) (map : fixmap n) : fixmap n.
    Admitted.

End fixmap. 

