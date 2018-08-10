From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype fintype choice ssrfun seq path.

From mathcomp.ssreflect
Require Import tuple.

From Probchain
Require Import FixedList Parameters InvMisc.

(* Structure used as the addresses for a multicast message *)
Definition AddressList := n_max_actors.-tuple bool.


(* Converts an address list into a seq (ordinal n_max_actors) *)
Fixpoint AddressList_unwrap' (m: nat) (n : 'I_n_max_actors) (ls: m.-tuple bool) : seq ('I_n_max_actors) .
    (* := match ls with
        (* if we have reached the end of our addresslist, no more addresses to convert*)
        | [tuple of [::]] => [::]
        | [tuple of h :: t] => 
        (* if value at index i is true, then add i *)
            if h 
                then n :: (AddressList_unwrap' (n.+1) t)
                else AddressList_unwrap' (n.+1) t
        end. *)
    case m eqn: H.
        (* if we have reached the end of our addresslist, no more addresses to convert*)
        exact [::].
        (* if m is m'.+1, look at the first boolean in the list *)
        case ls => bvec /eqP s_bvec.
            case bvec eqn: H'.
            (* obviously if m = m'.+1, the underlying list can not be empty*)
            inversion s_bvec.
        case b eqn: H''.
        (* if value at index i is true, then add i into our list of addresses to be delivered to *)
        exact   
            (n :: 
                (AddressList_unwrap' _ 
                    (@mod_incr n_max_actors valid_n_max_actors n) 
                    (ntuple_tail ls))).
        (* if value at index i is not true, then skip i, continue with the rest of the list*)
        exact (AddressList_unwrap' _ 
                    (@mod_incr n_max_actors valid_n_max_actors n) 
                    (ntuple_tail ls)).
Defined.

Definition AddressList_unwrap (ls : AddressList) : seq ('I_n_max_actors) :=
    (AddressList_unwrap' _ (Ordinal valid_n_max_actors) ls).




