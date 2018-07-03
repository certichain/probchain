From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat seq ssrfun eqtype.
Require Import FMapAVL.

From Probchain
Require Import BlockChain InvMisc.



Module M := FMapAVL.Make(Hash_Triple_as_OT).
Definition OracleState := M.t nat.

Definition OracleState_find k (m : OracleState) := M.find k m.

About eqtype.Equality.type.


Definition OracleState_put (p: (Hashed * (list Transaction) * nat) * nat) (m: OracleState) :=
  M.add (fst p) (snd p) m.

(* Notation "k |-> v" := (pair k v) (at level 60). *)
(* Notation "[ ]" := (M.empty nat). *)
(* Notation "[ p1 , .. , pn ]" := (OracleState_put p1 .. (OracleState_put pn (M.empty nat)) .. ). *)

