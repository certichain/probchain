From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat seq ssrfun eqtype choice fintype path.


From Probchain
Require Import BlockChain InvMisc FixedList.

Parameter OracleState_size: nat.


Module M := FMapAVL.Make(Hash_Triple_as_OT).
Definition OracleState := M.t nat.

Definition OracleState_new : OracleState.
Proof.
  (* TODO(Kiran): complete this proof *)
Admitted.


Definition OracleState_find k (m : OracleState) := M.find k m.



Definition OracleState_put (p: (Hashed * (list Transaction) * nat) * nat) (m: OracleState) :=
  M.add (fst p) (snd p) m.

(* Notation "k |-> v" := (pair k v) (at level 60). *)
(* Notation "[ ]" := (M.empty nat). *)
(* Notation "[ p1 , .. , pn ]" := (OracleState_put p1 .. (OracleState_put pn (M.empty nat)) .. ). *)

