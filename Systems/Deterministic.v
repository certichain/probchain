From Probchain
Require Import Comp Notationv1 BlockChain Protocol OracleState BlockMap InvMisc.

From mathcomp.ssreflect
Require Import ssreflect ssrnat ssrbool seq fintype eqtype.

Definition example2:=
    x <- 3;
    y <-$ [0 ... 3];
    ret y.
About example2.


About finType.

Fixpoint world_step (w : World) (s : seq RndGen) : option (Comp World) :=
    None.
