
From sflib Require Import sflib.
Require Import Lia.

Theorem lt_le_S : forall n m,
n < m -> S n <= m.
Proof.
    lia.
Qed.

Theorem lt_n_Sm_le : forall n m, n < S m -> n <= m.
Proof. lia. Qed.

Theorem neq_0_lt : forall n, 0 <> n -> 0 < n.
Proof. lia. Qed.