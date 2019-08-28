Require Import Arith Program.Equality.

Inductive le' : nat -> nat -> Prop :=
| le'_0 (n : nat) : le' 0 n
| le'_S (n m : nat) : le' n m -> le' (S n) (S m).

Fixpoint le'_irrelevant (n m : nat) (p q : le' n m) : p = q.
Proof.
  dependent destruction p; dependent destruction q.
  - reflexivity.
  - f_equal; apply le'_irrelevant.
Defined.
