Require Import Arith Omega.

Section bounded_forall.

  Implicit Type (P : nat -> Prop).

  Fixpoint bounded_forall P n :=
    match n with
      | 0 => True
      | S n => P 0 /\ bounded_forall (fun i => P (S i)) n
    end.

  Fact bounded_forall_spec P n : bounded_forall P n -> forall i, i < n -> P i.
  Proof.
    revert P.
    induction n as [ | n IHn ]; simpl; intros P Hn i Hi; try omega.
    destruct i as [ | i ]; try tauto.
    apply IHn with (P := fun i => P (S i)); try tauto.
    omega.
  Qed.

End bounded_forall. 

Lemma can_be_brute_forced : forall (n : nat), n < 10 -> n mod 10 = (n ^ 5) mod 10.
Proof.
  now apply bounded_forall_spec.
Qed.
