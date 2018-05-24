Require Import Arith.
Require Import Coq.omega.Omega.
Definition even (n: nat) := exists k, n = 2 * k.
Definition odd (n: nat) := exists k, n = 2 * k + 1.

Lemma odd_Sn : forall (n : nat), odd (S n) <-> even n.
Proof.
  intros n. split; intros H.
  unfold odd in H. unfold even. destruct H.
  assert (n = 2 * x) by omega. exists x. auto.
  unfold even in H. unfold odd. destruct H.
  exists x. omega.
Qed.



Lemma even_Sn : forall (n : nat), even (S n) <-> odd n.
Proof.
  intros n. split; intros H.
  unfold even in H. unfold odd.
  destruct H. exists (x - 1).  omega.
  unfold odd in H. unfold even. destruct H.
  exists (x + 1). omega.
Qed.


Lemma even_plus_aux :
forall n m,
(odd (n + m) -> odd n /\ even m \/ even n /\ odd m) /\
(even (n + m) -> even n /\ even m \/ odd n /\ odd m).
Proof.
  induction n.
  intros m. split; intros H. right.  split. unfold even. exists 0. auto.
  simpl in H. auto. simpl in H. left. split. unfold even. exists 0. auto. auto.
  intros m. split; intros H.
  simpl in H. apply odd_Sn in H. pose proof (IHn m). destruct H0.
  pose proof (H1 H). destruct H2. left. split.
  apply odd_Sn. destruct H2. assumption. destruct H2.  assumption.
  right. split. apply even_Sn. destruct H2. assumption.
  destruct H2.  assumption.


  simpl in H. apply even_Sn in H. destruct (IHn m).
  pose proof (H0 H). destruct H2 as [[H21 H22] | [H21 H22]].
  left. split. apply even_Sn. auto. auto.
  right. split. apply odd_Sn. auto. auto.
Qed.
