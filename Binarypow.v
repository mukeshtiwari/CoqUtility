Require Import ZArith Div2 Even.
Require Import Psatz.
Require Import Recdef.
Require Import Coq.NArith.BinNat.
Require Import Coq.Program.Wf.
Require Import Coq.NArith.BinNat.

Section Expo.

 

  Fixpoint power (x : Z) (n : nat) : Z :=
    match n with
    | O => 1%Z
    | S n' => Z.mul x (power x n')
    end.

 
  Function fast_expo_acc (x acc : Z) (n : nat) {measure (fun i => i) n} : Z :=
    match n with
    | O => acc
    | _ => match even_odd_dec n with
          | left _ => fast_expo_acc (Z.mul x x) acc (div2 n)
          | right _ => fast_expo_acc (Z.mul x x) (Z.mul x acc) (div2 n)
          end
    end.
  Proof.
    intros; apply lt_div2; lia.
    intros; apply lt_div2; lia.
  Defined.

  Definition fast_expo (a : Z) (n : nat) : Z :=
    fast_expo_acc a 1%Z n.


  

  Lemma power_unit :
    forall m, power 1 m = 1%Z.
  Proof.
    induction m.
    cbn.  auto.
    cbn.  rewrite IHm.
    auto.
  Qed.

  Lemma power_add_dist :
    forall (x : Z) (n m : nat),
      power x (n + m) = Z.mul (power x n) (power x m).
  Proof.
    intros.
    induction n. 
    assert (power x 0 = 1%Z). cbn. auto.
    rewrite H.
    replace (0 + m)
      with m by lia.
    lia. 
    cbn. rewrite IHn. lia. 
  Qed.
  
  Lemma power_distribute :
    forall (x : Z) (n m : nat),
      power (power x n) m = power x (Nat.mul n m).
  Proof.
    intros x n m.
    revert x n.
    induction m.
    + cbn. intros x n. replace (n * 0) with 0 by lia. 
      cbn.  auto.
    + intros x n. cbn.
      replace (n * S m) with (n + n * m) by lia.
      rewrite power_add_dist.
      f_equal. apply IHm.
  Qed.
  
   
       
    
  Lemma fast_power_acc :
    forall (n : nat) (x ret : Z),
      fast_expo_acc x ret n = Z.mul ret (power x n).
  Proof.
    Opaque Nat.div2.
    induction n using lt_wf_ind; intros.  
    rewrite fast_expo_acc_equation.
    destruct n.
    + cbn. lia.  
    + destruct (even_odd_double (S n)) as [[H1 H2] [H3 H4]]. 
      unfold Nat.double in * |-.
      destruct (even_odd_dec (S n)) as [Hl | Hr].
      pose proof (lt_div2 (S n) (Nat.lt_0_succ n)).
      pose proof (H (Nat.div2 (S n)) H0).
      rewrite H5. f_equal.
      assert (Hm : Z.mul x x = power x 2).
      cbn. lia. rewrite Hm.
      rewrite power_distribute.
      replace (2 * Nat.div2 (S n)) with (double (Nat.div2 (S n))).
      pose proof (even_double (S n) Hl). rewrite <- H6. auto. 
      unfold double. lia. 
      pose proof (lt_div2 (S n) (Nat.lt_0_succ n)).
      pose proof (H (Nat.div2 (S n)) H0 (Z.mul x x) (Z.mul x ret)).
      rewrite H5.
      replace (x * ret * power (x * x) (Nat.div2 (S n)))%Z with
          (ret * (x * power (x * x) (Nat.div2 (S n))))%Z by lia.
      f_equal. cbn. f_equal.
      assert (Hm : Z.mul x x = power x 2).
      cbn. lia. rewrite Hm.
      rewrite power_distribute.
      pose proof (odd_double (S n) Hr).
      assert (n = Nat.double (Nat.div2 (S n))) by lia.
      replace (2 * Nat.div2 (S n)) with (double (Nat.div2 (S n))).
      rewrite <- H7. auto.  
      unfold Nat.double.  lia.
  Qed.

  Lemma slow_is_equal_to_fast :
    forall a n, fast_expo a n = power a n.
  Proof.
    unfold fast_expo.
    intros. rewrite fast_power_acc.
    lia.
  Qed.

  
  Fixpoint expo_recursive (m acc : Z) (p : positive) :=
    match p with
    | xH => Z.mul m acc
    | xO w => expo_recursive (Z.mul m m) acc w
    | xI w => expo_recursive (Z.mul m m) (Z.mul acc m) w
    end.
     
     
  Definition expo_acc (m acc : Z) (n : N) : Z :=
    match n with
    | N0 => acc 
    | Npos p => expo_recursive m acc p
    end.

  Eval compute in expo_acc 2 1 10.

  Lemma binexpo_equal_power :
    forall a acc n , expo_acc a acc n = Z.mul acc (power a (nat_of_N n)).
  Proof.
    intros a acc n.
    revert a acc.
    destruct n.
    + intros a acc.
      cbn. lia.
    + induction p.
      ++  intros a acc. cbn in *.
          assert (Hm : Z.mul a a = power a 2).
          cbn. lia.
          pose proof (IHp (Z.mul a a) (Z.mul acc a)).
          rewrite H.
          replace (acc * a * power (a * a) (Pos.to_nat p))%Z
            with (acc * (a * power (a * a) (Pos.to_nat p)))%Z by lia.
          f_equal. rewrite Pos2Nat.inj_xI.
          cbn. f_equal.  rewrite Hm.
          rewrite power_distribute.
          replace ((Pos.to_nat p + (Pos.to_nat p + 0))) with
              (2 * Pos.to_nat p) by lia.  auto.
      ++ intros a acc. cbn in *.
         assert (Hm : Z.mul a a = power a 2).
         cbn. lia.
         pose proof (IHp (Z.mul a a) acc).
         rewrite H. f_equal.
         rewrite Pos2Nat.inj_xO.
         rewrite Hm. rewrite power_distribute.
         auto.
      ++ intros a acc. cbn in *.
         rewrite Pos2Nat.inj_1. cbn.
         lia.
  Qed.

  Definition expo (a : Z) (m : N) : Z :=
    expo_acc a 1 m.
    

  (* Fairly fast. I can't believe Coq is so good at computing stuff. 
     Kudos to Inria *)
  Eval compute in expo 2 10000.

  Lemma expo_is_equal_to_power :
    forall a n, expo a n = power a (nat_of_N n).
  Proof.
    intros a n. unfold expo. 
    pose proof (binexpo_equal_power a 1 n).
    lia.
  Qed.
  
  
End Expo.
