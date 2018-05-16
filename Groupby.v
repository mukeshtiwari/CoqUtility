Require Import Coq.Init.Peano.
Require Import Notations.
Require Import Coq.Lists.List.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Coq.omega.Omega.
Require Import Coq.Arith.Le.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Numbers.NatInt.NZMul.
Require Import Coq.Structures.OrdersFacts.
Require Import Coq.ZArith.Znat. 
Require Import Coq.QArith.QArith_base.
Require Import Coq.QArith.QOrderedType.
Require Import QArith_base Equalities Orders OrdersTac.
Require Import Coq.Sorting.Permutation.
Require Import Wf.
Require Import Lexicographic_Product.
Require Import Qreduction.
Require Import Coq.Bool.Bool.
Require Import Inverse_Image. 
Require Import Coq.Bool.Sumbool.
Require Import Coq.Sorting.Mergesort.
Require Import Coq.Sorting.Sorted.
Import ListNotations.
Require Import Coq.Program.Basics.
Require Import Program.
Require Import FunInd Recdef.

Notation "'existsT' x .. y , p" :=
  (sigT (fun x => .. (sigT (fun y => p)) ..))
    (at level 200, x binder, right associativity,
     format "'[' 'existsT' '/ ' x .. y , '/ ' p ']'") : type_scope.

Module NatOrder <: TotalLeBool.
  Open Scope nat.
  Definition t := nat.
  Fixpoint leb x y :=
    match x, y with
    | 0, _ => true
    | _, 0 => false
    | S x', S y' => leb x' y'
    end.
  Infix "<=??" := leb (at level 35).
  Theorem leb_total : forall a1 a2, a1 <=?? a2 = true \/ a2 <=?? a1 = true.
  Proof. induction a1.
         destruct a2; left; auto.
         destruct a2. right; auto.
         pose proof (IHa1 a2). firstorder.
  Qed.
  
End NatOrder.

Module Import NatSort := Sort NatOrder.


Module RatOrder <: TotalLeBool.
  Definition t := Q.

  
  Definition leb r1 r2 := 
    match Q_dec r1 r2 with
    | inleft l => match l with
                  | left _ =>   true 
                  | right _ => false
                  end
    | inright r => true
    end.
                 
 
  Theorem leb_total : forall r1 r2, is_true (leb r1 r2) \/ is_true (leb r2 r1).
  Proof.   
    intros r1 r2. unfold is_true, leb.
    destruct (Q_dec r1 r2). destruct s. auto.
    right.  destruct (Q_dec r2 r1). destruct s. auto.
    pose proof (Qlt_trans r1 r2 r1 q0 q).
    pose proof (Qlt_irrefl r1). unfold not in H0.
    pose proof (H0 H). inversion H1. auto. auto.
  Qed.
  
End RatOrder.

Module Import QSort := Sort RatOrder.

Definition Rat_eq r1 r2 := Qeq_bool r1 r2.

Lemma filter_len : forall (l : list Q) (f : Q -> bool),
    (length (filter f l) <= length l)%nat.
Proof.
  induction l. intros. auto.
  intros. simpl.
  remember (f a) as v.
  destruct v. simpl. pose proof (IHl f).
  omega.
  pose proof (IHl f). omega.
Qed.

Fixpoint takewhile (f : Q -> bool) (l : list Q) : list Q :=
  match l with
  | [] => []
  | h :: t => if f h then h :: takewhile f t else []
  end.

Fixpoint dropwhile (f : Q -> bool) (l : list Q) : list Q :=
  match l with
  | [] => []
  | h :: t => if f h then dropwhile f t else h :: t
  end. 
    

Lemma inverse_of_each : forall (l : list Q) (f : Q -> bool),
    takewhile f l ++ dropwhile f l = l.
Proof.
  induction l. intros. auto.
  intros. remember (f a) as v.
  destruct v. simpl. rewrite <- Heqv.
  pose proof (IHl f). simpl. apply f_equal.
  auto.
  simpl. rewrite <- Heqv. auto.
Qed.

Lemma takelength : forall (l :  list Q) (f : Q -> bool),
    (length (takewhile f l) <= length l)%nat.
Proof.
  induction l. auto.
  intros. remember (f a) as v.
  destruct v. simpl. rewrite <- Heqv.
  simpl. pose proof (IHl f). omega.
  simpl. rewrite <- Heqv. simpl. omega.
Qed.

Lemma droplength : forall (l : list Q) (f : Q -> bool),
    (length (dropwhile f l) <= length l)%nat.
Proof.
  induction l. auto.
  intros.  remember (f a) as v.
  destruct v. simpl. rewrite <- Heqv.
  simpl. pose proof (IHl f). omega.
  simpl. rewrite <- Heqv. simpl. omega.
Qed.


Lemma groupby : forall (l : list Q),  {x : list (list Q) | concat x = l}.
Proof.
  induction l using (well_founded_induction
                     (wf_inverse_image _ nat _ (@length _)
                        PeanoNat.Nat.lt_wf_0)).
  destruct l. exists []. auto.  
  remember (takewhile (Rat_eq q) l) as fhalf.
  remember (dropwhile (Rat_eq q) l) as shalf. 
  assert (length shalf <= length l)%nat.
  pose proof (droplength l (Rat_eq q)). 
  rewrite Heqshalf. auto.
  assert (length shalf < length (q :: l))%nat.
  simpl. omega.
  pose proof (H shalf H1). destruct H2.
  exists ((q :: fhalf) :: x). simpl.
  apply f_equal. rewrite e.
  pose proof (inverse_of_each l (Rat_eq q)).
  rewrite Heqfhalf. rewrite Heqshalf. auto.
Defined.

(* Change it to Qed if you want nice output of Eval statement *)
Eval compute in  (proj2_sig (groupby (sort [(3 # 1)%Q; (2 # 3)%Q; (2 # 1)%Q; (2 # 3)%Q; (2 # 1)]))).

Lemma concat_groupby_inverse :
    forall (l : list Q), concat (proj1_sig (groupby l)) = l. 
Proof.
  intros l.
  remember (groupby l) as v.
  destruct v. simpl. auto.
Qed.


Lemma concat_rat_dep :
  forall  (l : list Q) , length l = length (concat (proj1_sig (groupby (sort l) ))).
Proof.
  intros l.
  rewrite (concat_groupby_inverse (sort l)).
  pose proof (Permuted_sort l).
  pose proof (Permutation_length).
  pose proof (H0 _ l (sort l) H). auto.
Qed.

(* Non dependent type *)
Fixpoint countem y (xs: list Q) : nat :=
   match xs with
   | [] => 0
   | x :: more => if Qeq_bool x y then S (countem y more) else 0
   end.


Fixpoint take (y : nat) (xs: list Q) :=
   match y, xs with
   | O, _ => []
   | S y', [] => []
   | S y', x :: more => x :: take y' more
   end.

Fixpoint skip y (xs: list Q) :=
   match y, xs with
   | O, _ => xs
   | S y', [] => []
   | S y', x :: more => skip y' more
   end.

Lemma skip_bounded:
   forall y xs, (length (skip y xs) <= length xs)%nat.
Proof.
   intros y xs. revert y.
   induction xs; intros; simpl.
   - destruct y; simpl; omega.
   - destruct y; simpl; try omega.
     rewrite IHxs. omega.
Qed.

Lemma take_skip:
   forall k (xs : list Q) , (take k xs ++ skip k xs = xs)%nat.
Proof.
   intros k xs. revert k.
   induction xs; intros; simpl.
   - destruct k; simpl; auto.
   - destruct k; simpl; auto.
     rewrite IHxs. auto.
Qed.

Function groupbysimple (xs: list Q) { measure length xs } :=
   match xs with
   | [] => []
   | x :: more =>
        let k := countem x more in
        (x :: take k more) :: groupbysimple (skip k more)
   end.
Proof.
   intros.
   simpl.
   assert (length (skip (countem x more) more) <= length more)%nat by
        apply skip_bounded.
   omega.
Defined.


Eval compute in (groupbysimple (sort [(3 # 1)%Q; (2 # 3)%Q; (2 # 1)%Q; (2 # 3)%Q; (2 # 1)])).

Lemma groupby_identity:
   forall xs, concat (groupbysimple xs) = xs.
Proof.
   intros.
   functional induction (groupbysimple xs).
   - simpl. auto.
   - simpl. rewrite IHl. rewrite take_skip. auto.
Qed.


Lemma concat_rat: forall  (l : list Q) , length l = length (concat (groupbysimple (sort l))).
Proof.
  intros l.
  pose proof (groupby_identity (sort l)).
  rewrite H.
  pose proof (Permuted_sort l).
  pose proof (Permutation_length).
  pose proof (H1 _ l (sort l) H0).
  auto.
Qed.
