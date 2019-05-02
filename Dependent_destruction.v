
Inductive Fin : nat -> Set :=
| F1 n : Fin (S n)
| FS n : Fin n -> Fin (S n).


Definition cardinality (n : nat) (A : Type) : Prop :=
  exists (f : A -> Fin n) (g : Fin n -> A),
    (forall x, f (g x) = x) /\
    (forall y, g (f y) = y).

Definition bool_to_Fin_2 (x : bool) : Fin 2 :=
  if x then FS _ (F1 _) else F1 _.

Definition Fin_2_to_bool (y : Fin 2) : bool :=
  match y with
  | F1 _ => false
  | FS _ (F1 _) => true
  | _ => false
  end.

(* Can we write the above definition using Equations ? *)

From Equations Require Import Equations.

Equations Fin_2_to_bool_eq (y : Fin 2) : bool :=
  Fin_2_to_bool_eq (F1 _) := false;
  Fin_2_to_bool_eq (FS _ (F1 _)) := true.

(* Yup, We can do it :) *)

Require Import Program.
Theorem bool_cardinality_2 : cardinality 2 bool.
Proof.
  unfold cardinality.
  exists bool_to_Fin_2, Fin_2_to_bool.
  split; intros.
  unfold bool_to_Fin_2, Fin_2_to_bool. 
  dependent destruction x.
  + auto.
  + dependent destruction x; auto.
    dependent destruction x.
  + destruct y; try auto.
Qed.

Print Assumptions bool_cardinality_2.


Lemma bool_to_Fin_2__Fin_2_to_bool__id :
  forall y, bool_to_Fin_2 (Fin_2_to_bool y) = y.
Proof.
  intros. 
  refine (match y as y' in Fin n
                return forall pf : n = 2,
              eq_rect n Fin y' 2 pf = y -> 
              bool_to_Fin_2 (Fin_2_to_bool y) = y with
          | F1 _ => _
          | FS _ _ => _
          end eq_refl eq_refl).
  intros. inversion pf. subst.
  rewrite <- Eqdep_dec.eq_rect_eq_dec.
  auto.
  auto with arith.
  intros. inversion pf.  subst. 
  rewrite <- Eqdep_dec.eq_rect_eq_dec.
  cbn.
Abort.

Lemma fin_case :
  forall n (P : Fin (S n) -> Type),
    P (F1 _) -> (forall t, P (FS _ t)) -> forall q, P q.
Proof.
  intros.
  refine (match q as q' in Fin n'
                return forall pf : n' = S n,
              eq_rect n' Fin q' (S n) pf = q -> P q with 
          | F1 _ => _
          | FS _ t => _
          end eq_refl eq_refl).
  intros pf H. inversion pf. subst.
  rewrite <- Eqdep_dec.eq_rect_eq_dec.
  + assumption.
  + auto with arith.
  + intros pf H. inversion pf. subst.
    rewrite <- Eqdep_dec.eq_rect_eq_dec.
    apply X0. auto with arith.
Qed.

(*
fin_case
     : forall (n : nat) (P : Fin (S n) -> Type),
       P (F1 n) -> (forall t : Fin n, P (FS n t)) -> forall q : Fin (S n), P q 

Fin_ind
     : forall P : forall n : nat, Fin n -> Prop,
       (forall n : nat, P (S n) (F1 n)) ->
       (forall (n : nat) (f0 : Fin n), P n f0 -> P (S n) (FS n f0)) ->
       forall (n : nat) (f1 : Fin n), P n f1 *)

Require Import Vectors.VectorDef.
Check t_ind.

Lemma bool_to_Fin_2__Fin_2_to_bool__id :
  forall y, bool_to_Fin_2 (Fin_2_to_bool y) = y.
Proof.
  intros.
  pattern y.  
  apply fin_case. auto.
  intros. pattern t.
  apply fin_case.
  auto.
  intros. inversion t0.
Qed.

Ltac fin_dep_destruct v :=
  pattern v; apply fin_case; clear v; intros.

Lemma bool_to_Fin_2__Fin_2_to_bool__id' :
  forall y, bool_to_Fin_2 (Fin_2_to_bool y) = y.
Proof.
  intros.
  fin_dep_destruct y.
  + reflexivity.
  + fin_dep_destruct t.
    ++ reflexivity.
    ++ inversion t.
Qed.

Print Assumptions bool_to_Fin_2__Fin_2_to_bool__id'.


Require Import Arith.

Inductive t : nat -> Type :=
| A : t O
| B n : t n -> t (S n).
 
Lemma custom_ind :
  forall n (P : t n -> Type),
    (forall (Heq : n = O), P (eq_rect O t A n (eq_sym Heq))) ->
    (forall m tm (Heq : n = S m), P (eq_rect (S m) t (B m tm) n (eq_sym Heq))) -> forall q, P q.
Proof.
  intros n P H1 H2 q.
  destruct q as [| n' tm] eqn : Heq.
  specialize (H1 eq_refl).
  assumption.
  specialize (H2 n' tm eq_refl).
  assumption.
Qed.

Theorem t_uniq : forall (n : nat) (a b : t n), a = b.
Proof.
  pose proof Eqdep_dec.UIP_dec Nat.eq_dec as He.
  intros n a b.
  induction n.
  - pattern a. apply custom_ind.
    intros Heq. pattern b. apply custom_ind.
    intros Heq0. f_equal. auto.
    intros.  inversion Heq0.
    intros. pattern b. apply custom_ind.
    intros.  inversion Heq.
    intros. inversion Heq0.

  - pattern a. apply custom_ind.
    + intros Heq; inversion Heq.
    + intros m tm Heq. inversion Heq as [Heq']. pattern b. apply custom_ind.
      * intros Heq0; inversion Heq0.
      * intros m0 tm0 Heq0. inversion Heq0. subst m m0. repeat f_equal.
        apply IHn.
        apply He.
Qed.
