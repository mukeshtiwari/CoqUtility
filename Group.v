Require Import Setoid.
Require Import Psatz.

(* https://people.cs.umass.edu/~arjun/courses/cs691pl-spring2014/assignments/groups.html *)
Module Type Group.

  (* The set of the group. *)
  Parameter G : Type.

  (* The binary operator. *)
  Parameter f : G -> G -> G.
  
  (* The group identity. *)
  Parameter e : G.

  (* The inverse operator. *)
  Parameter inv : G -> G.

  (* For readability, we use infix <+> to stand for the binary operator. *)
  Infix "<+>" := f (at level 50, left associativity).

  (* The operator [f] is associative. *)
  Axiom assoc : forall a b c, a <+> b <+> c = a <+> (b <+> c).

  (* [e] is the right-identity for all elements [a] *)
  Axiom id_r : forall a, a <+> e = a.

  (* [i a] is the right-inverse of [a]. *)
  Axiom inv_r : forall a, a <+> inv a = e.

  (* Your task is to use the definitions above to prove all the theorems below: *)

  (* The identity [e] is unique. *)
  Lemma unique_id : forall a, a <+> a = a -> a = e.
  Proof.
    intros a H.
    rewrite <- (id_r a).
    rewrite <- (inv_r a).
    rewrite <- assoc.
    rewrite H. auto.
  Qed.
  
    
  (* [i a] is the left-inverse of [a]. *)
  Lemma inv_l : forall a, inv a <+> a = e.
  Proof.
    intros a.
    apply unique_id.
    rewrite assoc.
    assert ((a <+> (inv a <+> a)) = a <+> inv a <+> a).
    rewrite assoc. auto.
    rewrite H. rewrite (inv_r a).
    rewrite <- assoc.
    rewrite (id_r (inv a)). auto.
  Qed.
  
    
  (* [e] is the left-identity. *)
  Lemma id_l : forall a, e <+> a = a.
  Proof.
    intros a.
    rewrite <- (inv_r a).
    rewrite assoc. rewrite inv_l.
    rewrite id_r. auto.
  Qed.
  

    
  (* [x] can be cancelled on the right. *)
  Lemma cancel_r : forall a b x, a <+> x = b <+> x -> a = b. 
  Proof.
    intros a b x H. 
    rewrite <- (id_r a), <- (id_r b).
    rewrite <- (inv_r x).
    rewrite <- assoc, <- assoc.
    rewrite H. auto.
  Qed.
  
    
  (* [x] can be cancelled on the left. *)
  Lemma cancel_l: forall a b x, x <+> a = x <+> b -> a = b.
  Proof.
    intros a b x H.
    rewrite <- (id_l a), <- (id_l b).
    rewrite <- (inv_l x).
    rewrite assoc.
    rewrite H. rewrite assoc.
    auto.
  Qed.
  
    
  (* The left identity is unique. *)
  Lemma e_uniq_l : forall a p, p <+> a = a -> p = e.
  Proof.
    intros a p H.
    rewrite <- (id_r p).
    rewrite <- (inv_r a) at 1.
    rewrite  <- (inv_r a).
    rewrite <- assoc. rewrite H.
    auto.
  Qed.
  
  (* The left inverse is unique. *)
  Lemma inv_uniq_l : forall a b, a <+> b = e -> a = inv b.
  Proof.
    intros a b H.
    rewrite <- (inv_l b) in H.
    apply cancel_r in H.
    auto. 
  Qed.
  
  
  (* The left identity is unique. *)
  Lemma e_uniq_r : forall a p, a <+> p = a -> p = e.
  Proof.
    intros a p H.
    rewrite <- (id_l p).
    rewrite <- (inv_l a) at 1.
    rewrite assoc. rewrite H.
    rewrite (inv_l a). auto.
  Qed.
  
    
  (* The right inverse is unique. *)
  Lemma inv_uniq_r : forall a b, a <+> b = e -> b = inv a.
  Proof. 
    intros a b H.
    rewrite <- (id_l b).
    rewrite <- (inv_l a) at 1.
    rewrite assoc. rewrite H.
    rewrite id_r. auto.
  Qed.
  
    
  (* The inverse operator distributes over the group operator. *)
  Lemma inv_distr : forall a b, inv (a <+> b) = inv b <+> inv a.
  Proof.
    intros a b. symmetry. 
    apply inv_uniq_l.
    rewrite <- assoc.
    rewrite  (assoc (inv b) (inv a) a).
    rewrite (inv_l a).
    rewrite (assoc (inv b) e b).
    rewrite (id_l b).
    rewrite (inv_l b). auto.
  Qed.
  
    
  (* The inverse of an inverse produces the original element. *)
  Lemma double_inv : forall a, inv (inv a) = a.
  Proof.
    intro a. symmetry.
    apply inv_uniq_r.
    rewrite (inv_l a). auto.
  Qed.
    
  (* The identity is its own inverse. *)
  Lemma  id_inv : inv e = e.
  Proof.
    symmetry.
    apply inv_uniq_r.
    rewrite (id_l e).
    auto.
  Qed.
  
End Group.

Require Import Coq.ZArith.ZArith.
Module Z_Add_Zero (Grp : Group).
  Open Scope Z.

  Export Grp.
  (* The set of the group. *)
  Definition G := Z.

  (* The binary operator. *)
  Definition f := Z.add.
  Infix "<+>" := f (at level 50, left associativity).
  
  (* The group identity. *)
  Definition e := 0.

  (* The inverse operator. *)
  Definition inv := Z.sub e.

  Lemma assoc :  forall a b c, a <+> b <+> c = a <+> (b <+> c).
  Proof.
    intros a b c; rewrite Z.add_assoc.
    auto.
  Qed.

  Lemma id_r : forall a, a <+> e = a.
  Proof.
    unfold f, e; intro a;
      lia.
  Qed.
  
  Lemma inv_r : forall a, a <+> inv a = e.
  Proof.
    intro a; unfold f, inv, e; 
      rewrite Z.add_opp_diag_r; auto.
  Qed.

End Z_Add_Zero.
