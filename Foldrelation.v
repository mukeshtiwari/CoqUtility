Require Import List.
Import ListNotations.

Fixpoint fold {A B : Type} (f : A -> B -> B) (b : B) (l : list A)  :=
  match l with
  | [] => b
  | h :: t =>
    let v := fold f b t in
    f h v
  end.

(* 

fold f b [] = b
fold f b (h :: t) = let v = fold f b t in f h v 
===============================================
FoldR f b [] b
FoldR h t : FoldR f b t w -> FoldR f b (h ::t ) (f h w)

*)
Eval compute in fold (fun x y => x * y) 1 [1; 2; 3; 4].


(* Fold {A B : Type) (f : A -> B -> B) b l acc  (acc', v) *)
Inductive Foldind {A B : Type} (f : A -> B -> B) (b : B) : list A  -> B -> Prop :=
| FBasecase : Foldind f b [] b
| FConscase h t w : Foldind f b t w  ->  Foldind f b (h :: t) (f h w).


Lemma equivalence :
  forall (A B : Type) (f : A -> B -> B) l (b b' : B),
    Foldind f b l b' <-> b' = fold f b l.
Proof.
  intros A B f.
  induction l.
  + intros b b'.
    split; intros.
    inversion H; subst.
    cbn. auto.
    cbn in H. subst. constructor.
  + intros b b'.
    split; intros.
    cbn. inversion H; subst. apply IHl in H3.
    rewrite H3.  auto.
    cbn in H. subst.
    constructor. rewrite IHl.
    auto.
Qed.


Fixpoint fold_acc {A B : Type} (f : A -> B -> B) (b : B) (l acc : list A)  :=
  match l with
  | [] => (acc, b)
  | h :: t =>
    let (acc', v) := fold_acc f b t acc in
    (h :: acc', f h v)
  end.

(* In Haskell, it would 
fold_acc f b [] acc = (acc, b)
fold_acc f b (h :: t) acc = 
  let (acc', w) = fold_acc f b t acc in
  (h :: acc', f h w) 

In Relational style 
----------------------------Base Case 
FoldR f b [] acc (acc, b)

FoldR f b t acc (acc', w) 
----------------------------------Inductive case
FoldR f b (h :: t) acc (h :: acc', f h w)

*)


Eval cbn in fold_acc (fun x y => x + y) 0 [1; 2; 3] [10; 11].

Inductive Foldaccind {A B : Type} (f : A -> B -> B) (b : B) : list A -> list A -> list A * B -> Prop :=
| FoldAccbase acc : Foldaccind f b [] acc (acc, b)
| FoldConscase h t acc acc' v : Foldaccind f b t acc (acc', v) ->
                                Foldaccind f b (h :: t) acc ((h :: acc'), (f h v)).

Lemma same_fold_acc :
  forall (A B : Type) (f : A -> B -> B) (l acc acc' : list A) (b w : B),
    Foldaccind f b l acc (acc', w) <-> w = snd (fold_acc f b l acc)  /\
                                      acc' = fst (fold_acc f b l acc).
Proof.
  intros A B f.
  induction l.
  + intros acc acc' b w.
    split; intros.
    ++inversion H; subst. 
      cbn. auto. 
    ++ cbn in H.  destruct H. subst. constructor.
  + intros acc acc' b w.
    split; intros.
    ++ cbn. inversion H; subst.
       rewrite IHl in H3.
       destruct H3. subst.
       remember (fold_acc f b l acc) as t.
       destruct t. cbn. auto.
    ++ cbn in H.
       remember (fold_acc f b l acc) as t.
       destruct t.  cbn in *. destruct H. subst.
       constructor. rewrite IHl.
       cbn. rewrite <- Heqt.
       auto.
Qed.
