Require Import List.
Import ListNotations.

Notation "'existsT' x .. y , p" :=
  (sigT (fun x => .. (sigT (fun y => p)) ..))
    (at level 200, x binder, right associativity,
     format "'[' 'existsT' '/ ' x .. y , '/ ' p ']'") : type_scope.
(* http://www.cs.nott.ac.uk/~pszgmh/fold.pdf *)

(* Changing Haskell List function into Inductive data type, sort of Relational programming *)
Module Haskellfun.
  Section Hfold.
  
    Fixpoint fold (A B : Type) (f : A -> B -> B) (b : B) (l : list A) : B :=
      match l with
      | [] => b
      | h :: tl => f h (fold A B f b tl)
      end.


    Inductive foldind (A B : Type) (f : A -> B -> B) (b : B) : list A -> B -> Type :=
    | Basecase  : foldind A B f b [] b
    | Conscase b' h tl : foldind A B f b tl b' -> foldind A B f b (h :: tl) (f h b').
    

    Lemma same_fold_foldind :
      forall (A B : Type) (f : A -> B -> B) (b : B) (l : list A),
        foldind A B f b l (fold A B f b l).
    Proof.
      refine (fun A B f b =>
                fix Fn l :=
                match l with
                | [] => Basecase A B f b (* Base case *)
                | h :: tl => _ (* Cons case *)
                end).
      cbn. eapply Conscase. apply Fn.
    Qed.
    
    Lemma same_fold_foldind_proof :
      forall (A B : Type) (f : A -> B -> B) (b : B) (l : list A) (v : B),
        foldind A B f b l v -> v = fold A B f b l.
    Proof.
      refine (fun A B f b =>
                fix Fn l :=
                match l with
                | [] => fun v Hi => _
                | h :: tl => fun v Hi => _
                end).
      inversion Hi; cbn; reflexivity.
      inversion Hi; subst; cbn; f_equal;
        apply Fn; assumption.
    Qed.
    
    Lemma fold_fun_correctness :
      forall (A B : Type) (f : A -> B -> B) (l : list A) (b v : B),
        v = fold A B f b l -> foldind A B f b l v.
    Proof.
      refine (fun A B f =>
                fix Fn l :=
                match l with
                | [] => fun b v Hv => _
                | h :: t => fun b v Hv => _
                end).
      subst; cbn; eapply Basecase.
      subst; cbn; eapply Conscase; auto.
    Qed.
    
    
  End Hfold. 
  
  Section Htakewhile.

    
    Fixpoint takewhile (A : Type) (p : A -> bool) (l : list A) : list A :=
      match l with
      | [] => []
      | h :: t => if p h then h :: takewhile A p t else []
      end.
    
    
    (* constant space *)
    Fixpoint takewhile_acc (A : Type) (p : A -> bool) (l acc : list A) :=
      match l with
      | [] => List.rev acc
      | h :: tl => if p h then takewhile_acc A p tl (h :: acc)
                  else List.rev acc
      end.
    
    Lemma same_takewhile_acc :
      forall (A : Type) (p : A -> bool) (l acc : list A),
        takewhile_acc A p l acc = List.rev acc ++ takewhile A p l.
    Proof.
      intros A p.
      induction l.
      + cbn. intro acc.  rewrite app_nil_r.
        auto.
      + cbn. intro acc. case_eq (p a); intro Pa.
        ++ rewrite IHl. cbn.
           rewrite <-  app_assoc.
           auto.
        ++ rewrite app_nil_r. auto.
    Qed.

    (* Turing takewhile_acc into relation. 
       R : l -> acc -> takewhile_acc A p l acc *)
    Inductive Takewhileind (A : Type) (p : A -> bool) : list A -> list A -> list A -> Prop :=
    | TBasecase acc : Takewhileind A p [] acc acc 
    | TTruecase h tl acc ts : p h = true -> Takewhileind A p tl (h :: acc) ts -> 
                              Takewhileind A p (h :: tl) acc ts
    | TFalsecase h tl acc : p h = false -> Takewhileind A p (h :: tl) acc acc.

    Lemma same_takewhile_takewhileind :
      forall (A : Type) (p : A -> bool) (l acc : list A),
        Takewhileind A p l acc (List.rev (takewhile_acc A p l acc)).
    Proof.
      intros A p.
      induction l.
      + cbn; intros acc.
        rewrite rev_involutive.
        constructor.
      + cbn; intros acc.
        case_eq (p a); intros Pa.
        constructor 2. auto.
        apply IHl.
        rewrite rev_involutive. constructor 3.
        auto.
    Qed.
    
  End  Htakewhile.

  Section Hdropwhile.
    
    Fixpoint dropWhile (A : Type) (p : A -> bool) (l : list A) : list A :=
      match l with
      | [] => []
      | h :: tl => if p h then dropWhile A p tl else h :: tl
      end.
    
    Inductive Dropwhileind (A : Type) (p : A -> bool) : list A -> list A -> Prop :=
    | DBasecase : Dropwhileind A p [] []
    | DTruecase h tl t : p h = true ->  Dropwhileind A p tl t ->   Dropwhileind A p (h :: tl) t 
    | DFalsecase h t : p h = false -> Dropwhileind A p (h :: t) (h :: t).
    
    Lemma same_drop_caitlin_convinced_and_smiling :
      forall (A : Type) (p : A -> bool) l, Dropwhileind A p l (dropWhile A p l).
    Proof.
      intros A p.
      induction l.
      + cbn. constructor 1.
      + cbn. case_eq (p a); intros Pa.
        eapply DTruecase. auto. auto.
        constructor 3.  auto.
    Qed.

  End Hdropwhile.

  Section Hintersperse.
     
    Fixpoint intersperse (A : Type) (c : A) (l : list A) : list A :=
      match l with
      | [] => []
      | [h] => [h]
      | h :: t => h :: c :: intersperse _ c t
      end.
    
    Fixpoint intersperse_acc (A : Type) (c : A) (l : list A) (acc : list A) : list A :=
      match l with
      | [] => acc
      | [h] => acc ++ [h]
      | h :: t => intersperse_acc A c t (acc ++ [h; c])
      end.
     

     
     
     
    Eval cbn in intersperse_acc nat 0 [1; 2; 3; 4] []. (*  [1; 0; 2; 0; 3; 0; 4]
     : list nat *)
    Eval cbn in intersperse nat 0 [1; 2; 3; 4].

    
    Lemma intersperse_intersperse_acc :
      forall (A : Type) (c : A) (l acc : list A),
        acc ++ intersperse A c l = intersperse_acc A c l acc.
    Proof.
      induction l.
      + cbn. intros. rewrite app_nil_r. auto.
      + destruct l.
        ++ cbn. intros acc.  auto.  
        ++ assert (intersperse A c (a :: a0 :: l) = a :: c :: intersperse A c (a0 :: l)).
           auto. rewrite H.
           intro acc.
           assert (intersperse_acc A c (a :: a0 :: l) acc =
                   intersperse_acc A c (a0 :: l) (acc ++ [a; c])).
           auto. rewrite H0.
           rewrite <- IHl. rewrite <- app_assoc.
           auto.
    Qed.
    
    Inductive Intersperseind (A : Type) (c : A) : list A -> list A -> list A -> Prop :=
    | IBasecase acc : Intersperseind A c [] acc acc
    | IOnecase h xs : Intersperseind A c [h] xs (xs ++ [h])
    | IGencase h t acc zs : Intersperseind A c t (acc ++ [h; c]) zs ->
                            Intersperseind A c (h :: t) acc  zs. 

    Lemma same_intersperse : forall (A : Type) (c : A) (l acc : list A), 
        Intersperseind A c l acc (intersperse_acc A c l acc).
    Proof.
      intros A c.
      induction l.
      + cbn. intros.
        constructor. 
      + intros. destruct l.
        ++ cbn in *. constructor 2.
        ++ constructor 3. 
           eapply IHl.
    Qed.
    
    Lemma intersperse_acc_same : forall (A : Type) (c : A) (l acc : list A), 
        Intersperseind A c l acc (acc ++ intersperse A c l).
    Proof.
      intros. rewrite intersperse_intersperse_acc.
      apply same_intersperse.
    Qed.
        
      
  End Hintersperse.
