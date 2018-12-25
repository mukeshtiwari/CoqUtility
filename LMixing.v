Module EQ.

  Record class (T : Type) :=
    Class {cmp : T -> T -> Prop }.

  Structure type :=
    Pack {obj : Type;
          class_of : class obj}.

  
  Definition op (e : type) : obj e -> obj e -> Prop :=
    let 'Pack _ (Class _ the_cmp) := e in the_cmp.

  Check obj.
  Arguments op {e} x y : simpl never.
  Arguments Class {T} cmp.

  Module theory.

    Notation "x == y" := (op x y)
                           (at level 70).
  End theory.
End EQ.

Import EQ.theory.
Check forall (e : EQ.type) (a b : EQ.obj e), a == b.

Fail Check 3 == 3.

Definition nat_eq (x y : nat) := Nat.compare x y = Eq.

Definition nat_EQcl : EQ.class nat := EQ.Class nat_eq.

Canonical Structure nat_EQty := EQ.Pack _ nat_EQcl.

Check 3 == 3.

Eval compute in 3 == 4.

Fail Check forall (e : EQ.type) (a b : EQ.obj e), (a, b) == (a, b).

Definition pair_eq (e1 e2 : EQ.type) (x y : EQ.obj e1 * EQ.obj  e2) :=
  fst x == fst y /\  snd x = snd y.

Definition pair_EQcl e1 e2 := EQ.Class (pair_eq e1 e2).

Canonical Structure pair_EQty (e1 e2 : EQ.type) : EQ.type :=
  EQ.Pack _ (pair_EQcl e1 e2).

Check forall (e : EQ.type) (a b : EQ.obj e), (a, b) == (a, b).

Check forall n m : nat, (3, 4) == (n, m).

Module LE.

  Record class T := Class {cmp : T -> T -> Prop}.

  Structure type :=
    Pack {obj : Type;
          class_of : class obj}.

  Definition op (e : type) : obj e -> obj e -> Prop :=
    let 'Pack _ (Class _ f) := e in f.

  Arguments op {_} x y : simpl never.
  Arguments Class {T} cmp. 

  Module theory.

    Notation "x <= y" := (op x y)
                           (at level 70).
  End theory.

End LE.

Import LE.theory.

Definition nat_le x y := Nat.compare x y <> Gt.

Definition nat_LEcl : LE.class nat := LE.Class nat_le.

Canonical Structure nat_LEty := LE.Pack nat nat_LEcl.

Definition pair_le e1 e2 (x y : LE.obj e1 * LE.obj e2) :=
  fst x <= fst y /\  snd x <= snd y.

Definition pair_LEcl e1 e2 := LE.Class (pair_le e1 e2).

Canonical Structure pair_LEty (e1 e2 : LE.type) : LE.type :=
  LE.Pack _ (pair_LEcl e1 e2).

Check (3,4,5) <= (3,4,5).

Check 2 <= 3 /\ 2 == 2.
Check 2 == 2.

Fail Check forall (e : EQ.type) (x y : EQ.obj e), x <= y -> y <= x -> x == y.
Fail Check forall (e : LE.type) (x y : LE.obj e), x <= y -> y <= x -> x == y.

Module LEQ.

  Record mixin (e : EQ.type) (le : EQ.obj e -> EQ.obj e -> Prop) :=
    Mixin {compat : forall x y : EQ.obj e, le x y /\ le y x <-> x == y}.


  Record class T :=
    Class {
        EQ_class : EQ.class T;
        LE_class : LE.class T;
        extra : mixin (EQ.Pack T EQ_class) (LE.cmp T LE_class)}.

  
  Structure type := _Pack {obj : Type;
                           class_of : class obj}.

  Check Mixin.
  Arguments Mixin {e le} _.
  Check Class.
  Arguments Class {T} _ _ _.

  Module theory.

    Fail Check forall (le : type) (n m : obj le), n <= m -> n <= m -> n == m.

    Definition to_EQ (e : type) : EQ.type :=
      EQ.Pack _ (EQ_class _ (class_of e)).

    Canonical Structure to_EQ.

    Definition to_LE (e : type) : LE.type :=
      LE.Pack _ (LE_class _ (class_of e)).

    Canonical Structure to_LE.

    Lemma lele_eq (e : type) (x y : obj e) : x <= y -> y <= x -> x == y.
      intros; apply (compat _ _ (extra _ (class_of e)) x y); split; auto.
    Qed.


    Arguments lele_eq {e} x y _.
  End theory.

End LEQ.

Import LEQ.theory.
Check lele_eq.


  
Example test_algebraic (n m : nat) : n <= m -> m <= n -> n == m.
Fail apply (lele_eq n m).
Abort.

Example test_algebraic2 (l1 l2 : LEQ.type) (n m : LEQ.obj l1 * LEQ.obj l2) :
  n <= m -> m <= n -> n == m.
Fail apply (lele_eq n m).
Abort.

Require Import Psatz.
Require Import Omega.

Lemma nat_LEQ_compat (n m : nat) : n <= m /\ m <= n <-> n == m.
Admitted.

Definition nat_LEQmx := LEQ.Mixin nat_LEQ_compat.

Lemma pair_LEQ_compat (l1 l2 : LEQ.type) (n m : LEQ.obj l1 * LEQ.obj l2) :
  n <= m /\ m <= n <-> n == m.
Admitted.

Definition pair_LEQmx l1 l2 := LEQ.Mixin (pair_LEQ_compat l1 l2).

Module Add_instance_attempt.

  Canonical Structure nat_LEQty : LEQ.type :=
    LEQ._Pack nat (LEQ.Class nat_EQcl nat_LEcl nat_LEQmx).

  Canonical Structure pair_LEQty (l1 l2 : LEQ.type) : LEQ.type :=
    LEQ._Pack (LEQ.obj l1 * LEQ.obj l2)
              (LEQ.Class
                 (EQ.class_of (pair_EQty (to_EQ l1) (to_EQ l2)))
                 (LE.class_of (pair_LEty (to_LE l1) (to_LE l2)))
                 (pair_LEQmx l1 l2)).

  Example test_algebraic (n m : nat) : n <= m -> m <= n -> n == m.
  apply (lele_eq n m).
  Qed.

  Example test_algebraic2 (n m : nat * nat) : n <= m -> m <= n -> n == m.
  now apply (lele_eq n m).
  Qed.


End Add_instance_attempt.

Require Import Strings.String.

Module infrastructure.

  Inductive phantom {T : Type} (t : T) : Type := Phantom.

  Definition unify {T1 T2 : Type} (t1 : T1) (t2 : T2) (s : option string) :=
    phantom t1 -> phantom t2.

  Definition id {T : Type} {t : T} (x : phantom t) := x.

  Notation "[find v | t1 ~ t2 ] p" := (fun v (_ : unify t1 t2 None) => p)
                                        (at level 50, v ident, only parsing).
  Notation "[find v | t1 ~ t2 | s ] p" := (fun v (_ : unify t1 t2 (Some s)) => p)
                                            (at level 50, v ident, only parsing).
  Notation "'Error : t : s" := (unify _ t (Some s))
                                 (at level 50, format "''Error' : t : s").
  Open Scope string_scope.
End infrastructure.
