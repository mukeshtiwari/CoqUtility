
  Require Import Bool.
  Require Import Program.

  Inductive bits: nat -> Type :=
  | nothing: bits 0
  | bit {k} (more: bits k) (x: bool) :  bits (S k).

Fixpoint lt {k} (a b: bits k) : Prop :=
  match a with 
  | nothing => fun (b : bits O) =>
      match b with nothing => False end
  | @bit k amore ax => fun (b : bits (S k)) =>
    match b in bits k return
      match k with
      | O => IDProp
      | S k => bits k -> Prop
      end
    with
    | bit bmore bx => fun amore =>
        lt amore bmore \/ amore = bmore /\ ax = false /\ bx = true
    | nothing => idProp
    end amore
  end b.
  
