
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
  

Definition pairop' {k} {rt} (a b: bits k)
                     (r0: rt)
                     (r1: forall k', bits k' -> bool -> bits k' -> bool -> (k = S k') -> rt) : rt :=
   (* you must have the "as k''", and then the return must match it and not k *)
   match k as k'' return (
        match k'' with
        | 0 => option ()
        | S k' => option (bits k' * bool * bits k' * bool)
        end) -> (k = k'') -> rt
   with
   | 0 => fun _ _ => r0
   | S k' =>
        fun H pf =>
        match H with
        | None => r0
        | Some (amore, ax, bmore, bx) => r1 k' amore ax bmore bx pf
        end
   end (pairextract a b) eq_refl.
