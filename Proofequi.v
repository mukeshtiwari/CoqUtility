

Require Import Psatz. 
Require Import ZArith.
Require Import  Coq.Logic.EqdepFacts.
Require Import ProofIrrelevance.
Open Scope Z.

Lemma eq_proj:
  forall a b : {x : Z | x mod 3 = 0},
  a = b <-> proj1_sig a = proj1_sig b.
Proof.
  split; intros.
  + rewrite H; auto.
  + destruct a, b.
    apply eq_exist_uncurried;
      cbn in H; subst.
    exists eq_refl. apply UIP.
Qed.


(* Without proof irrelevance *)
Require Import Coq.Logic.Eqdep_dec.


Lemma eq_projt:
  forall a b : {x : Z | x mod 3 = 0},
  a = b <-> proj1_sig a = proj1_sig b.
Proof.
  split; intros.
  + rewrite H. auto.
  + destruct a, b. cbn in *.
    subst. f_equal. apply eq_proofs_unicity.
    intros. lia.
Qed.

