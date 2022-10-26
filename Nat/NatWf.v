(** * Well-Founded relation on [nat] *)
(** Used in some lemmas for well-founded [RLE].  *)
Require Import PeanoNat Lt.
From Equations Require Import Equations Signature.

Local Open Scope nat_scope.
  
Implicit Types m n p : nat.

Section Well_founded_Nat.

Variable A : Type.

Variable f : A -> nat.
Definition ltof (a b:A) := f a < f b.
Definition gtof (a b:A) := f b > f a.

Lemma ltofLem : forall(a b : A)(n : nat),
                  f a < S n ->
                  f b < f a ->
                  f b < n.
  intros a b n Ha Hb.
  apply Nat.lt_le_trans with (f a); auto with arith.
Qed.

Theorem Wf_ltf : well_founded ltof.
Proof.
  assert (H : forall n (a:A), f a < n -> Acc ltof a).
  { induction n.
    - intros; absurd (f a < 0); auto with arith.
    - intros a Ha. apply Acc_intro. unfold ltof at 1. intros b Hb.
      apply IHn. exact (ltofLem a b n Ha Hb). }
  intros a. apply (H (S (f a))). auto with arith.
Defined.

(** The [WellFounded] is from the [Equations] package. *)
Global Instance Wfltof : WellFounded ltof := Wf_ltf.

End Well_founded_Nat.

