
(** * The Nat Datatype *)

Require Import Dc.
Require Import Dci.
Require Import Kinds.
Require Import Functors.
Require Import Mu.

Require Import Coq.Init.Nat.

Inductive NatF(X : Set) : Set :=
| Zero : NatF X
| Succ : X -> NatF X.

Arguments Zero {X}.
Arguments Succ {X} n.

Global Instance FunListF : Functor NatF :=
  {fmap :=
      fun R1 R2 f n
      => match n with
        | Zero => Zero
        | Succ n => Succ (f n)
        end;
    fmapId := fun A xs => match xs with Zero => eq_refl | Succ _ => eq_refl end
  }.

(** The [Nat] datatype. *)
Definition Nat := Dc NatF.
