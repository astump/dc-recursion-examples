(** * Run-Length-Decode -- inverse of RLE. *)
Require Import Coq.Lists.List.
Import ListNotations.

Section Rld.
Context {A : Set}.

Fixpoint rld(xs : list (nat * A)) : list A :=
  match xs with
  | [] => []
  | (n, v) :: tl => repeat v n ++ rld tl
  end.
End Rld.
