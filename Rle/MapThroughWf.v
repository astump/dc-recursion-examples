(** * Well-Founded MapThrough *)

Require Import Coq.Lists.List Coq.Program.Wf Psatz.
Require Import Coq.Init.Nat.

Import ListNotations.

Section MapThroughWf.

  Definition mappedT(A B : Set) : Set :=
    A -> forall (xs : list A), B * sig (fun xs' : list A => length xs' <= length xs).

  Program Fixpoint mapThroughWf{A B : Set}(f:mappedT A B)(xs : list A) { measure (length xs) } : list B  :=
    match xs with
      [] => []
    | hd :: tl =>
      let '(b, exist _ c pf) := f hd tl in
        b :: mapThroughWf f c
    end.
    Next Obligation.
    simpl.
    lia.
    Qed.

(*
Print mapThroughWf. (* 6 *)
Print mapThroughWf_func. (*102*)
Print mapThroughWf_func_obligation_1. (*68*)
Print mapThroughWf_func_obligation_2. (*4*)
*)
End MapThroughWf.

