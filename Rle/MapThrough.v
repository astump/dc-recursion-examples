(** * MapThrough *)
(* similar to repeatedly from Haskell's #<a href="https://hackage.haskell.org/package/extra-1.7.10/docs/Data-List-Extra.html">Data.List.Extra</a>#. *)

Require Import Dc.
Require Import Dci.
Require Import Kinds.
Require Import Functors.
Require Import List.List.

Require Import Coq.Lists.List.
Require Import Coq.Init.Nat.

Import ListNotations.

Definition mappedT(A B : Set) : Set :=
  forall(R : Set)(sfo:ListSFoldT A R),
    A -> R -> B * R.

Section MapThrough.

  Context {A : Set}.

  Definition MapThroughAlg{B : Set}(f : mappedT A B) : ListAlg A (Const (list B)) :=
    rollAlg (fun R _ sfo mapThrough xs => 
      match xs with
        Nil => []
      | Cons hd tl =>
        let (b,c) := f R sfo hd tl in
          b :: mapThrough c
      end).

  Definition mapThroughr{R : Set}(fo : ListFoldT A R)
                        {B : Set}(f : mappedT A B) : R -> list B :=
    fo (Const (list B)) (FunConst (list B)) (MapThroughAlg f).

  Definition mapThrough{B : Set}(f : mappedT A B) : List A -> list B :=
    mapThroughr (fold (ListF A)) f.

End MapThrough.

