(** * Quicksort *)
(* Coq *)
Require Import Coq.Lists.List.
Import ListNotations.

(* Ours *)
Require Import Dc.
Require Import Dci.
Require Import Kinds.
Require Import Mu.
Require Import List.List.
Require Import Functors. 
Require Import ExtraLib.
Require Import PartitionSimple.

Section Quicksort.
  Variable A : Set.
  Variable ltA : A -> A -> bool.

  Definition partitionr{R : Set}(sfo : ListSFoldT A R) := partitionr A ltA sfo.

  Definition QuicksortAlg : ListAlg A (Const (list A)) :=
    rollAlg
      (fun R fo sfo qsort xs =>
         match xs with
           Nil       => nil
         | Cons p xs =>
             let (l, r) := partitionr sfo xs p in
             qsort l ++ p :: qsort r
         end).

  Definition Quicksort(l : List A) : list A :=
    @fold (ListF A) (Const (list A)) (FunConst (list A)) QuicksortAlg l.

  Definition quicksort(l : list A) : list A := Quicksort (toList l).

  Ltac foldQuicksort :=
    try (change (List A) with (Dc.Dc (ListF A)));
    change (fold (ListF A) (Const (list A)) (FunConst (list A)) QuicksortAlg) with Quicksort.
End Quicksort.

Arguments quicksort{A}.

(*
(* tests *)
Eval compute in quicksort ltb (cons 5 (cons 3 (cons 0 (cons 1 (cons 4 nil))))).

Eval compute in quicksort ltb (cons 0 (cons 1 nil)).

(*Eval compute in (length (fromList (toList (repeat 2 10000)))).*)

Eval compute in (quicksort ltb 
(58 :: 33 :: 82 :: 73 :: 84 :: 31 :: 40 :: 48 :: 90 :: 77 :: 72 :: 92 :: 66 :: 11 :: 10 :: 79 :: 69 :: 25 :: 74 :: 24 :: 9 :: 91 :: 16 :: 83 :: 27 :: 39 :: 42 :: 3 :: 93 :: 46 :: 87 :: 2 :: 86 :: 65 :: 44 :: 18 :: 63 :: 67 :: 4 :: 78 :: 95 :: 19 :: 61 :: 55 :: 54 :: 21 :: 36 :: 22 :: 34 :: 52 :: 81 :: 76 :: 57 :: 43 :: 1 :: 71 :: 12 :: 80 :: 47 :: 14 :: 41 :: 32 :: 28 :: 88 :: 29 :: 94 :: 89 :: 13 :: 15 :: 49 :: 60 :: 50 :: 5 :: 17 :: 38 :: 96 :: 56 :: 8 :: 70 :: 20 :: 51 :: 62 :: 64 :: 37 :: 97 :: 6 :: 23 :: 53 :: 30 :: 99 :: 68 :: 7 :: 98 :: 59 :: 35 :: 45 :: 100 :: 85 :: 26 :: 75 :: nil)).

*)
