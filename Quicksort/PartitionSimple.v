(** * Partition *)
(* Partition a list on some value (a : A) w.r.t. an order on A, as is done in
[quicksort]. *)

(* Coq *)
Require Import PeanoNat.
Require Import Coq.Logic.FunctionalExtensionality.
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

Section Partition.

  Variable A : Set.
  Variable ltA : A -> A -> bool.

  Definition PartitionF (X : Set) : Set := A -> (X * X).

  Definition PartitionFmap
    (A B : Set)
    (c : A -> B)
    (f : PartitionF A) : PartitionF B
    := fun bound =>
         let r := f bound in
         (c (fst r), c (snd r)).

  Lemma PartitionFmapId(B : Set)(f : PartitionF B) : PartitionFmap B B (fun x => x) f = f.
    apply functional_extensionality_dep; intro x.
    unfold PartitionFmap.
    destruct (f x).
    trivial.
  Qed.

  Global Instance FunPartitionF : Functor PartitionF :=
    {fmap := PartitionFmap; fmapId := PartitionFmapId }.

  Definition PartitionSAlg : ListSAlg A PartitionF :=
    rollSAlg
      (fun P R up sfo abstIn rec d bound =>
         match d with
           Nil => (abstIn d, abstIn d)
         | Cons x xs =>
             let (l , r) := rec xs bound in
             if ltA x bound then
               (abstIn (Cons x l), up r)
             else
               (up l, abstIn (Cons x r))
         end).

  Definition partitionr{R : Set}(sfo : ListSFoldT A R)(l : R)(bound : A) : (R * R) :=
    sfo PartitionF FunPartitionF PartitionSAlg l bound.

  Definition partition(l : List A)(bound : A) : (List A * List A) :=
    partitionr (sfold (ListF A)) l bound.

  (** return lists instead of Lists *)
  Definition partitionl(xs : List A)(bound : A) : (list A * list A) :=
    let (l, r) := partition xs bound in
    (fromList l, fromList r).

End Partition.

(* tests 
Eval compute in partitionl nat ltb (toList (cons 0 (cons 2 nil))) 1.

Eval compute in partitionl nat ltb (toList (cons 3 (cons 0 (cons 1 (cons 4 (cons 3 nil)))))) 3.

Eval compute in partitionl nat ltb (toList (cons 1 nil)) 1.

Eval compute in (length (snd (partitionl nat ltb (toList (repeat 2 1000)) 1))).
*)
 
