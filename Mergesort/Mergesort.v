(** * Mergesort *)
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
Require Import List.ExtraLib.

Section MergeSort.
  (** We presume nothing more than a comparator on type A. *)
  Variable A : Set.
  Variable leq : A -> A -> bool.

  (** split carrier *)
  Definition SplitF(X : Set) : Set := X * X.
  Definition SplitFmap{A B : Set} : FmapT A B SplitF :=
    fun f s => match s with
              (a1, a2) => (f a1, f a2)
            end.
  Definition SplitFMapId :
    forall (A : Set)(a : SplitF A), SplitFmap id a = a.
    intros.
    unfold SplitF in a; destruct a.
    simpl. unfold id.
    reflexivity.
  Defined.
  Global Instance FunSplitF : Functor SplitF :=
    {fmap A B := SplitFmap;
      fmapId := SplitFMapId
    }.  

  (** Definition of split *)
  Definition SplitAlg : ListSAlg A SplitF :=
    rollSAlg 
      (fun P R up sfo abstIn split xs =>
         match xs with
         | Nil => (abstIn Nil, abstIn Nil)
         | Cons hd tl => match (out (ListF A) sfo tl) with
                        | Nil => (abstIn (Cons hd tl), abstIn Nil)
                        | Cons hd' tl' => let (ys, zs) := (split tl') in
                                         (abstIn (Cons hd ys), abstIn (Cons hd' zs))
                        end
         end
      ).

  Definition Split (xs : List A) : (List A) * (List A) :=
    sfold (ListF A) SplitF FunSplitF SplitAlg xs.

  (** Mergesort. merge is defined in [ExtraLib] *)
  Definition MergeSortAlg : ListAlg A (Const (A -> list A)) :=
    rollAlg 
      (fun R fo sfo mergeSort xs a =>
         match xs with
           Nil => [a]
         | Cons hd tl =>
             let (ys, zs) := sfo SplitF FunSplitF SplitAlg tl in
             merge leq (mergeSort ys a) (mergeSort zs hd)
         end).

  Definition mergeSortH (xs : List A) (x : A) :=
    fold (ListF A) (Const  (A -> list A)) (FunConst (A -> list A)) (MergeSortAlg) xs x.

  Definition mergeSort (xs : list A) : list A :=
    match xs with
    | [] => []
    | hd :: tl => mergeSortH (toList tl) hd
    end.    

  (** a performance test, no recursion here (just calling split) *)

  Definition MTestAlg : ListAlg A (Const (A -> list A)) :=
    rollAlg 
      (fun R fo sfo mtest xs a =>
         match xs with
           Nil => [a]
         | Cons hd tl =>
             let (ys, zs) := sfo SplitF FunSplitF SplitAlg tl in
             (a :: fromListr fo ys) ++ (hd :: fromListr fo zs)
         end).

  Definition mtesth (xs : List A) (x : A) :=
    fold (ListF A) (Const  (A -> list A)) (FunConst (A -> list A)) MTestAlg xs x.

  Definition mtest (xs : list A) : list A :=
    match xs with
    | [] => []
    | hd :: tl => mtesth (toList tl) hd
    end.    

End MergeSort.

(*Require Extraction.
Extraction Language Haskell.
Extraction "Mtest.hs" mtest.
 *)
Arguments mergeSort{A}.
Arguments mtest{A}.

(* Eval compute in (fromList (merge nat leb (toList [ 1 ; 2; 3]) (toList [6 ; 8 ; 2]))). *)
(*Eval compute in (mergeSort ltb [ 3 ; 17 ; 5 ; 3 ; 2 ; 14 ; 100 ; 0]). *)





















