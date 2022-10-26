(** * Well-Founded Mergesort *)
(** Mergesort implemented via the [Function] keyword, as well as a theorem
showing it sorts. The proof has the same structure as the divide-and-conquer
approach in [Mergesort.v]. *)

(* Coq *)
Require Import Coq.Sorting.Mergesort.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Lists.List.
Require Import Orders.
Require Import Psatz.
Require Import PeanoNat.
From Coq Require Import Recdef.
Import ListNotations.

Local Coercion is_true : bool >-> Sortclass.
Module MergesortWf(Import A : TotalTransitiveLeBool').
  Definition A := t.  
  Fixpoint split (l : list A) : list A * list A :=
    match l with
      nil       => (nil, nil)
    | (x :: xs) => match xs with
                 nil => ([x], nil)
                 | (y :: ys) =>  let ret := split ys in
                               (x :: fst ret, y :: snd ret)
               end
    end.

  Fixpoint splitSmaller(l : list A) :
      length (fst (split l)) <= length l /\
      length (snd (split l)) <= length l.
    destruct l.
    + simpl; lia.
    + destruct l.
      ++ simpl; lia.
      ++ simpl.
         destruct (splitSmaller l).
         lia.
  Qed.

  Module Import MergeSort := Sort A.

  Function mergeSortHWf
    (a : A) (l:list A) {measure length l} : list A :=
    match l with
    | nil => [a]
    | (x :: xs) => let ret := split xs in
               merge (mergeSortHWf a (fst ret)) (mergeSortHWf x (snd ret))
    end.
  intros; destruct (splitSmaller xs); simpl; apply Nat.lt_succ_r; assumption.
  intros; destruct (splitSmaller xs); simpl; apply Nat.lt_succ_r; assumption.
  Qed.
    
  Definition mergeSortWf(l : list A) : list A :=
    match l with
      nil => []
    | hd :: tl => mergeSortHWf hd tl
    end.

  (** Theorems *)

  Local Notation sorted := (LocallySorted leb) (only parsing).
  Local Notation SSorted := (StronglySorted leb) (only parsing).
  
  (** Go from LocallySorted <-> StronglySorted *)
  Definition locally_StronglySorted_iff : forall xs,
      sorted xs <-> SSorted xs.
    intros; split.
    -  intros ls.
       apply (Sorted_StronglySorted leb_trans).
       apply (Sorted_LocallySorted_iff leb xs).
       exact ls.
    - intros ls.
      apply (Sorted_LocallySorted_iff leb xs).
      apply StronglySorted_Sorted.
      exact ls.
  Qed.
  
  (** Rebasing the theorem with assumption of strongly (instead of
       locally) sorted xs and ys. *)
  Corollary SStronglySorted_merge : forall xs ys,
      SSorted xs ->
      SSorted ys ->
      SSorted (merge xs ys).
    intros xs ys xSsorted ySsorted.
    assert (sorted xs) as xsorted by (apply locally_StronglySorted_iff; exact xSsorted).
    assert (sorted ys) as ysorted by (apply locally_StronglySorted_iff; exact ySsorted).
    apply locally_StronglySorted_iff; exact (Sorted_merge xs ys xsorted ysorted).
  Qed.
  
    Lemma MergeSortHSorts :
      forall (l : list A)(a : A),
        SSorted (mergeSortHWf a l).
      intros.
      apply (mergeSortHWf_ind (fun a xs ys => SSorted ys)).
      - repeat constructor.
      - intros.
        destruct ret.
        simpl.
        apply SStronglySorted_merge.
        apply H.
        apply H0.
    Qed.

    Theorem mergeSortSorts: forall (l : list A),
        SSorted (mergeSortWf l).
      intro l.
      destruct l.
      + constructor.
      + apply MergeSortHSorts.
    Qed.
End MergesortWf.
