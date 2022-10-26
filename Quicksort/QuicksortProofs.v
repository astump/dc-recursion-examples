(** * Proofs over Quicksort. *)
(* Coq *)
Require Import Coq.Program.Equality.
Require Import Coq.Lists.List.
Require Coq.Sorting.Sorted.
Require Import PeanoNat.
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
Require Import PartitionSimpleProofs.
Require Import Quicksort.


Section QuicksortProofs.

  Variable A : Set.
  Variable ltA : A -> A -> bool.
  Variable ltAtrans : forall{a b c : A}, ltA a b = true -> ltA b c = true -> ltA a c = true.
  Variable ltAtotal : forall{a b : A}{q : bool}, ltA a b = negb q -> ltA b a = q.
  Definition gtP := gtP A ltA.
  Definition lteP := lteP A ltA.

  Definition Quicksort := Quicksort A ltA.
  Definition sorted := Sorted.StronglySorted (fun x y => ltA x y = true).

  Lemma centralLemma :
    forall(l1 : list A)(h : A)(l2 : list A),
      Forall (gtP h) l1 ->
      Forall (lteP h) l2 ->
      sorted l1 ->
      sorted l2 ->
      sorted (l1 ++ h :: l2).
  induction l1; intros h l2 gl1 ll2 sl1 sl2.
  + apply Sorted.SSorted_cons.
    ++ exact sl2.
    ++ unfold lteP, PartitionSimpleProofs.lteP in ll2.
       apply (Forall_imp (lteP h) (ltP A ltA h)).
       +++ exact ll2.
       +++ unfold ltP, lteP, PartitionSimpleProofs.lteP; intros x u.
           apply ltAtotal; exact u.
  + simpl.         
    apply Sorted.SSorted_cons.
    ++ apply IHl1 ; try assumption.
       +++ inversion gl1; assumption.
       +++ inversion sl1; assumption.
    ++ apply Forall_append.       
       +++ inversion sl1; assumption.
       +++ inversion gl1. apply Forall_cons.
           ++++ assumption.
           ++++ apply (Forall_imp (lteP h) (ltP A ltA a)); try assumption.
                unfold ltP, lteP, PartitionSimpleProofs.lteP; intros y u.
                apply (ltAtrans (b := h)); try assumption.
                apply ltAtotal; assumption.
  Qed.

  Lemma boundShift{R : kMo (List A)}(fo : forall (d : List A), FoldTi (Algi (ListFi A)) R d)(h0 : A)
        (l : List A)(h : A)(rl : R l)(u : gtP h h0) :
    ForaL (gtP h0) l ->
    ForaL (gtP h) l.
    apply (fo l (Consti (fun l => ForaL (gtP h0) l -> ForaL (gtP h) l))).
    - apply FunConsti.
    - apply rollAlgi.
      intros R1 _ _ ih d fd.
      destruct fd as [ | x xs rxs].
      + intros _ . apply Forall_nil.
      + unfold Consti, ForaL, mkCons;  simpl'.
        intro v; inversion v; clear v.
        apply Forall_cons.
        apply (ltAtrans (b := h0)); assumption.
        exact (ih xs rxs H2).
    - exact rl.
  Qed.
        
  Lemma propPres{R : kMo (List A)}(fo : forall (d : List A), FoldTi (Algi (ListFi A)) R d)
        (l : List A)(h : A)(rl : R l)(P : A -> Prop) :
      ForaL P l ->
      Forall P (Quicksort l).
    apply (fo l (Consti (fun l => ForaL P l -> Forall P (Quicksort l)))).
    apply FunConsti.
    apply rollAlgi.
    intros R1 fo' sfo ih d fd.
    destruct fd as [  | h0 t0 ph0 ].
    + intros _ . apply Forall_nil.    
    + unfold Consti, ForaL, mkCons;  simpl'.
      intro u.
      inversion u.      
      change (fold (ListF A) (Const (list A)) (FunConst (list A)) (QuicksortAlg A ltA)) with Quicksort.
      generalize (partitionLem A ltA R1 sfo t0 ph0 h0).
      generalize (forallPres A ltA fo' t0 ph0 P H2 h0).
      change (partition A ltA t0 h0) with (partitionr A ltA (sfold (ListF A)) t0 h0).
      set (p := partitionr A ltA (sfold (ListF A)) t0 h0).
      destruct p as [p1 p2].
      intros [u1 u2].
      intros [i1 [i2 [i3 i4]]].
      apply Forall_append.
      ++ apply ih .
         +++ exact i3.         
         +++ exact u1.
      ++ apply Forall_cons.
         +++ assumption.
         +++ apply ih.
             ++++ exact i4.
             ++++ exact u2.
    + exact rl.
  Qed.

Definition QsortedP(_ : kMo (List A)) : kMo (List A) :=
  fun l => sorted (Quicksort l).

Theorem Qsorted : forall(l : list A), QsortedP (fun _ => True) (toList l).
  intro l.
  set (ind := foldi (Fi := ListFi A) (toList l) QsortedP).
  unfold QsortedP in *|-*; apply ind ; clear ind.
  + apply FunConsti.
  + apply rollAlgi; unfold AlgF.
    intros R fo sfo ih d di .
    destruct di.
    - apply Sorted.SSorted_nil.
    - simpl'. 
      change (fold (ListF A) (Const (list A)) (FunConst (list A)) (QuicksortAlg A ltA)) with Quicksort.
      generalize (partitionLem A ltA R sfo t H h).
      change (partition A ltA t h) with (partitionr A ltA (sfold (ListF A)) t h).
      set (p := partitionr A ltA (sfold (ListF A)) t h).
      destruct p as [p1 p2].
      intros [i1 [i2 [i3 i4]]].
      set (ih1 := ih p1 i3).
      set (ih2 := ih p2 i4).
      apply centralLemma.
      -- apply (propPres fo); assumption.
      -- apply (propPres fo); assumption.
      -- exact ih1.
      -- exact ih2.
  + exact (toListi l).
Qed.

End QuicksortProofs.
