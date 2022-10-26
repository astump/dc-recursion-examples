(** * Mergesort Theorems *)
(* Coq *)
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Classes.RelationClasses.
Import ListNotations.

(* Ours *)
Require Import Dc.
Require Import Dci.
Require Import Kinds.
Require Import Mu.
Require Import Functors.
Require Import List.ExtraLib.
Require Import List.List.
Require Import Mergesort.Mergesort.

(** Coerces [leq] from [bool] to [Prop] easily. *)
Local Coercion is_true : bool >-> Sortclass.

Section MergeSortProofs.
    (** We presume [A] has a total order. *)
    Variable A : Set.
    Variable leq : A -> A -> bool.
    Variable leq_trans : Transitive leq.
    Variable leq_total : forall a1 a2, leq a1 a2 \/ leq a2 a1.

    (** Merge is defined in [ExtraLib], and is taken from [Coq.Sorting.MergeSort]. *)
    Definition merge := merge leq.

    Local Notation sorted := (LocallySorted leq) (only parsing).
    Local Notation SSorted := (StronglySorted leq) (only parsing).

    Local Ltac invert H := inversion H; subst; clear H.

    (** The main lemma. This proof is ripped from [Coq.Sorting.MergeSort]. *)
    Theorem Sorted_merge : forall l1 l2,
        sorted l1 -> sorted l2 -> sorted (merge l1 l2).
      induction l1; induction l2; intros; simpl; auto.
      destruct (leq a a0) eqn:Heq1.
      invert H.
      simpl. constructor; trivial; rewrite Heq1; constructor.
      assert (sorted (merge (b::l) (a0::l2))) by (apply IHl1; auto).
      clear H0 H3 IHl1; simpl in *.
      destruct (leq b a0); constructor; auto || rewrite Heq1; constructor.
      assert (leq a0 a) by
        (destruct (leq_total a0 a) as [H'|H']; trivial || (rewrite Heq1 in H'; inversion H')).
      invert H0.
      constructor; trivial.
      assert (sorted (merge (a::l1) (b::l))) by auto using IHl1.
      clear IHl2; simpl in *.
      destruct (leq a b); constructor; auto.
    Qed.


    (** Go from [LocallySorted] <-> [StronglySorted] on [A] ([StronglySorted]
    presumes totality, which we have done). *)
    Definition locally_StronglySorted_iff : forall xs,
        sorted xs <-> SSorted xs.
      intros; split.
      -  intros ls.
         apply (Sorted_StronglySorted leq_trans).
         apply (Sorted_LocallySorted_iff leq xs).
         exact ls.
      - intros ls.
        apply (Sorted_LocallySorted_iff leq xs).
        apply StronglySorted_Sorted.
        exact ls.
    Qed.
    
    (** 
       Rebasing the theorem with assumption of strongly (instead of
       locally) sorted xs and ys.
     *)
    Corollary SStronglySorted_merge : forall xs ys,
        SSorted xs ->
        SSorted ys ->
        SSorted (merge xs ys).
      intros xs ys xSsorted ySsorted.
      assert (sorted xs) as xsorted by (apply locally_StronglySorted_iff; exact xSsorted).
      assert (sorted ys) as ysorted by (apply locally_StronglySorted_iff; exact ySsorted).
      apply locally_StronglySorted_iff; exact (Sorted_merge xs ys xsorted ysorted).
    Qed.

    (** [MotivePresF] asserts that it is safe to induct on the results of [split]. *)
    Definition MotivePresF
      (R : List A -> Prop)
      (l : List A) :=
      let ret := Split A l in
      R (fst ret) /\ R (snd ret).

    Definition MotivePresFmap(B C : kMo (List A)) : FmapiT (List A) MotivePresF B C.
      intros c d u; generalize u; simpl; intros [v1 v2].
      apply conj.
      - apply c; assumption.
      - apply c; assumption.
    Defined.
    
    Lemma MotivePresFmapId : FmapiId (List A) MotivePresF MotivePresFmap.
      intros B i x; destruct x as [p1 p2]; reflexivity.
    Qed.
    
    Global Instance FunMotivePresFi : Functori (List A) MotivePresF :=
      {fmapi := MotivePresFmap ; fmapiId := MotivePresFmapId }.

    Lemma MotivePres
               (U : List A -> Prop)
               (sfo : forall d : List A, ListSFoldTi A U d)
               (xs : List A)
               (sl : U xs) :
      MotivePresF U xs.
      apply (sfo xs MotivePresF).
      - exact FunMotivePresFi.
      - apply rollSAlgi; unfold SAlgF.
        intros S R up sfo' abstin ih d di.
        fold (List A) in *; unfold MotivePresF in *.
        destruct di as [| hd tl] eqn:co.
        + split.
          * apply abstin; setoid_rewrite (abstInId (ListF A) Nil); apply nilFi.
          * apply abstin; setoid_rewrite (abstInId (ListF A) Nil); apply nilFi.
        + simpl'; foldAbstIn.
          change (sfold (ListF A) SplitF FunSplitF (SplitAlg A) ?l) with (Split A l).
          (* This is generalized "out" -- we want to do [out] this way so that
             we get the assumption (R tl'), which destructing on (out tl) does
             not give. *)
          destruct (sfo' tl (ListFi A) (depList A)
                      (rollSAlgi (ListFi A) (Fi := ListFi A)
                         (fun S R up sfo abstin ih d di => (ListFiMap A R S up d di))) r
              ) as [| hd' tl'] eqn:co'.
          simpl'.
          * split.
            ** apply abstin; apply consFi; assumption.
            ** apply abstin; apply nilFi; assumption.
          * simpl'.
            destruct (Split A tl') as [ys zs] eqn:spl.
            foldAbstIn.
            set (i := ih tl' r0).
            rewrite spl in i.
            split.
            ** apply abstin; constructor; apply i.
            ** apply abstin; constructor; apply i.
      - exact sl.
    Qed.
        
    Definition mergesort := mergeSort leq.
    Definition mergesortH := mergeSortH A leq.

    (** The main theorem. *)
    Lemma MergeSortHSorts :
      forall (l : list A)(a : A),
        SSorted (mergesortH (toList l) a).
      intro l.
      apply (foldi (Fi := ListFi A) (toList l) (fun _ l => forall (a : A), SSorted (mergesortH l a))).
      - apply FunConsti.
      - apply rollAlgi; unfold AlgF.
        intros R' fo' sfo' ih d di.
        destruct di as [| x xs].
        + repeat constructor.
        + simpl'.
          change (fold (ListF A) (Const (A -> list A)) (FunConst (A -> list A)) 
                    (MergeSortAlg A leq) ?l ?a) with (mergesortH l a).
          change (sfold (ListF A) SplitF FunSplitF (SplitAlg A) xs) with (Split A xs).
          destruct (Split A xs) eqn:co.
          set  (guards := MotivePres R' sfo' xs H).
          unfold MotivePresF in guards.
          rewrite co in guards.
          intros a'.
          apply SStronglySorted_merge.
          * apply ih; apply guards.
          * apply ih; apply guards.
      - apply toListi.
    Qed.          
        
    Theorem mergeSortSorts: forall (l : list A),
        SSorted (mergesort l).
      intro l.
      destruct l.
      + constructor.
      + apply MergeSortHSorts.
    Qed.

End MergeSortProofs.
