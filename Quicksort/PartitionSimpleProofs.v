(** * Proofs over Partition *)

(* Coq *)
Require Import Coq.Lists.List.
Require Import PeanoNat.
Require Import Coq.Logic.FunctionalExtensionality.
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

Section PartitionPfs.

  Variable A : Set.
  Variable ltA : A -> A -> bool.

  Definition lteP(lower:A)(y : A) : Prop := ltA y lower = false.
  Definition gteP(upper:A)(y : A) : Prop := ltA upper y = false.
  Definition ltP(lower:A)(y : A) : Prop := ltA lower y = true.
  Definition gtP(upper:A)(y : A) : Prop := ltA y upper = true.

  Definition partition := partition A ltA.

  Definition partitionInv(R : List A -> Prop)
    (xs : List A) : Prop :=
    forall (bound : A),
      let p := partition xs bound in
      ForaL (gtP bound) (fst p) /\ ForaL (lteP bound) (snd p) /\ R (fst p) /\ R (snd p).

  Ltac extractPartition x :=
    match goal with
    | [ |- context[partition ?t ?b ] ] => set (x := partition t b)
    end.

  Definition partitionFmap(B C : kMo (List A)) : FmapiT (List A) partitionInv B C.
    intros c d u bound.
    generalize (u bound); extractPartition z; clear u.
    simpl.
    intros [v1 [v2 [v3 v4]]].
    repeat (apply conj); try assumption; apply c; assumption.
  Defined.

  Lemma partitionFmapId : FmapiId (List A) partitionInv partitionFmap.
    unfold FmapiId.
    intros B i x.
    apply functional_extensionality_dep.
    unfold partitionInv in x.
    intro bound.
    unfold partitionFmap.
    destruct (x bound) as [i1 [i2 [i3 i4]]].
    reflexivity.
  Qed.
  
  Global Instance FunPartitionFi : Functori (List A) partitionInv :=
    {fmapi := partitionFmap ; fmapiId := partitionFmapId }.

  Ltac etaFold :=
    change (fun (X0 : Set -> Set) (xmap : Functor X0) (alg0 : MuAlg (Dc.AlgF ?F) X0) =>
              fold ?F X0 xmap alg0) with (fold F).

  Lemma partitionLem(U : List A -> Prop)
    (sfo : forall d : List A, ListSFoldTi A U d)
    (l : List A)
    (sl : U l) : partitionInv U l.
    apply (sfo l partitionInv).
    + apply FunPartitionFi.
    + apply rollSAlgi; unfold SAlgF.
      intros S R up _ abstin ih d di.
      destruct di; unfold partitionInv; intro bound.
    - repeat (apply conj); try (apply Forall_nil); apply abstin;
        setoid_rewrite (abstInId (ListF A) Nil);
        apply nilFi.
    - generalize (ih t H bound).
      simpl'.
      change (sfold (ListF A) (PartitionF A) (FunPartitionF A) (PartitionSAlg A ltA) t bound)
        with (partition t bound).
      extractPartition p.
      destruct p eqn:pu; destruct (ltA h bound) eqn:hb;
        intros [iht1 [iht2 [iht3 iht4]]];
        repeat (apply conj); try assumption.
      -- apply Forall_cons; assumption.
      -- apply abstin.
         setoid_rewrite (abstInId (ListF A) (Cons h l0)).
         apply consFi ; assumption.
      -- apply up; assumption.
      -- apply Forall_cons.
         --- assumption.
         --- assumption.
      -- apply up; assumption.
      -- apply abstin.
         setoid_rewrite (abstInId (ListF A) (Cons h l1)); apply consFi; assumption.
      + exact sl.
  Qed.
  
  Definition forallPresT(xs : List A) : Prop :=
    forall (P : A -> Prop),
      ForaL P xs ->
      forall(bound : A),
        let p := partition xs bound in
        ForaL P (fst p) /\ ForaL P (snd p).

  Lemma forallPres{U : List A -> Prop}
    (fo : forall d : List A, FoldTi (Algi (ListFi A)) U d)
    (l : List A)
    (sl : U l) : forallPresT l.
    apply (fo l (Consti forallPresT)).
    + apply FunConsti.
    + apply rollAlgi.
      intros R _ _ ih d fd.
      destruct fd.
      ++ intros P u bound.
         apply conj; apply Forall_nil.
      ++ unfold Consti, forallPresT, ForaL; simpl'.
         intros P u; inversion u; clear u.
         intro bound.
         change (sfold (ListF A) (PartitionF A) (FunPartitionF A) (PartitionSAlg A ltA) t bound) with
           (partition t bound).
         generalize (ih t H P H3 bound).
         set (p := partition t bound); destruct p.
         intros [i1 i2].
         destruct (ltA h bound) eqn:e.
         +++ apply conj; [apply Forall_cons; assumption | assumption].
         +++ apply conj; [assumption | apply Forall_cons; assumption ].
    + exact sl.
  Qed.

End PartitionPfs.

(** Common tactics *)
Ltac extractPartitionr x :=
  match goal with
  | [ |- context[partitionr ?A ?ltA ?sfo ?t ?b ] ] => set (x := partitionr A ltA sfo t b)
  end.

