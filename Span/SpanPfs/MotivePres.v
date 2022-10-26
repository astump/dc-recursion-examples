(** * Span Motive Preservation *)
(** prove that appending the lists returned by Span gives the original list *) 

Require Import Dc.
Require Import Dci.
Require Import Mui.
Require Import Kinds.
Require Import Functors.
Require Import List.List.
Require Import Span.Span.

Require Import Coq.Lists.List.
Require Import Coq.Init.Nat.

Import ListNotations.

Section MotivePres.

Variable A : Set.
Variable eqb : A -> A -> bool.

Definition MotivePresF(p : A -> bool)(S : List A -> Prop)(xs : List A) : Prop :=
  forall (l : list A)(r : List A),
    span p xs = (l,r) ->
    S r.

Definition MotivePresFun(p : A -> bool){X Y : List A -> Prop} : FmapiT (List A) (MotivePresF p) X Y.
  intros f xs gxs l r u.
  apply f.
  exact (gxs l r u).
Defined.

Lemma MotivePresFunId(p : A -> bool) : FmapiId (List A) (MotivePresF p) (@MotivePresFun p).
  intros Q d fd.
  reflexivity.
Qed.

Global Instance MotivePresFunctor(p : A -> bool) : Functori (List A) (MotivePresF p) :=
  { fmapi := @MotivePresFun p ;
    fmapiId := MotivePresFunId p }.

Lemma MotivePresh(p : A -> bool) : ListSAlgi A (MotivePresF p) .
  apply rollSAlgi.
  intros S R up _ abstIn ih xs fxs .
  destruct fxs; intros l r; simpl'; foldAbstIn.
  + intro u; injection u as u1 u2.
    rewrite <- u2.
    apply abstIn.    
    apply nilFi.
  + foldSpan.
    destruct (p h) eqn:e.
    ++ destruct (span p t) eqn:e2;    
         intro u;
         injection u as u1 u2; rewrite <- u2.
       +++ set (i := ih t H l0 l1 e2).
           exact (up l1 i).
    ++ intro u; injection u as u1 u2; rewrite <- u2.
       apply abstIn.
       apply consFi.
       assumption.
Qed.

Definition motivePres{R : List A -> Prop}(sfoi:forall d : List A, ListSFoldTi A R d)
                    (p : A -> bool)(xs : List A)(rxs : R xs) : MotivePresF p R xs
 := sfoi xs (MotivePresF p) (MotivePresFunctor p) (MotivePresh p) rxs.

End MotivePres.

Arguments motivePres {A} {R} sfoi p xs rxs {l}{r}.
