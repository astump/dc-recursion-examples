(** * Span -- Forall Proofs *)
(** prove that all elements in the first list returned by span satisfy the predicate *) 

Require Import Dc.
Require Import Dci.
Require Import Kinds.
Require Import Functors.
Require Import List.List.
Require Import List.ExtraLib.
Require Import Span.Span.

Require Import Coq.Lists.List.
Require Import Coq.Init.Nat.

Import ListNotations.

Section spanForall.

Variable A : Set.
Variable eqb : A -> A -> bool.

Definition SpanForallF(p : A -> bool)(xs : List A) : Prop :=
  forall (l : list A)(r : List A),
    span p xs = (l,r) ->
    Forallb p l.

Lemma SpanForall(p : A -> bool) : ListAlgi A (Consti (SpanForallF p)) .
  apply rollAlgi.
  intros R _ _ ih xs fxs l r .
  destruct fxs.
  + intro e; inversion e; apply Forall_nil.
  + unfold span, spanr. simpl'.
    foldSpan.
    destruct (p h) eqn:e.
    ++ destruct (span p t) eqn:e'; intro u; inversion u as [(u1,u2)]; clear u; apply Forall_cons; try assumption.
       +++ set (i := ih t H l0 l1).
           rewrite e' in i.
           apply i.
           reflexivity.
    ++ intro u; inversion u; apply Forall_nil.
Qed.

Definition spanForall{R : List A -> Prop}(foi:forall d : List A, ListFoldTi R d)
           (p : A -> bool)(xs : List A)(rxs : R xs) : SpanForallF p xs :=
  foi xs (Consti (SpanForallF p)) (FunConsti (SpanForallF p)) (SpanForall p) rxs.


Definition spanForall2F(p : A -> bool)(xs : List A) : Prop :=
  Forallb p (fromList xs) ->
  span p xs = (fromList xs, getNil xs).

Lemma SpanForall2(p : A -> bool) : ListAlgi A (Consti (spanForall2F p)) .
  apply rollAlgi.
  intros R fo sfo ih xs fxs .
  destruct fxs as [|h t rt].
  + intro u; trivial.
  + intro u.
    change (fromList (mkCons h t)) with (h :: fromList t) in *.
    inversion u as [|h' t' ph' u'].
    unfold span, spanr.
    rewrite (getNilCons sfo t rt h).
    simpl'; rewrite ph'.
    foldSpan.
    rewrite (ih t rt u').
    reflexivity.
Qed.

Definition spanForall2{R : List A -> Prop}(foi:forall d : List A, ListFoldTi R d)
           (p : A -> bool)(xs : List A)(rxs : R xs) : spanForall2F p xs :=
  foi xs (Consti (spanForall2F p)) (FunConsti (spanForall2F p)) (SpanForall2 p) rxs.

End spanForall.

Arguments spanForall{A}{R} foi p xs rxs {l}{r}.
Arguments spanForall2{A}{R}.
