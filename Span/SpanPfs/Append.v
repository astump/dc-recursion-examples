(** * Span -- Append Proofs *)
(** prove that appending the lists returned by Span gives the original list *) 

Require Import Dc.
Require Import Dci.
Require Import Kinds.
Require Import Functors.
Require Import List.List.
Require Import Span.Span.

Require Import Coq.Lists.List.
Require Import Coq.Init.Nat.

Import ListNotations.

Section Append.
Variable A : Set.
Variable eqb : A -> A -> bool.

Definition SpanAppendF(p : A -> bool)(xs : List A) : Prop :=
  forall (l : list A)(r : List A) ,
    span p xs = (l,r) ->
    fromList xs = l ++ (fromList r).

Lemma SpanAppend(p : A -> bool) : ListAlgi A (Consti (SpanAppendF p)) .
  apply rollAlgi.
  intros R _ _ ih xs fxs l r.
  destruct fxs. 
  + intro e; inversion e; trivial.
  + change (fromList (mkCons h t)) with (h :: fromList t).
    unfold span,spanr; simpl'.
    destruct (p h) eqn:e.
    ++ foldSpan. 
       destruct (span p t) eqn:e'; intro u; inversion u as [(u1, u2)]; clear u.
       +++ set (ih1 := ih t H l0 l1).
       unfold span,spanr in ih1.
       unfold span, spanr in e'.       
       rewrite e' in ih1.
       rewrite (ih1 eq_refl).      
       rewrite u2.
       reflexivity.
    ++ intro u; inversion u as [(u1,u2)].
       reflexivity.
Qed.

Definition spanAppend{R : List A -> Prop}(foi:forall d : List A, ListFoldTi R d)
           (p : A -> bool)(xs : List A)(rxs : R xs) : SpanAppendF p xs :=
  foi xs (Consti (SpanAppendF p)) (FunConsti (SpanAppendF p)) (SpanAppend p) rxs.

End Append.

Arguments spanAppend{A}{R} foi p xs rxs {l}{r}.
