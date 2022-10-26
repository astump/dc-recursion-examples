(** * Span *)
(** similar to span from Haskell's <a
href="https://hackage.haskell.org/package/base-4.16.1.0/docs/Data-List.html">Data.List</a>,
but written as an [Alg]. *)

(* Coq *)
Require Import Coq.Lists.List.
Import ListNotations.

(* Ours *)
Require Import Dc.
Require Import Kinds.
Require Import Functors.
Require Import List.List.

Section Span.
  Variable A : Set.
  Variable eqb : A -> A -> bool.
    
  Definition SpanF(X : Set) : Set := list A * X.

  Definition spanFmap{Y Z : Set} : FmapT Y Z SpanF :=
  fun f c =>
    let (x , y) := c in
    (x, f y).

  Lemma SpanFunctorId : FmapId SpanF (@spanFmap).
    intros B d.
    destruct d; trivial.
  Qed.

  Global Instance SpanFunctor : Functor SpanF :=
    {
     fmap := (@spanFmap);
     fmapId := SpanFunctorId
    }.
  
  Definition SpanSAlg(p : A -> bool)
    : ListSAlg A SpanF :=
    rollSAlg 
      (fun P R up sfo abstIn span xs => 
         match xs with
           Nil => ([], abstIn xs)
         | Cons x xs' =>
           if p x
           then let (r,s) := span xs' in (x :: r, up s)
           else ([], abstIn xs)
         end).

  Definition spanr{R : Set}(sfo:ListSFoldT A R)
                  (p : A -> bool)(xs : R) : SpanF R :=
    sfo SpanF SpanFunctor (SpanSAlg p) xs.

  Definition span(p : A -> bool)(xs : List A) : SpanF (List A) :=
    spanr (sfold (ListF A)) p xs.

  (** intended just for testing below *)
  Definition spanl(p : A -> bool)(xs : list A) : list A * list A :=
    let (l,r) := span p (toList xs) in
      (l,fromList r).

  Definition dropWhiler{R : Set}(sfo:ListSFoldT A R)
             (p : A -> bool)(xs : R) : R :=
    snd (spanr sfo p xs).

  Definition dropWhile(p : A -> bool)(xs : List A) : List A :=
    dropWhiler (sfold (ListF A)) p xs.

  Definition breakr{R : Set}(sfo : ListSFoldT A R)
             (p : A -> bool)(xs : R) : list A * R :=
    (spanr sfo (fun x => negb (p x)) xs).

  Definition break(p : A -> bool)(xs : List A) : list A * List A :=
    breakr (sfold (ListF A)) p xs.

End Span.

Arguments spanr{A}{R}.
Arguments span{A}.
Arguments dropWhiler{A}{R}.
Arguments dropWhile{A}.
Arguments breakr{A}{R}.
Arguments break{A}.

(** Common tactics *)
Ltac foldSpan :=
  repeat (match goal with
  | |- context[sfold ?F ?SF ?SFun (SpanSAlg ?A ?p) ?t] =>
    change (sfold F SF SFun (SpanSAlg A p) t) with (span p t)
  end).

(* testcases 

Definition test := spanl nat (eqb 1) (1 :: 1 :: 2 :: 2 :: 1 :: 3 :: 5 :: []).
Definition test2 := spanl nat (eqb 0) (1 :: 1 :: 2 :: 2 :: 1 :: 3 :: 5 :: []).
Definition test3 := spanl nat (eqb 0) (0 :: 0 :: 0 :: []).

Eval compute in test.
Eval compute in test2.
Eval compute in test3.
*)
