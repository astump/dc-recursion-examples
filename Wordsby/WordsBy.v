(** * WordsBy *)
(** similar to wordsBy from Haskell's #<a href="https://hackage.haskell.org/package/extra-1.7.10/docs/Data-List-Extra.html">Data.List.Extra</a>#. *)

Require Import Dc.
Require Import Kinds.
Require Import Functors.
Require Import List.List.

Require Import Coq.Lists.List.
Require Import Coq.Init.Nat.

Require Import ExtraLib.
Require Import Span.
Require Import SpanPfs.Forall.
Require Import SpanPfs.MotivePres.

Import ListNotations.

Section WordsBy.

  Variable A : Set.
  
  Definition WordsByAlg(p : A -> bool)
    : Alg (ListF A) (Const (list (list A))) :=
    rollAlg (fun R _ sfo wordsBy xs => 
       match xs with
         Nil => [] 
       | Cons hd tl =>
         if p hd then
           wordsBy tl
         else
           let (w,z) := breakr sfo p tl in
             (hd :: w) :: wordsBy z
       end).

  Definition WordsBy(p : A -> bool)(xs : List A) : list (list A) :=
    fold (ListF A) (Const (list (list A))) (FunConst (list (list A))) (WordsByAlg p) xs.

  Definition wordsBy(p : A -> bool)(xs : list A) : list (list A) :=
    WordsBy p (toList xs).

  Definition wordsByOutputsNegT(p : A -> bool)(xs : List A) : Prop :=
    Forall (Forallb (fun x => negb (p x))) (WordsBy p xs).

  Theorem wordsByOutputsNeg(p : A -> bool)(xs : list A) : wordsByOutputsNegT p (toList xs).  
  listInd A (fun (X : List A -> Prop) => wordsByOutputsNegT p) xs.
  + apply Forall_nil.
  + unfold wordsByOutputsNegT.
    simpl'.
    change (fold (ListF A) (Const (list (list A))) (FunConst (list (list A))) (WordsByAlg p) t) with (WordsBy p t).
    destruct (p h) eqn:e.
    ++ exact (ih t H).
    ++ destruct (breakr (sfold (ListF A)) p t) eqn:e'.
       apply Forall_cons.
       +++ apply Forall_cons.
           ++++ rewrite e; trivial.
           ++++ apply (spanForall fo (fun x : A => negb (p x))t H e').
       +++ apply ih.
           exact (motivePres sfo (fun x : A => negb (p x)) t H e').
Qed.

  Theorem wordsByInputNeg(p : A -> bool)(xs : list A) :
    Forallb p xs ->
    WordsBy p (toList xs) = nil.
    induction xs; intro H.
    - simpl'; trivial.
    - simpl'.
      inversion H.
      destruct (p a) eqn:e.
      -- exact (IHxs H3).
      -- discriminate H2.
   Qed.

End WordsBy.

Arguments wordsBy{A}.
Arguments WordsBy{A}.


(* testcases *)

(* 0 will play the role of a space *)
(*
Definition t1 := repeat 1 5.
Definition t2 := repeat 0 5.

Eval compute in (wordsByl (Nat.eqb 0) (t1 ++ t2 ++ t1 ++ t2)).
*)
