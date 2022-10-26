(** * Run-Length Encoding *)
(* Coq *)
Require Import Coq.Lists.List.
Require Import Coq.Init.Nat.
Import ListNotations.

(* Ours *)
Require Import Dc.
Require Import Dci.
Require Import Kinds.
Require Import Mu.
Require Import List.List.
Require Import Functors.
Require Import List.ExtraLib.
Require Import MapThrough.
Require Import Span.
Require Import Rld.
Require Import SpanPfs.Forall.
Require Import SpanPfs.MotivePres.
Require Import SpanPfs.Append.

(** We have a naming conflict between Coq.Lists.List.length and (our)
List.List.length... but we want to use the former, here. *)
Local Notation length := Coq.Lists.List.length.

Section RLE.
  
  Context {A : Set}.
  Variable eqb : A -> A -> bool.
  Variable eq : forall a1 a2, eqb a1 a2 = true -> a1 = a2.

  Definition compressSpan : mappedT A (nat * A) :=
    fun R sfo hd tl => 
      let (p, s) := spanr sfo (eqb hd) tl in
         ((succ (length p), hd), s).

  Definition RleCarr := Const (list (nat * A)).
  Definition RleAlg : ListAlg A RleCarr :=
    MapThroughAlg compressSpan.

  Definition Rle(xs : List A) : list (nat * A)
    := fold (ListF A) RleCarr (FunConst (list (nat * A))) RleAlg xs.
  Definition rle(xs : list A) : list (nat * A)
    := Rle (toList xs).

Theorem RldRle (xs : list A): rld (Rle (toList xs)) = xs.  
  listInd A (fun (X : List A -> Prop) xs => rld (Rle xs) = fromList xs) xs.
  + trivial.
  + unfold rle, rle; simpl'. unfold compressSpan.
   destruct (spanr (sfold (ListF A)) (eqb h) t) as (p,s) eqn:e.
   fold (Rle s).
   simpl.
   rewrite (ih s (motivePres sfo (eqb h) t H e)).
   rewrite <- (Foralleqb eqb eq h p (spanForall fo (eqb h) t H e)).
   rewrite <- (spanAppend fo (eqb h) t H e).
   trivial.
Qed.
End RLE.

(* testcases *)

(* Definition test := rle eqb (1 :: 1 :: 1 :: 2 :: 2 :: 3 :: 3 :: 3 :: 3 :: 4 :: 5 :: 5 :: []). *)

(*Eval compute in test.*)


