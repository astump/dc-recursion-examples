(** * Well-Founded Run-Length Encoding *)
Require Import Coq.Lists.List Coq.Init.Nat Psatz.
Require Import List.ExtraLib.

Require Import MapThroughWf.
Require Import Span.
Require Import Wordsby.WordsByWf. (* for span *)

Import ListNotations.

Section RLE.

  Context {A : Set}.
  Variable eqb : A -> A -> bool.
  Variable eq : forall a1 a2, eqb a1 a2 = true -> a1 = a2.
  Variable eqRefl : forall a , eqb a a = true.

  Definition compressSpanWf : mappedT A (nat * A).
    intros hd tl.
    destruct (span A (eqb hd) tl) as (p, s) eqn:e.
    apply pair.
    exact (succ (length p), hd).
    apply (exist _ s).    
    exact (span_snd_smaller A (eqb hd) tl p s e).
  Defined.

  Definition rleWf(xs : list A) : list (nat * A)
    := mapThroughWf compressSpanWf xs.

End RLE.

(* testcases *)

Definition test := rleWf eqb (1 :: 1 :: 1 :: 2 :: 2 :: 3 :: 3 :: 3 :: 3 :: 4 :: 5 :: 5 :: []).

(*Eval compute in test.*)


