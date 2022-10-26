(** * CastAlg *)
(** Cast from one algebra to another, parametrically over any Endofunctor [X]. *)

Require Import Kinds.

Definition CastAlg(alg1 alg2 : KAlg) :=
  forall (X : Set -> Set), alg1 X -> alg2 X.

