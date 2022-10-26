(* Coq *)
Require Import Coq.Lists.List.
Require Import Coq.Init.Nat.
Import ListNotations.

(* Ours *)
Require Import Rle.
Require Import Rld.

(* Sample rle executions *)
Eval compute in rle eqb [1 ; 1 ; 1 ; 2 ; 2 ; 3 ; 3 ; 3 ; 3 ; 4 ; 5 ; 5 ].
Eval compute in rle eqb [5 ; 4 ; 3 ; 2 ; 1].
Eval compute in rle eqb [5 ; 5 ; 4 ; 3 ; 4 ; 2 ; 1 ; 1].

(* Sample rld executions *)
Eval compute in rld [(3, 1); (2, 2); (4, 3); (1, 4); (2, 5)].
Eval compute in rld [(1, 5); (1, 4); (1, 3); (1, 2); (1, 1)].
Eval compute in rld [(2, 5); (1, 4); (1, 3); (1, 4); (1, 2); (2, 1)].

