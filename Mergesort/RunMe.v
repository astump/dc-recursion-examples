(* Coq *)
Require Import Coq.Lists.List.
Require Import Coq.Init.Nat.
Import ListNotations.

(* Ours *)
Require Import Mergesort.
Open Scope string_scope.

(* Sort [ 5 ; 3 ; 0 ; 1 ; 4 ] *)
Eval compute in [ 5 ; 3 ; 0 ; 1 ; 4 ].
Eval compute in mergeSort ltb ([ 5 ; 3 ; 0 ; 1 ; 4 ]).

Eval compute in mergeSort ltb [0 ; 1].

(* Sort big list *)
Eval compute in (mergeSort ltb 
(58 :: 33 :: 82 :: 73 :: 84 :: 31 :: 40 :: 48 :: 90 :: 77 :: 72 :: 92 :: 66 :: 11 :: 10 :: 79 :: 69 :: 25 :: 74 :: 24 :: 9 :: 91 :: 16 :: 83 :: 27 :: 39 :: 42 :: 3 :: 93 :: 46 :: 87 :: 2 :: 86 :: 65 :: 44 :: 18 :: 63 :: 67 :: 4 :: 78 :: 95 :: 19 :: 61 :: 55 :: 54 :: 21 :: 36 :: 22 :: 34 :: 52 :: 81 :: 76 :: 57 :: 43 :: 1 :: 71 :: 12 :: 80 :: 47 :: 14 :: 41 :: 32 :: 28 :: 88 :: 29 :: 94 :: 89 :: 13 :: 15 :: 49 :: 60 :: 50 :: 5 :: 17 :: 38 :: 96 :: 56 :: 8 :: 70 :: 20 :: 51 :: 62 :: 64 :: 37 :: 97 :: 6 :: 23 :: 53 :: 30 :: 99 :: 68 :: 7 :: 98 :: 59 :: 35 :: 45 :: 100 :: 85 :: 26 :: 75 :: nil)).
