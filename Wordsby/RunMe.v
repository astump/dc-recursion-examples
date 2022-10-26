(* Coq *)
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.

Open Scope string_scope.

(* Ours *)
Require Import WordsBy.

Definition t1 := repeat "A" 5.
Definition t2 := repeat " " 4.
Definition t3 := repeat "B" 3.
Definition t4 := repeat " " 2.
Definition t5 := repeat "C" 1.

(* We calculate wordsBy "AAAAA    BBB  C". The result should
give us back the list of strings ["AAAAA","BBB", "C"]. *)
Eval compute in (wordsBy (String.eqb " ") (t1 ++ t2 ++ t3 ++ t4 ++ t5)).
