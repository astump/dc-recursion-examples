(* Coq *)
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Import ListNotations.

Open Scope char_scope.

(* Ours *)
Require Import Matcher.
Require Import Regex.

Definition a : Regex := MatchChar "a".
Definition b : Regex := MatchChar "b".
Definition c : Regex := MatchChar "c".


(* We are matching the pattern ((a | b) | c) against: "abc", "a", "b", and "c". *)
Eval compute in matcher (Or (Or a b) c) [ "a" ; "b" ; "c" ].
Eval compute in matcher (Or (Or a b) c) [ "a" ].
Eval compute in matcher (Or (Or a b) c) [ "b" ].
Eval compute in matcher (Or (Or a b) c) [ "c" ].
