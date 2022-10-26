(** * Harper's Matcher Regular Expression Inductive Datatype *)

Require Import Coq.Strings.Ascii.
Require Import List.List.

Definition Char   : Set := ascii.
Definition string : Set := list Char.
Definition String : Set := List Char.

Inductive Regex : Set :=
  NoMatch   : Regex
| MatchChar : Char  -> Regex
| Or        : Regex -> Regex -> Regex
| Plus      : Regex -> Regex
| Concat    : Regex -> Regex -> Regex.

