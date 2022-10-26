(** * Harper's Regular Expression Matcher *)
(* Coq *)
Require Import Bool.

(* Ours *)
Require Import Regex.
Require Import ExtraLib.
Require Import List.List.
Require Import Dc.Functors.
Require Import Dc.Dc.

Definition K(T      : Set) : Set := T -> bool.
Definition MatchT(T : Set)       := K T -> bool.

Definition matchi(T : Set)(matcher : T -> Regex -> MatchT T)
  : Regex -> Ascii.ascii -> T -> MatchT T :=
  fix matchi (r : Regex) : Ascii.ascii -> T -> MatchT T :=
  match r with 
    NoMatch =>
    fun c cs k => false 
  | MatchChar c' =>
    fun c cs k =>
      if (Ascii.eqb c c') then k cs else false 
  | Or r1 r2 =>
    fun c cs k =>
      (matchi r1 c cs k) || (matchi r2 c cs k)
  | Plus r =>
    fun c cs k =>
      matchi r c cs
             (fun cs => (k cs) || (matcher cs (Plus r) k))
  | Concat r1 r2 =>
    fun c cs k =>
      matchi r1 c cs
             (fun cs' => matcher cs' r2 k)
  end.

(** Matcher carrier *)
Definition MatcherF(X : Set) := Regex -> MatchT X.
Definition fmapMatcher{U V : Set} : FmapT U V MatcherF.
  intros f d.
  intros r k.
  apply (d r).
  intro s.
  exact (k (f s)).
Defined.

Definition fmapMatcherId : FmapId MatcherF (@fmapMatcher).
  intros X d.
  reflexivity.
Defined.

Global Instance funMatcher : Functor MatcherF :=
  { fmap := (@fmapMatcher) ;
    fmapId := fmapMatcherId }.

(** Matcher algebra *)
Definition matcherAlg : ListAlg Char MatcherF :=
  rollAlg
    (fun R fo sfo matcher s =>  
       match s with
         Nil =>
         fun r k => false
       | Cons c cs =>
         fun r k =>
           matchi R matcher r c cs k
       end).

Definition matcherh(r : Regex)(s : String) : MatchT String :=
  fold (ListF Char) MatcherF funMatcher matcherAlg s r.

Definition matcher(r : Regex)(s : string) : bool :=
  matcherh r (toList s) (fun s => isNil (fromList s)).
