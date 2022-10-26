(** * ExtraLib *)
(** Commonly used definitions & theorems. *)
Require Import PeanoNat.
Require Import Coq.Lists.List.

Fixpoint lt_false_lte(a b : nat) : a <? b = false -> b <=? a = true.
  intro u.
  destruct a , b ; try reflexivity.
  inversion u.
  change (S a <? S b) with (a <? b) in u.
  change (S b <=? S a) with (b <=? a).
  exact (lt_false_lte a b u).
Qed.

Lemma Forall_append :
  forall(A : Set)(l1 l2 : list A)(p : A -> Prop),
    Forall p l1 -> Forall p l2 ->
    Forall p (l1 ++ l2).
  intros A l1 l2 p.
  induction l1.
  + intros u1 u2. exact u2.
  + intros u1 u2. 
    inversion u1.
    apply Forall_cons.
    - exact H1.
    - apply IHl1; assumption.
Qed.

Theorem Forall_imp : forall {A : Set}{l : list A}(P P' : A -> Prop),
    Forall P l ->
    (forall x : A, P x -> P' x) ->
    Forall P' l.
  intros a l P P' u.
  induction u.
  + intros _; apply Forall_nil.
  + intro impp; apply Forall_cons.
    ++ apply impp; assumption.
    ++ apply (IHu impp).
Qed.

Definition Forallb{A : Set}(p:A -> bool)(xs : list A) : Prop := Forall (fun a => p a = true) xs.

Lemma Foralleqb{A : Set}(eqb:A -> A -> bool)(eq:forall(a a' : A), eqb a a' = true -> a = a')
      (a : A)(xs : list A) : Forallb (eqb a) xs -> xs = repeat a (length xs) .
  induction xs; simpl.
  - trivial.
  - intro u.
    inversion u.
    rewrite (eq a a0 H1) in *.
    rewrite <- (IHxs H2).
    reflexivity.
Qed.

Lemma Foralleqb2{A : Set}(eqb:A -> A -> bool)(eqRefl:forall(a : A), eqb a a = true)
      (a : A)(n : nat) : Forallb (eqb a) (repeat a n).
  induction n.
  + apply Forall_nil.
  + apply Forall_cons.
    ++ apply eqRefl.    
    ++ fold (repeat a n).
       apply IHn.
Qed.

Lemma hopRepeat : forall{A : Set} (n : nat)(a : A)(xs : list A),
    a :: repeat a n ++ xs = repeat a n ++ a :: xs.
  intros. induction n; simpl.
  - reflexivity.
  - rewrite IHn. reflexivity.
Qed.

Definition liftRel{A:Set}(r:A -> A -> bool)(x y : A) : Prop := r x y = true.
Definition liftRelneg{A:Set}(r:A -> A -> bool)(x y : A) : Prop := r x y = false.

Definition isNil{A : Set}(l : list A) : bool :=
  match l with
    nil => true
  | cons _ _ => false
  end.

Section Merge.
  Variable A : Set.
  Variable leq : A -> A -> bool.
  
  (** This def'n is stolen (modulo alpha-eqeuivalence) from Coq.Sorting.MergeSort. *)
  
  Fixpoint merge(xs ys : list A) :=
    let fix merge_aux ys :=
        match xs, ys with
        | nil, _ => ys
        | _, nil => xs
        | x :: xs', y :: ys' =>
          if leq x y then x :: merge xs' ys else y :: merge_aux ys'
        end
    in merge_aux ys.
End Merge.

Arguments merge {A} leq xs ys.
