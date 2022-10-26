(** * Well-Founded Quicksort *)

(* Coq *)
Require Import Program Coq.Lists.List Psatz.
Require Import PeanoNat.
Local Open Scope list_scope.

Section QSort.

  Variable A : Type.
  Variable ltA : A -> A -> bool.

  Fixpoint partition (l:list A)(bound : A) : list A * list A :=
    match l with
    | nil => (nil, nil)
    | x::xs =>
      let (l,r) := partition xs bound in
        if ltA x bound then
          (x::l,r)
        else
          (l,x::r)
    end.

    Lemma partition_smaller (bound:A)(xs:list A) :
      forall (l r : list A), partition xs bound = (l , r) ->
      Datatypes.length l <= Datatypes.length xs /\
      Datatypes.length r <= Datatypes.length xs.
    Proof.
      induction xs as [ |a l IHl]; auto; intros l1 l2; simpl.
      - intro H; inversion H. apply conj; reflexivity.
      - destruct (partition l bound) eqn:e.
        set (i := IHl l0 l3 eq_refl); destruct i as [i1 i2].
        case (ltA a bound); intro H; inversion H; apply conj; simpl.
        -- apply le_n_S. assumption.
        -- apply le_S.
           congruence.
        -- apply le_S. congruence.
        -- apply le_n_S; assumption.
    Qed.

  Program Fixpoint quicksortWf (xs:list A) {measure (Datatypes.length xs)} : list A :=
    match xs with
    | nil => nil
    | x::xs' =>
      let '(l,r) := partition xs' x in
        quicksortWf l ++ x :: quicksortWf r
    end.
  Next Obligation.
    set (u := partition_smaller x xs' l r (eq_sym Heq_anonymous)); destruct u.
    simpl. apply Nat.lt_succ_r; assumption.
  Qed.
  Next Obligation.
    set (u := partition_smaller x xs' l r (eq_sym Heq_anonymous)); destruct u.
    simpl. apply Nat.lt_succ_r; assumption.    
  Qed.

(*
  Print quicksortWf. (* 55 *)
  Print quicksortWf_obligation_3. (* 2 *)
  Print quicksortWf_obligation_2. (* 21 *)
  Print quicksortWf_obligation_1. (* 21 *)
  *)
  
End QSort.

Arguments quicksortWf {A}.

