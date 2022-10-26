(** * Well-Founded Wordsby *)

(**
Implementation of [wordsBy] using well-founded recursion with different measure-functions.

- [wordsByP]: well-founded recursion on length of list.
- [wordsByPl]: well-founded recursion directly on the list
- [wordsByPn]: well-founded recursion on length of list, but using a different proof of well-foundedness             
             that avoids evaluating the measure function (the length) as we recurse into the
             proof of [Acc] for the initial input.
*)
Require Import Program Coq.Lists.List Psatz.
Require Import SmallerListWf.
Require Import NatWf.

From Coq Require Import Recdef.

Local Open Scope list_scope.

Section Span.

  Variable A : Type.

  Section Span.
    Variable p : A -> bool.

    Fixpoint span (l : list A) : list A * list A :=
      match l with
      | nil => (nil, nil)
      | x::xs => if p x then let (ys, zs) := span xs in (x::ys, zs) else (nil, l)
      end.

    Lemma span_snd_smaller (l:list A) :
      forall(w z : list A),
        span l = (w,z) -> 
        length z <= length l.
    Proof.
      induction l as [ |a l IHl]; auto; simpl; intros w z.
      + intro u; injection u as u1 u2. rewrite <- u2; reflexivity.
      + destruct (p a) eqn:e; destruct (span l) eqn:e'; intro u; injection u as u1 u2.
        - set (i := IHl l0 l1 eq_refl). rewrite u2 in i. lia.
        - rewrite <- u2. simpl. lia.
    Qed.

    Lemma span_snd_smallerList (tl:list A) :
      forall(hd : A)(w z : list A),
        span tl = (w,z) -> 
        smallerList A z (hd :: tl).
    Proof.
      induction tl as [ |a tl IH]; auto; simpl; intros hd w z.
      + intro u; injection u as u1 u2. rewrite <- u2.  apply sl_nil.
      + destruct (p a) eqn:e; destruct (span tl) eqn:e'; intro u; injection u as u1 u2.
        - set (i := IH a l l0 eq_refl). rewrite u2 in i. apply smallerListCons; assumption.
        - rewrite <- u2. apply smallerListTail.
    Qed.

  End Span.

  Definition break(p : A -> bool) := span (fun a => negb (p a)).

  Variable p : A -> bool.

  Function wordsByF (l:list A)
          { measure length l } : list (list A) :=
    match l with
    | nil => nil
    | hd::tl =>
        if p hd then
          wordsByF tl
        else
          let (w,v) := break p tl in
            (hd::w)::(wordsByF v)
    end.
    + intros; simpl; lia.
    + intros. simpl. apply Lt.le_lt_n_Sm. unfold break in teq1.
      apply (span_snd_smaller (fun x => negb (p x)) tl w v); assumption.
    Defined.

(*
  Print wordsByF. (* 1 *)
  Print wordsByF_terminate. (* 207 *)
*)

  Obligation Tactic := idtac.
  
  Program Fixpoint wordsByP (l:list A)
          { measure (length l) } : list (list A) :=
    match l with
    | nil => nil
    | hd::tl =>
        if p hd then
          wordsByP tl
        else
          let '(w,z) := break p tl in
            (hd::w)::(wordsByP z)
    end.
  Next Obligation.
    program_simpl.
  Qed.
  Next Obligation.
    program_simpl.
    simpl. apply Lt.le_lt_n_Sm. apply (span_snd_smaller (fun x => negb (p x)) tl w z).
    fold (break p).
    rewrite Heq_anonymous.    
    reflexivity.
  Qed.
  Next Obligation.
    program_simpl.
  Defined.

(*
  Print wordsByP. (* 40 *)
  Print wordsByP_obligation_1. (* 7 *)
  Print wordsByP_obligation_2. (* 11 *)
  Print wordsByP_obligation_3. (* 2 *)

(*  Print Wf_nat.well_founded_ltof. *)

  *)

  Program Fixpoint wordsByPl (l:list A)
          { measure l (smallerList A) } : list (list A) :=
    match l with
    | nil => nil
    | hd::tl =>
        if p hd then
          wordsByPl tl
        else
          let '(w,z) := break p tl in
            (hd::w)::(wordsByPl z)
    end.
  Next Obligation.
    program_simpl.
    exact (smallerListTail A tl hd).
  Qed.
  Next Obligation.
    program_simpl.
    unfold break in *|-*.
    apply (span_snd_smallerList (fun a => negb (p a)) tl hd w z).
    congruence.
  Qed.
  Next Obligation.
    unfold MR.
    exact (smallerListWf A).
  Defined.

  Program Fixpoint wordsByPn (l:list A)
          { measure l (ltof (list A) (@length A))  } : list (list A) :=
    match l with
    | nil => nil
    | hd::tl =>
        if p hd then
          wordsByPn tl
        else
          let '(w,z) := break p tl in
            (hd::w)::(wordsByPn z)
    end.
  Next Obligation.
    unfold ltof. program_simpl.
  Qed.
  Next Obligation.
    unfold ltof. program_simpl.
    simpl. apply Lt.le_lt_n_Sm. apply (span_snd_smaller (fun x => negb (p x)) tl w z).
    fold (break p).
    rewrite Heq_anonymous.    
    reflexivity.
  Qed.
  Next Obligation.
    program_simpl.
    apply Wf_ltf.
  Defined.

  Lemma l1 : 
forall (l : list A) (hd : A) (tl : list A),
  l = hd :: tl -> p hd = true -> ltof (list A) (length (A:=A)) tl (hd :: tl).
    intros; unfold ltof; simpl; lia.
    Qed.

  Lemma l2 :
  forall (l : list A) (hd : A) (tl : list A),
  l = hd :: tl ->
  p hd = false -> forall w v : list A, break p tl = (w, v) -> ltof (list A) (length (A:=A)) v (hd :: tl).
  intros; unfold ltof; simpl. apply Lt.le_lt_n_Sm. unfold break in H1.
  apply (span_snd_smaller (fun x => negb (p x)) tl w v); assumption.
  Qed.


  (* use the more efficient version of well-foundedness *)
  Function wordsByFn (l:list A)
          { wf (ltof (list A) (@length A)) l } : list (list A) :=
    match l with
    | nil => nil
    | hd::tl =>
        if p hd then
          wordsByFn tl
        else
          let (w,v) := break p tl in
            (hd::w)::(wordsByFn v)
    end.
    + exact l1.
    + exact l2.
    + exact (Wf_ltf (list A) (@length A)).
    Defined.

End Span.

Arguments wordsByP {A} p l.
Arguments wordsByPl {A} p l.
Arguments wordsByPn {A} p l.
Arguments wordsByF {A} .
Arguments wordsByFn {A} .

(*Eval compute in (wordsByF (Nat.eqb 0) (0 :: 1 :: 1 :: 2 :: 0 :: 1 :: 3 :: 5 :: 0 :: nil)).*)

(*
Eval compute in (wordsByP (Nat.eqb 0) (0 :: 1 :: 1 :: 2 :: 0 :: 1 :: 3 :: 5 :: 0 :: nil)).

Definition t1 := repeat 0 1000.

Eval compute in (wordsByP (Nat.eqb 0) (t1 ++ 1 :: 1 :: 2 :: (t1 ++ 1 :: 3 :: 5 :: 0 :: nil))).
*)

(*
Print wordsByP.
Print wordsByP_obligation_3.
*)
