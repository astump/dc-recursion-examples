(** * SmallerList *)
(** Custom ordering directly on the [list] datatype.
    See Section 3.6 of paper. *)
Require Import Lists.List.

Section SmallerListWf.
  Variable A : Type.

  Inductive smallerList : list A -> list A -> Prop :=
  | sl_nil  : forall (h : A)(t : list A), smallerList nil (cons h t)
  | sl_cons : forall (h h' : A)(x y : list A), smallerList x y -> smallerList (cons h x) (cons h' y).

  Lemma accSlNil : Acc smallerList nil.
    apply Acc_intro.
    intros y uy.
    inversion uy.
  Defined.

  Lemma triple : forall(x y : list A),
      smallerList x y ->
      forall (z : list A),
        smallerList y z ->
        exists h z', z = h :: z' /\ smallerList x z'.
    intros x y p1.
    induction p1; intros z p2.
    - inversion p2.
      exists h'.
      exists y.
      apply conj.
      -- trivial.
      -- inversion H2; apply sl_nil.
    - inversion p2.
      set (ih := IHp1 y0 H2).
      destruct ih.
      destruct H3.  
      destruct H3.
      exists h'0. exists y0.
      apply conj.
      trivial.
      rewrite H3.
      apply sl_cons.
      assumption.
  Qed.
  
  Lemma nilSl : forall (x : list A)(P : Prop), smallerList x nil -> P.
    intros x P u.
    inversion u.
  Defined.

  Lemma decLem : forall(hd1 hd:A)(tl1 tl v : list A),
      smallerList (hd1 :: tl1) (hd :: tl) ->
      smallerList v (hd1 :: tl1) ->
      smallerList v tl.
    intros hd1 hd tl1 tl v s1 s2.
    set (u := triple v (hd1 :: tl1) s2 (hd :: tl) s1).
    destruct u.
    destruct H.
    destruct H.
    inversion H.                    
    assumption.
  Qed.

  (* write without tactics -- but 'dec' below runs comparably fast, so no need for this one: *)
  Fixpoint decByHand(y : list A) : forall(x : list A), smallerList x y -> Acc smallerList x :=
    match y with
      nil => fun x s => nilSl x (Acc smallerList x) s
    | hd :: tl =>
        fun x => 
          match x with
            nil => fun s => accSlNil
          | hd1 :: tl1 => fun s => Acc_intro (hd1 :: tl1) (fun v s' => decByHand tl v (decLem hd1 hd tl1 tl v s s') )
          end
    end.
  
  (* don't pattern-match on the proof that things are decreasing, or you cannot use Qed for
   such proofs 
Fixpoint dec(y : list A) : forall(x : list A), smallerList x y -> Acc smallerList x :=
  match y with
    nil => fun x s => nilSl x (Acc smallerList x) s
  | hd :: tl =>
      fun x s => 
        match s in smallerList a b return b = (hd :: tl) -> Acc smallerList a with
          sl_nil hd' tl' => fun u => accSlNil 
        | sl_cons hd1 hd2 tl1 tl2 sm => fun u =>
            Acc_intro (hd1 :: tl1) (fun v s' => dec tl v (decLem hd hd1 hd2 v tl1 tl2 tl sm s' u))
        end eq_refl
   end.
   *)

  Lemma dec : forall (y x : list A), smallerList x y -> Acc smallerList x.
    induction y; intros x.
    - intro s; apply (nilSl x); assumption.
    - destruct x eqn:e; intro s.
      -- exact accSlNil.
      -- apply Acc_intro.
         intros y1 sy1.       
         apply IHy.
         apply (decLem a0 a l y); assumption.
  Defined.

  Theorem smallerListWf : well_founded smallerList.
    unfold well_founded.
    intro a.
    apply Acc_intro.
    exact (dec a).
  Defined.

  Theorem smallerListTail : forall (t : list A)(h : A), smallerList t (h :: t).
    induction t; intro h.
    - apply sl_nil.
    - apply sl_cons.
      apply IHt.
  Qed.
  
  Theorem smallerListCons :
    forall (t' t: list A)(h : A), smallerList t t' -> smallerList t (h :: t').
    intros t'.
    induction t'; intros t h p.
    - inversion p.
    - inversion p as [|x y z q u].
      -- apply sl_nil.
      -- apply sl_cons.
         apply IHt'.
         assumption.
  Qed.  
End SmallerListWf.

