(** * The List Datatype *)
(** We define the recursive type [List] from its signature functor [ListF], as
 well as how to cast from the regular inductive datatype [list] to [List] and
 vice versa. *)

Require Import Dc.
Require Import Dci.
Require Import Kinds.
Require Import Functors.
Require Import Mu.

Require Import Coq.Lists.List.
Require Import Coq.Init.Nat.

Require Import Coq.Logic.FunctionalExtensionality.

Require Import Functorializer.

Import ListNotations.

Module List.
  Section _List.
    Variable A : Set.

    (** The [List] signature functor. *)

    Inductive ListF(X : Set) : Set :=
    | Nil : ListF X
    | Cons : A -> X -> ListF X.

    Arguments Nil {X}.
    Arguments Cons {X} a r.

    Global Instance FunListF : Functor ListF :=
      {fmap :=
         fun R1 R2 f xs
         => match xs with
           | Nil => Nil
           | Cons hd tl => Cons hd (f tl)
           end;
       fmapId := fun A xs => match xs with Nil => eq_refl | Cons _ _ => eq_refl end
      }.

    (** The [List] datatype. *)
    Definition List := Dc ListF.

    (** Constructors. *)
    Definition inList : ListF List -> List := inDc ListF.
    Definition outList : List -> ListF List := out ListF (sfold ListF).
    Definition mkNil : List := inList Nil.
    Definition mkCons (hd : A) (tl : List) : List := inList (Cons hd tl).

    Fixpoint listFold(l : list A){X : Set}(alg : ListF X -> X) : X :=
      match l with
        nil => alg Nil
      | cons hd tl => alg (Cons hd (listFold tl alg))
      end.

    Definition ListFoldT(R : Set) : Set :=
      FoldT (Alg ListF) R.

    Definition ListSFoldT(R : Set) : Set :=
      FoldT (SAlg ListF) R.

    (** (list A) => List A injection. *)
    Definition toList (xs : list A) : List := listFold xs (inDc ListF).
    Definition fromListr{R : Set}(fo:ListFoldT R) : R -> list A :=
      fo (Const (list A)) (FunConst (list A))
         (rollAlg (fun R fo sfo rec fr => match (fmap rec fr) with Nil => [] | Cons hd tl => hd :: tl end)) .
    Definition fromList : List -> list A := fromListr (fold ListF).
  End _List.
End List.

(** Or we can derive all definitions automatically  *)
MetaCoq Run (gen_functor list "ListF" fst_upper).
Definition gen_listF_defs :=
  gen_functor_defs_named list ListF "Listmap" "ListmapId" "FunListF" "List"
                    "inList" "outList" "listFold" "ListFoldT" "ListSFoldT"
                    "toList" "fromListr" "fromList".

MetaCoq Run (gen_listF_defs).

Arguments Nil {A} {X}.
Arguments Cons {A} {X} a r : rename.

Arguments mkNil {A}.
Arguments mkCons {A}.

Arguments inList {A}.
Arguments outList {A}.
Arguments toList {A} xs.
Arguments fromListr {A}{R}.
Arguments fromList {A} xs.

Section ListProperties.
  Variable A : Set.
  (** Despite noncanonicity, some expected properties of constructors hold.             *)
  Lemma nilCons : forall(h : A)(t : List A), mkNil = mkCons h t -> False.
    intros h t u.
    assert (c : outList mkNil = outList (mkCons h t)).
    + rewrite u; reflexivity.    
    + discriminate c.    
  Qed.

  Lemma consCons : forall(h1 h2 : A)(t1 t2 : List A),
                   mkCons h1 t1 = mkCons h2 t2 ->
                   h1 = h2 /\ t1 = t2.
    intros h1 h2 t1 t2 u.
    assert (c : outList (mkCons h1 t1) = outList (mkCons h2 t2)).
    + rewrite u; reflexivity.
    + simpl in c.
      injection c.
      auto.
    Qed.

  Definition canonList (xs : List A) : List A := toList (fromList xs).

  Theorem inj : forall (xs : list A), fromList (toList xs) = xs.
    induction xs.
    - simpl. auto.
    - replace (fromList (toList (a :: xs))) with (cons a (fromList (toList xs))).
      rewrite IHxs.
      reflexivity.
      auto.
  Qed.
        
  Definition ForaL(P : A -> Prop)(l : List A) : Prop := Forall P (fromList l).

  (** Some basic list operations. *)

  Definition ListAlg := Alg (ListF A).
  Definition ListSAlg := SAlg (ListF A).

  Definition LengthSAlg : ListSAlg (Const nat) :=
   rollSAlg
   (fun _ _ _ _ _ eval xs =>
       match xs with
         Nil => 0
       | Cons hd tl => 1 + eval tl
       end).

  Definition length : List A -> nat :=
    sfold (ListF A) (Const nat) (FunConst nat) LengthSAlg.

  Definition appendAlg : ListAlg (Const (List A -> List A)) :=
    rollAlg (fun _ _ _ eval xs ys =>
               match xs with
               | Nil => ys
               | Cons hd tl => mkCons hd (eval tl ys)
               end).
  
  Definition append (xs ys : List A) : List A :=
    fold (ListF A) _ _ appendAlg xs ys.
  

  Definition getNilSAlg : ListSAlg Id :=
    rollSAlg 
      (fun P R up _ (abstIn : ListF A R -> P) rec d => abstIn Nil).

  Definition getNil : List A -> List A :=
    sfold (ListF A) Id FunId getNilSAlg.


  (** Dependent [List]. *)
      
  Definition lkMo := List A -> Prop.
  Inductive ListFi(R : lkMo) : lkMo :=
    nilFi : ListFi R mkNil
  | consFi : forall (h : A)(t : List A), R t -> ListFi R (mkCons h t).

  Arguments nilFi {R}.
  Arguments consFi {R} h t rt.

  Definition ListFiMap(B C : lkMo)
             (f : forall l : List A , B l -> C l)
             (l : List A)(d : ListFi B l) : ListFi C l :=
    match d with
      nilFi => nilFi
    | consFi hd tl rtl => consFi hd tl (f tl rtl)
    end.

  Lemma ListFiMapId : FmapiId (List A) ListFi ListFiMap.
    intros B i fi.
    destruct fi.
    + reflexivity.
    + reflexivity.
  Qed.

  Fixpoint listFoldi
           (l : list A)
           (X : lkMo)
           (alg : forall l : List A , ListFi X l -> X l)
           { struct l} :
    X (toList l) :=

    match l with
      [] => alg (toList []) nilFi
    | hd :: tl =>
      alg (toList (cons hd tl))
          (consFi
             hd
             (toList tl)
             (listFoldi tl X alg))
    end.

  Global Instance depList : Functori (List A) (ListFi) :=
    {
    fmapi := ListFiMap;
    fmapiId := ListFiMapId
    }.

  Definition Listi := Dci ListFi.
  Definition inListi(l : List A)(fl : ListFi Listi l) : Listi l := inDci l fl.
  Definition mkNili : Listi mkNil :=
    inListi mkNil nilFi.
  Definition mkConsi (hd : A) (tl : List A) (tli : Listi tl) : Listi (mkCons hd tl) :=
    inListi (mkCons hd tl) (consFi hd tl tli).

  Definition ListFoldTi(R : List A -> Prop)(d : List A) : Prop :=
    FoldTi (Algi ListFi) R d.

  Definition ListSFoldTi(R : List A -> Prop)(d : List A) : Prop :=
    FoldTi (SAlgi ListFi) R d.

  Definition toListi(xs : list A) : Listi (toList xs).
    apply (listFoldi xs Listi).
    intros l li.
    destruct li as [|hd tl tli].
    apply mkNili.
    apply mkConsi; assumption.
  Defined.
  
  Definition ListAlgi := Algi ListFi.
  Definition ListSAlgi := SAlgi ListFi.  

  (** Some proofs about the above basic list operations. *)

  Definition getNilEqP(_ : kMo (List A))(d : List A) : Prop :=
    fromList (getNil d) = nil.
  
  Lemma getNilEqFun(B C : kMo (List A)) : FmapiT (List A) getNilEqP B C.
    intros f d u.
    exact u.
  Qed.

  Lemma getNilEqSAlgi : ListSAlgi getNilEqP.
    apply rollSAlgi; intros S R up sfo abstIn ih d di.
    destruct di; reflexivity.
  Qed.

  Definition getNilConsP(d : List A) : Prop :=
    forall h : A, getNil (mkCons h d) = getNil d.

  Lemma getNilConsSAlgi : ListSAlgi (Consti getNilConsP).
    apply rollSAlgi; intros S R up sfo abstIn ih d di.
    destruct di; intro hh; reflexivity.
  Qed.

  Definition getNilCons{R : List A -> Prop}(sfo : forall d : List A, ListSFoldTi R d)(l : List A)(r : R l) : getNilConsP l :=
    sfo l (Consti getNilConsP) (FunConsti getNilConsP) getNilConsSAlgi r.

End ListProperties.

Arguments canonList {A} xs.

Arguments ForaL {A} P l.
Arguments ListFoldTi{A}.
Arguments getNil{A}.
Arguments getNilCons{A}{R}.
Arguments inj{A}.

Arguments toListi{A}.

(** Common, helpful tactics. *)
Ltac fromCons := change (fromList (mkCons ?h ?t)) with (h :: fromList t).

(** Prove P (toList xs) using Dci for lists. *)
  Ltac listInd A P xs :=
  let ind := fresh "ind" in
    set (ind := foldi (Fi := ListFi A) (toList xs) P);
    simpl in ind; try (rewrite (inj xs) in ind);
    apply ind; clear ind; [apply FunConsti | apply rollAlgi; intros R fo sfo ih d fd; destruct fd (*; [ idtac | fromCons]*) | exact (toListi xs)]. 

Section example.
  Context {A : Set}.
  (** Just an example F-algebra mentioned in the paper. *)
  Definition lengthAlg(d : ListF A nat) : nat :=
    match d with
      Nil => O
    | Cons x xs => S xs
    end.
End example.
