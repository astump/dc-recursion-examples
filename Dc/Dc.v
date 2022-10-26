(** * Divide and Conquer Interface *)
Require Import Kinds.
Require Import Mu.
Require Import CastAlg.
Require Import Functors.

Require Import Coq.Logic.FunctionalExtensionality.

Section Dc.
(** Assumptions *)

  Variable F : Set -> Set.
  Context {FunF : Functor F}.

(** Helper Typedefs *)

Definition FoldT(alg : KAlg)(C : Set) : Set :=
  forall (X : Set -> Set) (FunX : Functor X), alg X -> C -> X C.

(** Subsidiary Algebra *)

Definition SAlgF
           (A: KAlg)
           (X : Set -> Set) : Set
  := forall
        (P : Set)
       (R : Set)
       (up : R -> P)    
       (sfo : FoldT A R)    
       (abstIn : F R -> P)      
       (rec : R -> X R)      
       (d : F R),             
       X P.

Definition SAlg := MuAlg SAlgF.

Definition monoSAlg : forall (A B : KAlg), CastAlg A B -> CastAlg (SAlgF A) (SAlgF B) :=
  fun A B castSAlg =>
    fun X salgf P R cRS sfo =>
      salgf P R cRS (fun X1 xmap y => sfo X1 xmap (castSAlg X1 y)).

Definition rollSAlg : forall {X : Set -> Set}, SAlgF SAlg X -> SAlg X :=
  fun X d => inMuAlg SAlgF d.

Definition unrollSAlg : forall {X : Set -> Set}, SAlg X -> SAlgF SAlg X :=
  fun X d => outMuAlg SAlgF monoSAlg d.

Definition castSAlgId : forall (A : KAlg), CastAlg A A :=
  fun A X d => d.
  
(* fmapId law for HO KAlg Functor *)
Lemma monoSAlgId :
  forall (A : KAlg) (X : Set -> Set) (salgf : SAlgF A X),
    monoSAlg A A (castSAlgId A) X salgf = salgf.
  intros.
  unfold monoSAlg.
  repeat (apply functional_extensionality_dep; simpl; intros).
  repeat f_equal.
Qed.                                                  

(** Regular Algebra *)

Definition AlgF(A: KAlg)(X : Set -> Set) : Set :=
  forall (R : Set)
      (fo : FoldT A R)
      (sfo : FoldT SAlg R)
      (rec : R -> X R)      
      (d : F R),             
      X R.

Definition Alg := MuAlg AlgF.

Definition monoAlg : forall (A B : KAlg), CastAlg A B -> CastAlg (AlgF A) (AlgF B) :=
  fun A B f =>
    fun X algf R fo  =>
      algf R (fun X xmap alg => fo X xmap (f X alg)).

Definition castAlgId : forall (A : KAlg), CastAlg A A :=
  fun A X d => d.
  
(** fmapId law for higher order [KAlg] Functor *)
Lemma monoAlgId :
  forall (A : KAlg) (X : Set -> Set) (algf : AlgF A X),
    monoAlg A A (castAlgId A) X algf = algf.
  intros.
  unfold monoAlg.
  repeat (apply functional_extensionality_dep; simpl; intros).
  repeat f_equal.
Qed.

Definition rollAlg : forall {X : Set -> Set}, AlgF Alg X -> Alg X :=
  fun X d => inMuAlg AlgF d.

Definition unrollAlg : forall {X : Set -> Set}, Alg X -> AlgF Alg X :=
  fun X d => outMuAlg AlgF monoAlg d.

Lemma UnrollRollIso :
  forall (X : Set -> Set) (algf : AlgF Alg X), unrollAlg (rollAlg algf) = algf.
  intros.
  apply monoAlgId.
Qed.

(** building Dc, our initial algebra carrier *)

Definition DcF(C : Set) := forall (X : Set -> Set) (FunX : Functor X), Alg X -> X C.
Definition Dc := Mu DcF.
    
Definition fmapDc(A B : Set) : FmapT A B DcF := fun f initA => fun X xmap alg => fmap f (initA X xmap alg).

Lemma fmapIdDc : FmapId DcF fmapDc. 
  intros A x.
  unfold fmapDc.
  apply functional_extensionality_dep.
  intro X.
  apply functional_extensionality_dep.
  intro funX.
  apply functional_extensionality_dep.
  intro alg.
  apply (@fmapId X).
Qed.

Instance initFunc : Functor DcF :=
  {
  fmap := fmapDc;
  fmapId := fmapIdDc
  }.
  
Definition rollDc: DcF Dc -> Dc :=
  inMu DcF.

Definition unrollDc: Dc -> DcF Dc :=
  outMu (FunF := initFunc) DcF.

(** 
   We want to build [inDc : F Dc -> Dc].
   to build [inDc], we need to build concretizations of its abst. functions:
   - [fold], [sfold], [out].
   - [promote] is needed to write [sfold].
*)

Definition fold : FoldT Alg Dc := fun X FunX alg d => unrollDc d X FunX alg.

Definition RevealT(X : Set -> Set) : Set -> Set := (fun R => (R -> Dc) -> (X Dc)).

Definition RevealFmap(X : Set -> Set)(Fun:Functor X)(A B : Set)(f : A -> B)(xs : RevealT X A) : RevealT X B.
  intro reveal.
  apply xs.
  intro a.
  exact (reveal (f a)).
Defined.

Lemma RevealFmapId(X : Set -> Set)(Fun : Functor X)(A : Set)(xs : RevealT X A):
         RevealFmap X Fun A A (fun x => x) xs = xs.
  reflexivity.
Qed.

Global Instance FunRevealT(X : Set -> Set)`(Fun:Functor X) : Functor (RevealT X) :=
  { fmap := RevealFmap X Fun ;
    fmapId := RevealFmapId X Fun }.

Definition promote : forall (X : Set -> Set)
                       (FunX : Functor X),
    (SAlg X) -> Alg (RevealT X) :=
  fun X funX salg =>
    rollAlg (fun R fo sfo rec fr reveal =>
               let abstIn := fun fr => rollDc (fun X funX alg =>
                                           fmap reveal (unrollAlg alg R fo sfo (fo X funX alg) fr))
               in let rec' := sfo X funX salg                                        
               in unrollSAlg salg Dc R reveal sfo abstIn rec' fr).

Definition sfold : FoldT SAlg Dc :=
  fun X funX salg x =>
    fold (RevealT X) (FunRevealT X funX) (promote X funX salg) x (fun x => x).

Definition out{R : Set}(sfo : FoldT SAlg R) : R -> F R :=
  sfo F FunF (rollSAlg (fun _ _ up _ _ _ d => fmap up d)).

Definition inDc : F Dc -> Dc :=
  fun d => rollDc (fun X xmap alg =>
                    unrollAlg alg Dc fold sfold (fold X xmap alg) d).
  
Definition abstInDc : F Dc -> Dc :=
  fun d => rollDc (fun X xmap alg =>
                    fmap (fun x : Dc => x) (unrollAlg alg Dc fold sfold (fold X xmap alg) d)).

Lemma rollDcCong(x y : DcF Dc) : x = y -> rollDc x = rollDc y.
  intro u; rewrite u; trivial.
Qed.

Lemma abstInId(fd : F Dc) : abstInDc fd = inDc fd.
  unfold abstInDc, inDc.
  apply rollDcCong.
  apply functional_extensionality_dep.
  intro X.
  apply functional_extensionality_dep.
  intro FunX.
  apply functional_extensionality_dep.
  intro alg.
  rewrite fmapId.
  trivial.
Qed.

End Dc.

Arguments rollAlg{F}{X}.
Arguments rollSAlg{F}{X}.

Ltac foldAbstIn :=
  repeat (match goal with
          | |- context[rollDc ?F (fun (X : Set -> Set)(funX : Functor X) (alg : Alg ?F X) =>
                                    fmap (fun x : Dc ?F => x)
                                         (unrollAlg ?F alg (Dc ?F) (fold ?F) (sfold ?F) (fold ?F X funX alg) ?d))] =>
    change (rollDc F (fun (X : Set -> Set)(funX : Functor X) (alg : Alg F X) =>
              fmap (fun x : Dc F => x)
                   (unrollAlg F alg (Dc F) (fold F) (sfold F) (fold F X funX alg) d))) with (abstInDc F d);
    rewrite (abstInId F d)
  end).

(** Common Tactics *)

Tactic Notation "simpl'" "in" hyp(c) :=
  simpl in c;
  try (repeat (rewrite monoAlgId, monoSAlgId, RevealFmapId in c)).

Tactic Notation "simpl'"  :=
  simpl;
  repeat (rewrite monoAlgId || rewrite monoSAlgId || rewrite RevealFmapId).


          
