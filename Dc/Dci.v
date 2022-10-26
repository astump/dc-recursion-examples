(** * Indexed Divide and Conquer Interface *)

Require Import Kinds.
Require Import Mu.
Require Import Mui.
Require Import Functors.
Require Import CastAlg.
Require Import Dc.
  
Require Import Coq.Logic.FunctionalExtensionality.

Section Dci.
  
(** Assumptions *)
  Variable I : Set.

  Definition KAlgi := KAlgi I.
  Definition kMo := kMo I.

  Variable Fi : kMo -> kMo.
  Context {FunFi : Functori I Fi }.  

 
(** Helper Typedefs *)
  
  Definition FoldTi(alg : KAlgi)(C : kMo) : kMo :=
    fun d => forall (X : kMo -> kMo) (xmap : Functori I X), alg X -> C d -> X C d.

(** Subsidiary Algebra *)

Definition SAlgF
           (A: KAlgi)
           (X : kMo -> kMo) : Set
  := forall
       (P : kMo)
       (R : kMo)
       (up : forall (d : I), R d -> P d)    
       (sfo : forall (d : I), FoldTi A R d)    
       (abstIn : forall (d : I), Fi R d -> P d)      
       (ih : forall (d : I), R d -> X R d)
       (d : I),      
       Fi R d -> X P d.

Definition SAlgi := MuAlgi I SAlgF.

Definition monoSAlgi : forall (A B : KAlgi), CastAlgi I A B -> CastAlgi I (SAlgF A) (SAlgF B) :=    
  fun A B castSAlgi =>
    fun X salgf P R up sfo =>
      salgf P R up (fun d1 X1 xmap salg => sfo d1 X1 xmap (castSAlgi X1 salg)).

Definition rollSAlgi : forall {X : kMo -> kMo}, SAlgF SAlgi X -> SAlgi X :=
  fun X d => inMuAlgi I SAlgF d.

Definition unrollSAlgi : forall {X : kMo -> kMo}, SAlgi X -> SAlgF SAlgi X :=
  fun X d => outMuAlgi I SAlgF monoSAlgi d.

(** Regular Algebra *)

Definition AlgF(A: KAlgi)(X : kMo -> kMo) : Set :=
  forall (R : kMo)
    (fo : (forall (d : I), FoldTi A R d))
    (sfo : (forall (d : I), FoldTi SAlgi R d))
    (ih : (forall (d : I), R d -> X R d))
    (d : I),
    Fi R d -> X R d.

Definition Algi := MuAlgi I AlgF.

Definition monoAlgi : forall (A B : KAlgi),
    CastAlgi I A B ->
    CastAlgi I (AlgF A) (AlgF B) :=
  fun A B cAB =>
    fun X algf R fo  =>
      algf R (fun i' X xmap alg => fo i' X xmap (cAB _ alg)).

Definition rollAlgi : forall {X : kMo -> kMo}, AlgF Algi X -> Algi X :=
 fun X i => inMuAlgi I AlgF i.

Definition unrollAlgi : forall {X : kMo -> kMo}, Algi X -> AlgF Algi X :=
  fun X => outMuAlgi I AlgF monoAlgi.

(** Ii *)

Definition DcFi(C : kMo) : kMo := fun d => forall (X : kMo -> kMo) (xmap : Functori I X), Algi X -> X C d.
Definition Dci := Mui I DcFi.

Definition DciFmap{A B : kMo} : FmapiT I DcFi A B :=
  fun f i d => fun X xmap alg => 
    fmapi I X f i (d X xmap alg).

Definition DciFmapId : FmapiId I DcFi (@DciFmap).
  intros A i x .
  unfold DciFmap.
  apply functional_extensionality_dep.
  intro X.
  apply functional_extensionality_dep.
  intro xmap.
  apply functional_extensionality_dep.
  intro alg.
  rewrite fmapiId.
  reflexivity.
Qed.

Global Instance DcFmapi : Functori I DcFi :=
  {
    fmapi := fun A B => @DciFmap A B;
    fmapiId := DciFmapId
  }.

Definition rollDci(i : I)(d : DcFi Dci i) : Dci i :=
  inMui I DcFi i d.

Definition unrollDci(i : I)(d : Dci i) : DcFi Dci i :=
  outMui I DcFi i d.

(** Building toDci. *)

Definition foldi(i : I) : FoldTi Algi Dci i := fun X xmap alg d => unrollDci i d X xmap alg.

Definition outi(i :I) : Dci i -> Fi Dci i :=
  foldi i Fi FunFi
            (rollAlgi
               (fun R fo sfo ih i' df => df)).

Definition RevealT(X : kMo -> kMo) : kMo -> kMo := (fun R i => (forall i : I , R i -> Dci i) -> (X Dci i)).

Definition RevealFmap(X : kMo -> kMo)(Fun:Functori I X)(A B : kMo)(f : forall i : I, A i -> B i)
                     (i : I)(xs : RevealT X A i) : RevealT X B i.
  intro reveal.
  apply xs.
  intros i' a.
  exact (reveal i' (f i' a)).
Defined.

Lemma RevealFmapId(X : kMo -> kMo)(Fun : Functori I X)(A : kMo)(i : I)(xs : RevealT X A i):
         RevealFmap X Fun A A (fun x c => c) i xs = xs.
  reflexivity.
Qed.

Global Instance FunRevealT(X : kMo -> kMo)`(Fun:Functori I X) : Functori I (RevealT X) :=
  { fmapi := RevealFmap X Fun ;
    fmapiId := RevealFmapId X Fun }.

Definition promotei :
  forall (X : kMo -> kMo)
    (xmap : Functori I X),
    SAlgi X -> Algi (RevealT X) :=
  fun X xmap salg =>
    rollAlgi (
        fun R fo sfo IH d fd reveal =>
          let abstIn : forall (d : I), Fi R d -> Dci d :=
              fun d1 fd1 => rollDci d1 (
                            fun X1 xmap1 alg1 =>
                              fmapi I X1 reveal d1
                                    (unrollAlgi alg1 R fo sfo 
                                                (fun d0 rd => fo d0 X1 xmap1 alg1 rd)
                                    d1 fd1)
                                  )
                         
          in let IHs := fun d1 => sfo d1 X xmap salg
             in unrollSAlgi salg Dci R reveal sfo abstIn  IHs d fd
      ).

Definition sfoldi(i : I) : FoldTi SAlgi Dci i :=
  fun X xmap salg di =>
    foldi i (RevealT X) (FunRevealT X xmap) (promotei X xmap salg) di (fun i di => di).


Definition inDci(i : I)(fd : Fi Dci i) : Dci i :=
  rollDci i 
            (fun X xmap alg =>
               let IH := fun i1 d => unrollDci i1 d X xmap alg in
               unrollAlgi alg Dci foldi sfoldi IH i fd
            ).

End Dci.

(** Make F implicit for all terms after Dc decl. *)
Arguments Dci{I}.
Arguments Algi{I}.
Arguments SAlgi{I}.
Arguments FoldTi{I}.
Arguments foldi{I} {Fi}.
Arguments rollSAlgi{I} {Fi}.
Arguments unrollSAlgi{I} {Fi}.
Arguments rollAlgi{I} {Fi}.
Arguments unrollAlgi{I} {Fi}.
Arguments rollDci{I} {Fi}.
Arguments unrollDci{I} {Fi}.
Arguments sfoldi{I} {Fi}.
Arguments inDci{I} {Fi}.
