(** * Functors *)
(** The Functors file includes a fair amount of generic definitions we reuse
elsewhere (such as the [Functor] typeclass). We also store some frequently used
functors, e.g., [Const] and [Id].  *)
Require Import Kinds.

Definition FmapT(A B : Set)(F : Set -> Set) : Set := forall(f : A -> B), F A -> F B.
Definition FmapId(F : Set -> Set)(fmap : forall{A B : Set}, FmapT A B F) : Set :=
  forall (A : Set) (x : F A), fmap (fun x => x) x = x .

Class Functor (F : Set -> Set) :=
  {
  fmap : forall {A B : Set}, FmapT A B F;
  fmapId : FmapId F (@fmap)
  }.

(** Identity, option, and constant [functor]s. *)
Definition Id(X:Set) : Set := X.
Global Instance FunId : Functor Id := {
    fmap := fun A B c xs => c xs ; fmapId := fun A x => eq_refl
  }.

Global Instance FunOption : Functor option :=
  { fmap := fun A B c o => match o with Some x => Some (c x) | None => None end;
    fmapId := fun A o => match o with Some x => eq_refl | None => eq_refl end }.

Definition Const(T: Set) : Set -> Set := fun _ => T.
Global Instance FunConst(T : Set)  : Functor (Const T) :=
  {fmap := fun A B f xs => xs;
   fmapId := fun A xs => eq_refl }.


(** Indexed (dependent) versions. *)

Section Ind.
 Variable I : Set.
 Definition kMo := kMo I .

 Section IndF.
  Variable Fi : kMo -> kMo.

  Definition FmapiT(A B : kMo) : Set := (forall i : I, A i -> B i) -> forall i : I , Fi A i -> Fi B i.

  Definition FmapiId(fmapi : forall{A B : kMo}, FmapiT A B) : Set :=
   forall (A : kMo) (i : I)(x : Fi A i), fmapi (fun _ x => x) i x = x .

  Class Functori :=
  {
   fmapi : forall {A B : kMo}, FmapiT A B;
   fmapiId : FmapiId (@fmapi)
  }.

 End IndF.

 Definition Consti(R: kMo) : kMo -> kMo := fun _ d => R d.
 Global Instance FunConsti(R : kMo) : Functori (Consti R) :=
  { fmapi := fun A B f i xs => xs;
    fmapiId := fun A x c => eq_refl }.

End Ind.

Arguments Consti{I}.
Arguments FunConsti{I}.
