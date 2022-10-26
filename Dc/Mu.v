(** * Mu.V *)
(** Derivation of "positive-retractive" types. [Mu] is a least fixed-point
operator for signature functors which are positive (but needn't be strictly
positive). *)

Require Import Kinds.
Require Import CastAlg.
Require Import Functors.
Require Import Coq.Setoids.Setoid.

Section Mu.

  Variable F : Set -> Set.
  Context {FunF : Functor F}.           

  Definition MAlgebra
             (A : Set) :=
    forall (R : Set), (R -> A) -> F R -> A.

  Inductive Mu : Set := 
    mu : MAlgebra Mu.

  Definition inMu(d : F Mu) : Mu :=
    mu Mu (fun x => x) d.

  Definition outMu(m : Mu) : F Mu :=
    match m with
    | mu A r d => fmap r d
    end.

  Definition retraction : forall(d : F Mu), outMu (inMu d) = d.
  simpl.
  intro d.
  rewrite fmapId.
  trivial.
  Qed.
  
(** The definitions below show that canonicity can be recovered using a
normalization equivalence relation; these definitions are not used elsewhere in
our development, though. *)

  Definition IndMu(m : Mu) : Set :=
    forall X : Mu -> Set,
      (forall(R:Set)(reveal : R -> Mu),
          (forall r : R, X (reveal r)) ->
          forall d : F R ,
            X (mu R reveal d))->
      X m.

  Fixpoint Mu_fold
           {A : Set}
           (alg : MAlgebra A)
           (m : Mu)
    {struct m} : A :=
    match m with
      mu A reveal d => alg _ (fun r => Mu_fold alg (reveal r) ) d
    end.
    
  Definition normalize_Mu (m : Mu) : Mu :=
    Mu_fold (fun R rec fr => inMu (fmap rec fr)) m.

  Definition Mu_equiv (m1 m2 : Mu) : Prop := normalize_Mu m1 = normalize_Mu m2.

  Lemma Mu_equiv_refl : Reflexive Mu_equiv.
    unfold Reflexive; reflexivity.
  Qed.

  Lemma Mu_equiv_sym : Symmetric Mu_equiv.
    unfold Symmetric; symmetry; eauto.
  Qed.

  Lemma Mu_equiv_trans : Transitive Mu_equiv.
    unfold Transitive; etransitivity; eauto.
  Qed.

  #[global] Add Relation Mu Mu_equiv
      reflexivity proved by Mu_equiv_refl
      symmetry proved by Mu_equiv_sym
      transitivity proved by Mu_equiv_trans
    as Mu_equiv_rel.

  Infix "≈" := Mu_equiv (at level 90).
  
End Mu.
(** 
   Higher-ordered [Mu] over [KAlg].
   This permits non-strictly positive occurrences of [Alg] in defining
   [Alg] via its (higher ordered) [AlgF].
*)

Section MuAlg.

  Variable F : KAlg -> KAlg.
  Variable algMap : forall {A B : KAlg}, CastAlg A B -> CastAlg (F A) (F B). 


  Inductive MuAlg : KAlg := 
  muAlg : forall A : KAlg,
    (forall (X : Set -> Set), A X -> MuAlg X) ->
    forall (X : Set -> Set), F A X -> MuAlg X.

  Definition inMuAlg {X : Set -> Set} (d : (F MuAlg) X) : MuAlg X :=
    muAlg MuAlg (fun X x => x) X d.

  
  Definition outMuAlg{X : Set -> Set} (v : MuAlg X) : (F MuAlg) X :=
    match v with
    | muAlg A r X1 d => algMap r X1 d
    end.
End MuAlg.
