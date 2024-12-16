From idt Require Export all.
From MetaCoq.Template Require Export utils All.
From Coq.Strings Require Import Ascii.

Require Import Functorializer.

Ltac TMo_kind T := refine_params T; exact Type.

Ltac getGoal :=
  match goal with
  | [ |- ?U ] => U
  end.

Ltac raiseParams :=
  let rec go U :=
    match U with
    | let p := param ?A ?n in ?S => mark_param A n; go S
    | _ => idtac
    end in go getGoal.

Ltac TMo TF := repeat (intro; raiseParams);
           refine (_ -> Prop); exact_build TF.

Inductive Param' : typed_term -> nat -> Type :=
| param' : forall (A : typed_term) (n : nat), Param' A n.

Ltac mark_param' S n :=
  let H := fresh "p" in
  pose (param' S n) as H;
  simpl in H.

Ltac refine_params'_tac S tac :=
  let rec go U n :=
    let K := type of U in
    match K with
    | forall (A : Set), ?V =>
        refine (forall (A: Set), (_ : Type));
        let RA := fresh A in
        pose (RA := existT_typed_term _ A);
        mark_param' RA n;
        let n := eval simpl in (n+1) in
        specialize (U A);
        go U n
  | forall (A : Type), ?V =>
      refine (forall (A: Set), (_ : Type));
      let RA := fresh A in
      pose (RA := existT_typed_term _ A);
      mark_param' RA n;
      let n := eval simpl in (n+1) in
      specialize (U A);
      go U n
  | forall (A : ?S), ?V =>
      refine (forall (A: S), (_ : Type));
      let RA := fresh A in
      pose (RA := existT_typed_term _ A);
      mark_param' RA n;
      let n := eval simpl in (n+1) in
      specialize (U A);
      go U n
  | _ => let n := eval simpl in (n-1) in tac n
end in
  let H := fresh "S" in
  pose proof S as H;
  go H constr:(0);
  clear H.

Ltac idtacarg n := idtac.

Ltac refine_params' S := refine_params'_tac S idtacarg.

Inductive MarkInd : typed_term -> Type :=
  | markind : forall (A : typed_term), MarkInd A.

Ltac mark_ind n :=
  match goal with
  | [ H : Param' ?A n |- _ ] => pose (markind A)
  end.


Ltac refine_params'_mark_ind S :=
  refine_params'_tac S mark_ind.

(* Definition P := forall A, list A -> Prop. *)

Ltac buildParams' U :=
  let rec go U n :=
    match goal with
        | [ H : Param' ?A n |- _] =>
            let n := eval simpl in (n+1) in
            let A := eval simpl in A.(my_projT2) in
            go (U A) n
      | _ => U
end in go U constr:(0).

Ltac clear_params' :=
  repeat match goal with
           | [ H : Param' _ _ |- _ ] => clear H
         end.

Tactic Notation "build_params'" open_constr(U) ">>" tactic(tac) :=
  let K := buildParams' U in
  tac K.

Tactic Notation "build_params'" open_constr(U) :=
  build_params' U >> (fun K => let H := fresh "K" in pose K as H).

Tactic Notation "exact_build'" open_constr(U) :=
  build_params' U >> (fun K => exact K).

Definition getConstRef (g : list global_reference) : TemplateMonad kername :=
  match g with
  | ConstRef k :: _ => tmReturn k
  | _ => tmFail "Not a constant"
  end.

Set Printing Universes.

Definition QuoteDef (c : string) : TemplateMonad (ident * typed_term).
  refine (g <- tmLocate c ;;
          k <- getConstRef g;;
          tm <- tmUnquote (tConst k []);;
          tmReturn (c, tm)
          ).
Defined.

Ltac mks_names TF :=
  (run_template_program (get_ctors TF)
                         (fun xs =>
                            let xs := eval simpl in xs in
                              let rec go xs :=
                                lazymatch xs with
                                 | (?name, _) :: ?xs =>
                                     let name := constr:(append "mk" name) in
                                     let name := eval simpl in name in
                                     refine (cons name _);
                                     go xs
                                | _ => exact nil
                                end in go xs
  )).


Notation mkIndConstrs TF :=
  (let l := ltac:(mks_names TF) in
  ls <- (monad_map QuoteDef l) ;;
  tmReturn ls)
(only parsing).

Ltac getInd :=
  match goal with
  | [ H : MarkInd ?P |- _ ] =>
      let P := eval cbn in (my_projT2 P) in P
  end.

Ltac refineRecCall :=
  let rec go n :=
    match goal with
        | [ H : Param' ?P n |- _] =>
            let n := eval simpl in (n+1) in
            let A := eval cbn in P.(my_projT1) in
            let D := eval cbn in P.(my_projT2) in
              match A with
              | Dc _ => let P := getInd in
                       let F := eval cbn in (P D) in
                       refine (F -> _); go n
              | _ => go n
              end

  | _ => idtac
end in go constr:(0).


Ltac build_induction R ctor :=
  refine_params'_mark_ind R;
  build_params' R >> (fun R => build_params' ctor >>
                      (fun c => clear_params'; refine_params' c; build_params' c >>
                       (fun c => refineRecCall; exact (R c)))).

Ltac indConstrs mks :=
  run_template_program mks (fun xs =>
                              let xs := eval cbn in xs in
                                let rec go xs :=
                                  match xs with
                                  | nil => exact Functorializer.nil'
                                  | (?name, existT_typed_term ?ty ?ctor) :: ?xs =>
                                     let name := constr:(append name "Fi") in
                                     let name := eval simpl in name in
                                      let c := fresh "ctor" in
                                      refine (Functorializer.cons' (name, _) _);
                                      [ intros Hc R; pose (ctor : ty) as c
                                        ; build_induction R c
                                      | go xs ]
                                  end in go xs).

Ltac ISig T Mo :=
  refine_params' T; build_params' Mo >> (fun l => refine (forall (P : l), l)).

Definition tsf_default_mind' (T : Type) (name : ident) (ctors : list (ident * term)) (orig_mind : mutual_inductive_body)
  : TemplateMonad unit :=
  ty <- tmQuote T ;;
  let npars := orig_mind.(ind_npars) + 1 in
  let params := extract_params ty npars in
  let indparam := map (fun '(s, t) => mk_indparam s t) params in
  let ctors := map (fun '(n, t) =>
                      let t' := try_remove_n_lambdas 1 t in
                      (n, t', count_tProds t' - npars)) ctors in

  tmMkInductive' {| ind_finite := Finite;
    ind_npars := npars;
    ind_universes := Monomorphic_ctx (LevelSet.empty, ConstraintSet.empty);
    ind_variance := None;
    ind_params := indparam;
    ind_bodies := [ {| ind_name := name;
                      ind_type  := ty;
                      ind_kelim := IntoPropSProp;
                      ind_ctors :=
                        ctors;
                      ind_projs := [];
                      ind_relevance := Relevant |} ] |}.

(* Notation buildInd Mo indName cts := *)
Notation buildInd T TSig indName cts :=
  (let ctors := ltac:(tsf_ctors_to_tm' (unfolded cts)) in
  l <- tmQuote T;;
  '(orig_mind, i) <- tsf_get_mind l;;
  tsf_default_mind' (unfolded TSig) indName ctors orig_mind)
(only parsing).

Notation gen_motive propname T TF :=
  (let kMo : ltac:(TMo_kind T) := ltac:(TMo TF) in
   k <- tmEval cbn kMo;;
   tmDefinition propname k) (only parsing).

Notation gen_induction T TF kMo indName :=
  (
   (* let kMo : ltac:(TMo_kind T) := ltac:(TMo DTF) in *)
   let TFiSig : Type := ltac:(ISig T kMo) in
   let l := ltac:(mks_names TF) in
   let Fi_ctors : tsf_ctors_ty' (unfolded TFiSig) := ltac:(indConstrs (monad_map QuoteDef l)) in
   buildInd T TFiSig indName Fi_ctors
  ) (only parsing).
