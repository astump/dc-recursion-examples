(** * Functorializer -- generating D&C datatypes from inductive Coq definitions. *)

(** This file converts a datatype to it's functorial representation
   using the interface described in dc-recursion/.../List.v *)
From idt Require Export all.
From MetaCoq.Template Require Export utils All.
From Coq.Strings Require Import Ascii.

Require Export Dc.
Require Export Dci.
Require Export Kinds.
Require Export Functors.
Require Export Mu.

(* ------------ Metacoq Auxiliary Functions ------------ *)

Fixpoint extract_params (t : term) (n : nat) : list (aname * term) :=
  match n with
      | O => []
      | S n' => match t with
                   | tProd s ty t' => (s, ty) :: extract_params t' n'
                   | _ => []
               end
  end.

Fixpoint extract_ty_ret (t : term) : term :=
  match t with
      | tProd _ _ t' => extract_ty_ret t'
      | t => t
  end.

Definition mk_indparam (s : aname) (t : term) : context_decl :=
  {| decl_name := s;
    decl_body := None;
    decl_type := t |}.

Definition get_level (t : term) : list LevelSet.elt :=
  match t with
      | tSort (Universe.lType {|Universe.t_set := {| UnivExprSet.this := xs |}
              |}) => map fst xs
      | _ => []
  end.

Fixpoint count_tProds' (n : nat)  (t : term) : nat :=
  match t with
      | tProd _ _ t' => count_tProds' (S n) t'
      | _ => n
  end.

Definition count_tProds := count_tProds' 0.


(* ----------------------------------------------------- *)


Inductive hlist : (list Type) -> Type :=
| HNil : hlist nil
| HCons : forall (x:Type) (ls:list Type), string -> x -> hlist ls -> hlist (x::ls).

Fixpoint hget (ls:list Type) (hls:hlist ls) (n:nat){struct n} : option (nth n ls Empty_set) :=
  match hls in (hlist l) return option (nth n l Empty_set) with
      | HNil => None
      | HCons _ nil _ _ _ => None
      | HCons _ ys _ x xs =>
          match n with
              | 0 => Some x
              | S p => hget ys xs p
          end
  end.

Fixpoint hmap (ls : list Type) (hls: hlist ls) {struct hls} :
    (string -> forall (A : Type), A -> TemplateMonad A) -> TemplateMonad unit.
  refine (fun f =>
      match hls in hlist l return l = ls -> TemplateMonad unit with
      | HNil => fun _ => tmReturn tt
      | HCons T ys s x xs => fun (eq : T :: ys = ls) => f s T x;; hmap ys xs f
      end eq_refl).
Defined.


Arguments HCons [x ls] _ _ _.
Arguments hget [ls].

Inductive list' (A : Type) : Type :=
| nil'  : list' A
| cons' : A -> list' A -> list' A.

Arguments nil' {A}.
Arguments cons' {_}.

Section MonadOperations.
  Context {T : Type -> Type} {M : Monad T}.
  Context {A B} (f : A -> T B).
  Context (h : nat -> A -> T B).

Fixpoint monad_map_i_aux' (n0 : nat) (l : list A) : T (list' B)
  := match l with
         | nil => ret nil'
         | x :: l => x' <- (h n0 x) ;;
                   l' <- (monad_map_i_aux' (S n0) l) ;;
                   ret (cons' x' l')
     end.

Definition monad_map_i' := @monad_map_i_aux' 0.
End MonadOperations.

Notation tsf_ctors_ty' T := (list' (ident * (False -> T -> Type))).

Definition get_ctors' {T : Type} (t : T)
  : TemplateMonad (list' (ident * typed_term@{Type})) :=
  tm <- tmQuote t;;
  match tm with
  | tInd ind _ =>
     mind <- tmQuoteInductive ind.(inductive_mind);;
     match nth_error mind.(ind_bodies) ind.(inductive_ind) with
     | Some body =>
         monad_map_i' (fun i '(name, _, _) =>
                        tm <- tmUnquote (tConstruct ind i []);;
                        ret (@pair _ typed_term name (tm : typed_term)))
                     body.(ind_ctors)
     | _ => tmFail "No body found"
     end
  | _ => tmFail "Not an inductive type"
  end.

Fixpoint nth_error' {A : Type} (l : list' A) (n : nat) {struct n} : option A :=
  match n with
      | 0 => match l with
                | nil' => None
                | cons' x _ => Some x
            end
      | S n0 => match l with
                   | nil' => None
                   | cons' _ l0 => nth_error' l0 n0
               end
  end.

Polymorphic Definition get_corresp_ctor {T T': Type} (tf : T') (t : T)
           `{ty : @QuoteTermOf _ t} : TemplateMonad typed_term@{Type} :=
  match ty with
      | tConstruct _ i _  =>
          terms <- get_ctors' tf;;
          t' <- tmEval cbv (nth_error' terms i);;
          match t' with
              | Some (_, t'') => tmReturn (t'' : typed_term)
              | None => tmFail "could not find matching constructor"
          end
      | _ => tmFail "type is not a tConstruct"
  end.




(** ind_gen' adapts [ind_gen] from idt.v to accomodate the changes made
   to the parameters of the new datatype. ind_gen' takes various bits
   of information about the source type and target functorial
   representation, and produces a deeply-embedded program in the
   TemplateMonad. Running MetaCoq over this program adds the new
   datatype definition to the environment. *)

Definition ind_gen' (T : Type) (name : ident) (ctors : list (ident * term))
           (mind : mutual_inductive_body) (i : nat) : TemplateMonad unit :=
  ty <- tmQuote T ;;
  match nth_error mind.(ind_bodies) i with
  | Some ind =>
      let npars := mind.(ind_npars) + 1 in
      let ctors := map (fun '(n, t) =>
                          let t' := try_remove_n_lambdas 1 t in
                          (n, t', count_tProds t' - npars)) ctors in
      let params := extract_params ty npars in
      (* let ty_ret := extract_ty_ret ty in *)
      let indparam := map (fun '(s, t) => mk_indparam s t) params in
      (* let param_terms := map snd params in *)
      (* let lvls := flat_map get_level (ty_ret :: param_terms) in *)
      let univ := Monomorphic_ctx (LevelSetProp.of_list [], ConstraintSet.empty) in
      let ind' :=
        {| ind_finite := mind.(ind_finite);
           ind_npars := mind.(ind_npars) + 1;
           ind_universes := univ;
           ind_variance := mind.(ind_variance);
           ind_params := indparam;
           ind_bodies := [ {| ind_name := name;
                              ind_type  := ty;
                              ind_kelim := ind.(ind_kelim);
                              ind_ctors := ctors;
                              ind_projs := ind.(ind_projs);
                              ind_relevance := ind.(ind_relevance) |} ]
        |}
      in
      tmMkInductive' ind'
  | _ => tmFail "No body found"
  end.

Definition getTerm (q : qualid) : TemplateMonad typed_term :=
  kn <- tmLocate1 q ;;
  match kn with
      | IndRef ind => tmUnquote (tInd ind [])
      | _ => tmFail ("[" ^ q ^ "] is not an inductive")
  end.

Definition ind_name {T : Type} (t : T) :=
          t <- tmQuote t;;
          name <- match t with
                     | tInd {| inductive_mind := (_, name) |} _ => tmReturn name
                     | _ => tmFail "not an inductive"
                 end;;
          tmReturn name.

Tactic Notation "tsf_ctors'" constr(ind) open_constr(tsf_ident) tactic3(tsf_ctor) :=
  run_template_program (get_ctors' ind)
                       (fun xs =>
                          let xs := eval simpl in xs in
                          let rec go xs :=
                            lazymatch xs with
                            | cons' (?name, (existT_typed_term _ ?ctor)) ?xs =>
                                let n := eval compute in (tsf_ident name) in
                                refine (cons' (n, _) _); [
                                  intros Hc R; tsf_ctor ctor R
                                | go xs ]
                            | _ => exact nil'
                            end
                          in go xs).

(* ----------------------------------------------------- *)

(** We start by defining some example datatypes that we to convert. We
   stick to Set for now in order to avoid dealing with universes.  *)

(** The first step in building a functor-based representation of a type is
   to build a new type that includes the functor's inductive parameter. *)

Ltac buildFunKind T :=
  let rec buildFunKind' K :=
  match K with
    (* Work our way down the kind of the source type: *)
        | forall (A : Type), ?M =>  refine (forall (A : Set), _); buildFunKind' M
        | forall (A :?Z), ?M =>  refine (forall (A : Z), _); buildFunKind' M
        (* Insert X as the last parameter of the new Functor: *)
        | ?U => exact (forall (X : Set), Set)
    end in
  let K := type of T in
  buildFunKind' K.

(** This helper function gets the codomain of a type. *)
Ltac codTy ty :=
  match ty with
  | forall (_ : _), ?U => codTy U
  | ?U => U
  end.

Definition to_upper_num := nat_of_ascii "a" - nat_of_ascii "A".

Definition to_upper c := ascii_of_nat ((nat_of_ascii c) - to_upper_num).

Definition fst_upper (s : string) :=
  match s with
      | EmptyString => EmptyString
      | String c s' => String (to_upper c) s'
  end.

(** This tactic constructs a deep embedding of the constructors for the
   functorial representation of the the type T, using X as the name for the parameter of the functor. *)
(** f is the function to be used to build the of the constructors
 *)
Ltac buildFunCtors X T f:=
  (* tsf_ctors T (fun s => append s "F") *)
  tsf_ctors' T f
             (fun c R => let R := eval cbn in R in
                      pose (ctor := c);
                      (* Now we refine each one of R parameters with `refine (forall A, _)` *)
                      (* And apply each one to R, to build its complete return type for each constructor *)
                      let rec rector ty := lazymatch ty with
                                               | forall (A : Set), ?U => refine (forall (A : Set), _);
                                                                   try specialize (ctor A);
                                                                   pose proof (R A) as R;
                                                                   rector U
                                               | forall (A : Type), ?U => refine (forall (A : Set), _);
                                                                   try specialize (ctor A);
                                                                   pose proof (R A) as R;
                                                                   rector U
                                               | _ => idtac
                                           end in
                      let Ty := type of R in
                      rector Ty;
                      let ctorTy := type of ctor in
                      (* We remember the type of the constructor as Cty *)
                      let Cty := codTy ctorTy in
                      (* Finally, to functorialize each constructor do the following: *)
                      let rec genFunCtor ty := lazymatch ty with
                                                   (* If Cty appears as a type, change it to X *)
                                                   | forall (A : Cty), ?U => refine (forall (A : X), _); genFunCtor U
                                                   (* Everything else remains unchanged *)
                                                   | forall A : ?S, ?U => refine (forall (A : S), _); genFunCtor U
                                                   (* If Cty appears as the return type, change it to R *)
                                                   | Cty => exact R
                                                                 (* TODO: Add other cases for more complex datatypes *)
                                               end in
                      genFunCtor ctorTy).


(* ------------------ Auxiliary Ltacs ------------------ *)

Notation "'unfolded' d" :=
  ltac:(let y := eval unfold d in d in exact y) (at level 100, only parsing).


Inductive ltac_Mark : Type :=
 | ltac_mark : ltac_Mark.

Ltac gen_until_mark :=
  match goal with H: ?U |- _ =>
  match U with
  | ltac_Mark => clear H
  | _ => generalize H; clear H; gen_until_mark
  end end.

Ltac intro_until_mark :=
  match goal with
  | |- (ltac_Mark -> _) => intros _
  | _ => intro; intro_until_mark
  end.

Ltac gen_mark :=
  let H := fresh in
  pose (ltac_mark) as H; generalize H.

Ltac clear_mark :=
  match goal with
      | [ H : ltac_Mark |- _ ] => clear H
      | _ => idtac
  end.

Inductive mainT : Type -> Set :=
  | mT : forall (T : Type), mainT T.

Ltac markT T :=
  match goal with
    | [ T : Set |- _ ] => pose (mT T)
    | [ T : Type |- _ ] => pose (mT T)
    | _ => idtac
  end.

Inductive Param : Set -> nat -> Type :=
| param : forall (A : Set) (n : nat), Param A n.

Ltac markparam H H' :=
  pose proof (param H) as H'.

Ltac mark_param S n :=
  let H := fresh "p" in
  pose (param S n) as H;
  simpl in H.

Ltac refine_params S :=
  let rec go U n := match U with
                      | forall (A : Set), ?V => refine (forall (A: Set), (_ : Set));
                                          mark_param A n;
                                          let n := eval simpl in (n+1) in
                                          go V n
                      | forall (A : Type), ?V => refine (forall (A: Set), (_ : Set));
                                          mark_param A n;
                                          let n := eval simpl in (n+1) in
                                          go V n
                      | _ => idtac
                  end in
  let SU := type of S in
  go SU constr:(0).

Ltac nparam S :=
  let rec go U n := match U with
                    | forall (A : Type), ?V => go V constr:(n+1)
                    | forall (A : Set), ?V => go V constr:(n+1)
                        | _ =>
                            let n := eval simpl in n in
                            exact n
                    end in
  let SU := type of S in
   go SU 0.

Ltac refine_params' S :=
  let rec go U n := match U with
                      | forall (A : Set), ?V => refine (forall (A: Set), (_ : Type));
                                          mark_param A n;
                                          let n := eval simpl in (n+1) in
                                          go V n
                      | forall (A : Type), ?V => refine (forall (A: Set), (_ : Type));
                                          mark_param A n;
                                          let n := eval simpl in (n+1) in
                                          go V n
                      | _ => idtac
                  end in
  let SU := type of S in
  go SU constr:(0).


Ltac buildApp U :=
  lazymatch goal with
      | [A : Set |- _ ] => refine (_ A); clear A; buildApp U
      | _ => exact U
  end.

Ltac buildParams U :=
  let rec go U n :=
    match goal with
        | [ H : Param ?A n |- _] =>
            let n := eval simpl in (n+1) in
            go (U A) n
      | _ => U
end in go U constr:(0).

Tactic Notation "build_params" open_constr(U) ">>" tactic(tac) :=
  let K := buildParams U in
  tac K.

Tactic Notation "build_params" open_constr(U) :=
  build_params U >> (fun K => let H := fresh "K" in pose K as H).

Tactic Notation "exact_build" open_constr(U) :=
  build_params U >> (fun K => exact K).

Ltac get_constr t :=
  match goal with
      | [ H : t = ?C |- _ ] => get_head C
  end.

Ltac countP U :=
  let rec go U n := match U with
                        | forall (_ : _), ?V => go V (n+1)
                        | _ =>
                            let n := eval simpl in n in
                            n
                    end
  in
  let t := type of U in
  go t 0.

Ltac number_to_nat N :=
  match type of N with
      | nat => constr:(N)
  end.

Ltac markfst n :=
  match reverse goal with
      | [ U : Set |- _ ] =>
          match goal with
            (* Don't mark if this is the main T *)
            | [ H : mainT U |- _ ] => idtac
              | _ =>
                  let H := fresh "param" in
                  let H1 := fresh in
                  gen_mark;
                  pose (param U n) as H;
                  generalize dependent U;
                  intro_until_mark; clear_mark
          end
      | _ => idtac
  end.

Ltac markN x :=
    let rec go x y :=  match number_to_nat x with
                           | 0 => markfst y
                           | S ?x' => markfst y;
                                     let y := eval simpl in (y+1) in
                                     go x' y
                       end in
    let x := eval simpl in (x - 1) in
   go x 0.

Ltac mark_params U :=
  let n := countP U in
  markN n.

Ltac introN n :=
  match n with
      | 0 => idtac
      | S ?x' => intro; introN x'
  end.

Ltac intro_params U :=
  let n := countP U in
  let n := eval simpl in n in
introN n; markN n.

Ltac func_params :=
  let rec go n := match goal with
                      | |- forall (A : Set), ?V => refine (fun (A: Set) => _);
                                          mark_param A n;
                                          let n := eval simpl in (n+1) in
                                          go n
                      | |- forall (A : Type), ?V => refine (fun (A: Set) => _);
                                          mark_param A n;
                                          let n := eval simpl in (n+1) in
                                          go n
                      | _ => idtac
                  end in
  go constr:(0).


(* ------------- LTacs to build definitions ------------ *)

Ltac tfmap_kind T TF :=
  markT T;
  refine_params T; refine (forall X1 X2, FmapT X1 X2 _); exact_build TF .

Ltac tfmap T :=
  markT T;
  intro_params T;
  unfold FmapT;
  let X1 := fresh "X" in
  let X2 := fresh "X" in
  let f := fresh "f" in
  let t := fresh "t" in
  intros X1 X2 f t;
  let ct := fresh "ct" in
  pose t as ct;
  destruct t;
  let c := eval unfold ct in ct in
  let constr := get_head c in
  let rec go x := match x with
                      | ?K ?a => match type of a with
                                   | X1 => refine (_ (f a)); go K
                                   | _ => match a with
                                             | X1 => refine (_ X2); go K
                                             | _ => refine (_ a); go K

                                         end
                               end
                      | _ => exact constr
                  end
  in
  go c.

Ltac tfFunctor_kind T TF :=
  markT T;
  refine_params T; build_params TF >> (fun K => exact (Functor K)).

Tactic Notation "tfMapId_kind" constr(T) constr(TF) constr(tfmap) :=
  markT T;
  refine_params T;
  build_params TF >>
    (fun H => build_params tfmap >>
    (fun M => exact (FmapId H M))).

Ltac tfMapId T TF :=
  markT T;
  unfold FmapId;
  intros;
  match goal with
      | [ t : context[TF] |- _ ] => destruct t
  end; reflexivity.

Ltac tfFunctor T tfMapId :=
  markT T;
  repeat intro; refine {| fmap := _ ; fmapId := _ |}; apply tfMapId.

Ltac dctf_kind T :=
  markT T;
  refine_params' T; exact Set.

Ltac dctf T TF :=
  markT T;
  repeat intro; mark_params T;
  refine (Dc _); exact_build TF.

Ltac intf_kind T TF DCTF :=
  markT T;
  refine_params T;
  build_params DCTF >>
               (fun K => build_params TF >>
                (fun K' => refine (K' K -> K))).

Ltac intf T TF :=
  markT T;
  repeat intro;
  mark_params T;
  build_params TF >> (fun K => refine (@inDc K ltac:(assumption))).

Ltac outtf_kind T TF DCTF :=
  markT T;
  refine_params T;
  build_params DCTF >> (fun K => build_params TF >> (fun K' => exact (K -> K' K))).

Ltac outtf T TF DCTF TFunctor :=
  markT T;
  repeat intro;
  mark_params T;
  match goal with
      | H : context[DCTF] |- _ => revert H
  end;
  build_params TF >>
  (fun TFApp => build_params TFunctor >>
    fun funct => refine (@out TFApp funct _ (sfold TFApp))).

(* ----------------------------------------------------- *)

Ltac clear_params :=
  repeat match goal with
           | [ H : Param _ _ |- _ ] => clear H
         end.

Ltac tfold_kind T TF :=
  markT T;
  refine_params T;
  build_params T >>
  (fun PT => build_params TF >>
  (fun PTF => let fresh X := fresh "X" in
           clear_params;
           exact (forall (t : PT) (X : Set) (alg : PTF X -> X), X))).

Ltac intro_param_lets T :=
  let n := countP T in
  let n := eval simpl in (n+n) in
  introN n.

Ltac buildFold T TF :=
  markT T;
  simpl; intro_params T;
  let alg := fresh "alg" in
  intros ? ? alg;
  let fold := fresh "fold" in
  (* let T' := eval unfold T in T in *)
  let H' := fresh in
  match goal with
      (* We find the argument that has type T, define it's fixpoint and destruct it *)
      | [ H : context[T] |- _ ] =>
          let ty := type of H in
          revert H;
          (* pose ty as H'; *)
          let t := fresh "t" in
          refine (fix fold (t : ty) := _);
          pose t as H';
          destruct H ;
          (* The head of the match is alg *)
          refine (alg _)
  end;
  let C1 := eval unfold H' in H' in
  let constr := get_head C1 in
  let rec go D :=
    let D := eval cbv in D in
  match D with
      | ?lhs ?rhs =>
          let ty := type of rhs in
          (* Match through the arguments of C *)
          lazymatch ty with
              (* If T shows up, fold it *)
              | context[T] =>
                  refine (_ (fold rhs));
                  go lhs

              | _ =>
                  refine (_ rhs);
                  go lhs
          end

      | constr => repeat match goal with
                            | |- forall A : Set, _ => intro
                        end;
                 run_template_program (get_corresp_ctor TF constr)
                                      (fun c => let c := eval cbv in (my_projT2 c) in apply c)
      | _ => idtac
  end in go C1.

Ltac tfoldT_kind T :=
  markT T;
  refine_params' T;
  let R := fresh "R" in
  refine (forall (R : Set), Set).

Ltac tfoldT T TF alg :=
  markT T;
  simpl; intro_params T;
  build_params TF >> (fun K => exact (FoldT (alg K))).

Ltac toDCTF_kind T DCTF :=
  markT T;
  refine_params T;
  build_params T >> (fun PT => build_params DCTF >> (fun PDCTF =>
                    exact (PT -> PDCTF))).

Ltac toDCTF T DCTF TFold :=
  markT T;
  simpl;
  intro_params T;
  let t := fresh "t" in intro t;
  build_params TFold >> (fun PTFold => refine (PTFold t _ (inDc _))).

Ltac fromDCTFr_kind T TFoldT :=
  markT T;
  refine_params T;
  let R := fresh "R" in let fo := fresh "fo" in
  (build_params TFoldT >>
  (fun PTFoldT => refine (forall (R : Set) (fo : PTFoldT R), (_ : Set))));
  match goal with
      | [ A : Set |- _ ] => refine (A -> _)
  end;
  exact_build T.

Ltac fromdctfr T TFMap :=
  markT T;
  simpl;
  intro_params T;
  let R := fresh "R" in
  let fo := fresh "fo" in
  let H := fresh in
  intros R fo H;
  refine (fo (Const _) (FunConst _) _ H);
  apply rollAlg;
  let rc := fresh "rec" in
  let fr := fresh "fr" in
  let tfmap := fresh "tfmap" in
  intros ? ? ? rc fr;
  pose proof TFMap as tfmap;
  eapply tfmap in rc;
  apply rc in fr;
  pose ltac_mark;
  destruct fr eqn:?H;
  unfold Const in *;
  match goal with
      | [H : ?t = ?C |- _ ] =>
          clear H;
          let h := ltac:(get_head C) in
          let H1 := fresh in
          gen_until_mark;
          run_template_program (get_corresp_ctor T h)
                               (fun xs => let xs := eval simpl in (my_projT2 xs) in
                                       apply xs)
      end.

Ltac fromDCTF_kind T DCTF :=
  markT T;
  refine_params T;
  build_params DCTF >> (fun PDCTF => build_params T >> (fun PT => exact (PDCTF -> PT))).

Ltac fromDCTF T TF fromDCTFr :=
  markT T;
  simpl;
  intro_params T;
  let H := fresh in
  intro H;
  build_params fromDCTFr >>
               (fun f => build_params TF >>
               (fun TFP => exact (f (Dc.Dc TFP) (fold TFP) H))).

Ltac mkkinds T TF DCTF :=
  markT T;
  let rec rparams U H :=
    lazymatch U with
        | forall (A : ?S), ?V =>
            let x := fresh "x" in
            refine (forall (x : S), (_ : Set));
            specialize (H x);
            rparams V H
        | _ => idtac
    end in
  let rec process xs :=
    lazymatch xs with
        | (?name, (existT_typed_term _ ?ctor)) :: ?xs =>
            refine (_ :: _);
            [ refine_params T;
              build_params DCTF >>
              (fun D => build_params ctor >>
              (fun K => let H := fresh "K" in
                     (* Instantiate X of ctor with DCTF *)
                     pose proof (K D) as H;
                     let Kty := type of H in
                     (* refine the arguments of ctor *)
                     rparams Kty H;
                     (* returns DCTF *)
                     exact D
              ))
                | process xs ]
        | _ => exact []
    end
  in run_template_program (get_ctors TF)
                          (fun xs => let xs := eval simpl in xs in process xs).


Ltac smart_constrs T TF DCTF inTF :=
  markT T;
  let rec process xs :=
    lazymatch xs with
        | (?name, (existT_typed_term _ ?ctor)) :: ?xs =>
            refine (HCons _ _ _); [ exact (append "mk" name) |
              simpl; func_params;
              (* Instantiate the parameters of C and DCTF *)
              build_params DCTF >>
              (fun D => build_params ctor >>
              fun ctor => let H := fresh "K" in
                       pose (ctor D) as H;
                       (* Instantiate the arguments of the constructor one by one *)
                       repeat (let A := fresh "arg" in intro A; specialize (H A); clear A);
                       apply inTF; exact H
              )
                | process xs]
        | _ => exact HNil
    end in
  run_template_program (get_ctors TF)
                       (fun xs => let xs := eval simpl in xs in
                              process xs).


Ltac tsf_ctors_to_tm' ctors :=
  let rec go xs :=
    lazymatch xs with
    | cons' (?n, ?ctor) ?xs =>
        lazymatch ctor with
        | (fun _ => ?P) =>
            lazymatch P with
            | (fun _ => tsf_skip_marker) => idtac
            | _ => quote_term P (fun P => refine ((n, P) :: _))
            end
        end; go xs

    | _ => refine ([])
    end in
  (* Not ideal. If parts of [ctors] are defined as definitions, we need to
  use [Arguments] to instruct [cbn] to unfold those definitions. *)
  let xs := eval cbn in ctors
    in go xs.

Notation gen_functor T TName f :=
  (let newFunSig : Type := ltac:(buildFunKind T) in
   let newFunCtors : tsf_ctors_ty' (unfolded newFunSig) :=
     ltac:(let X := fresh in buildFunCtors X T f) in
   '(mind, i) <- tsf_get_mind ltac:(quote_term T (fun t => exact t));;
   (* Quotes the new types of the constructors into metacoq *)
   let ctorsT := ltac:(tsf_ctors_to_tm' (unfolded newFunCtors)) in
   (* Synthesize the functorial representation of T as Fname *)
   ind_gen' (unfolded newFunSig) TName ctorsT mind i)
   (only parsing).

Notation gen_functor_defs_named T TF mapname mapidname functorname
  dcname inname outname foldname foldTname sfoldTname toname fromrname froname :=
  (let TFMap : ltac:(tfmap_kind T TF) := ltac:(tfmap T) in
  let TFMapId : ltac:(tfMapId_kind T TF TFMap) := ltac:(tfMapId T TF) in
  let TFunctor : ltac:(tfFunctor_kind T TF) := ltac:(tfFunctor T TFMapId) in
  let DCTF : ltac:(dctf_kind T) := ltac:(dctf T TF) in
  let inTF : ltac:(intf_kind T TF DCTF) := ltac:(intf T TF) in
  let outTF : ltac:(outtf_kind T TF DCTF) := ltac:(outtf T TF DCTF TFunctor) in
  let tFold : ltac:(tfold_kind T TF) := ltac:(buildFold T TF) in
  let tFoldT : ltac:(tfoldT_kind T) := ltac:(tfoldT T TF Alg) in
  let tsFoldT : ltac:(tfoldT_kind T) := ltac:(tfoldT T TF SAlg) in
  let toDCTF : ltac:(toDCTF_kind T DCTF) := ltac:(toDCTF T DCTF tFold) in
  let fromdctfr : ltac:(fromDCTFr_kind T tFoldT) := ltac:(fromdctfr T TFMap) in
  let fromdctf : ltac:(fromDCTF_kind T DCTF) := ltac:(fromDCTF T TF fromdctfr) in
  let mk_kinds : list Type := ltac:(mkkinds T TF DCTF) in
  let mks : hlist mk_kinds := ltac:(smart_constrs T TF DCTF inTF) in
  let tfname := functorname in
  (* Declare Definitions *)
  tmDefinition mapname TFMap;;
  tmDefinition mapidname TFMapId;;
  tmDefinition tfname TFunctor;;
  currModPath <- tmCurrentModPath tt;;
  tmExistingInstance (ConstRef (currModPath, tfname));;
  tmDefinition dcname DCTF;;
  tmDefinition inname inTF;;
  tmDefinition outname outTF;;
  tmDefinition foldname tFold;;
  tmDefinition foldTname tFoldT;;
  tmDefinition sfoldTname tsFoldT;;
  tmDefinition toname toDCTF;;
  tmDefinition fromrname fromdctfr;;
  tmDefinition froname fromdctf;;
  (* Define the smart constructors *)
  hmap mk_kinds mks tmDefinition;;
  tmReturn tt) (only parsing).

Notation gen_functor_defs T TF :=
  (TFName <- ind_name TF;;
   let mapname := (TFName ^ "Map") in
   let mapidname := (TFName ^ "MapId") in
   let functorname := (TFName ^ "Functor") in
   let dcname := ("DC" ^ TFName) in
   let inname := ("in_" ^ TFName) in
   let outname := ("out_" ^ TFName) in
   let foldname := (TFName ^ "Fold") in
   let foldTname := (TFName ^ "FoldT") in
   let sfoldTname := (TFName ^ "SFoldT") in
   let toname := ("to_" ^ TFName ^ "DC") in
   let fromrname := ("from_" ^ TFName ^ "DCr") in
   let fromname := ("from_" ^ TFName ^ "DC") in
   gen_functor_defs_named T TF mapname mapidname functorname dcname inname outname
                          foldname foldTname sfoldTname toname fromrname fromname)
  (only parsing).
