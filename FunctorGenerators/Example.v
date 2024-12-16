(** * Example Functorialization of list and tree datatypes. *)
Require Import Functorializer.
Require Import Induction.

(** We start by defining some example datatypes that we want to convert. *)

Inductive list' (A : Set) : Set :=
| nil'  : list' A
| cons' : A -> list' A -> list' A.

#[universes(template)]
Inductive tree (A : Type) : Type :=
| mempty : tree A
| mnode : A -> tree A -> tree A -> tree A.

Definition Const(T: Set) : Set -> Set := fun _ => T.

(** Here are the kinds for the functorialization of lists, trees, and
   strings (these strings are from the standard library): *)
Example listF_Kind : Type := ltac:(buildFunKind list').
Print listF_Kind.

Example treeF_Kind : Type := ltac:(buildFunKind tree).
Print treeF_Kind.

Example stringF_Kind : Type := ltac:(buildFunKind string).
Print stringF_Kind.

(** Generating some example constructor descriptions for the
   functorialization of lists, trees, and strings: *)
Example listF_emb : tsf_ctors_ty' ltac:(buildFunKind list') :=
  ltac:(let X := fresh in buildFunCtors X list' fst_upper).
Eval compute in listF_emb.

Example treeF_emb : tsf_ctors_ty' ltac:(buildFunKind tree) :=
  ltac:(let X := fresh in buildFunCtors X tree fst_upper).

Example stringF_emb : tsf_ctors_ty' ltac:(buildFunKind string) :=
  ltac:(let X := fresh in buildFunCtors X string (fun s => append s "F")).

(** Generate the functorial representaion of lists: *)
MetaCoq Run (gen_functor list "listF" fst_upper).
Print listF.

(** We can also generate the functorial representation of other types *)
MetaCoq Run (gen_functor string "stringF" (fun s => append s "F")).
MetaCoq Run (gen_functor tree "treeF" fst_upper).

Print stringF.
Print treeF.

(** We can also generate the definitions associated with each functorial representation
   such as smart constructors, the Functor instance, Fold and more *)
Definition gen_stringF_defs := gen_functor_defs string stringF.
MetaCoq Run (gen_stringF_defs).

Definition gen_listF_defs := gen_functor_defs list listF.
MetaCoq Run (gen_listF_defs).

Definition gen_treeF_defs := gen_functor_defs tree treeF.
MetaCoq Run (gen_treeF_defs).

(* We also provide a version of gen_functor_defs to give more control of the generated names *)
(* Ltac Debug. *)

MetaCoq Run (gen_functor list' "ListF" fst_upper).

Definition gen_ListF_defs :=
  gen_functor_defs_named list' ListF "Listmap" "ListmapId" "FunListF" "List"
                         "inList" "outList" "listFold" "ListFoldT" "ListSFoldT"
                         "toList" "fromListr" "fromList".

MetaCoq Run (gen_ListF_defs).

(* Generates the Induction Principles *)
MetaCoq Run (gen_motive "lkMo" list' List).
Print lkMo.

MetaCoq Run (gen_induction list' ListF lkMo "ListFi").
Print ListFi.

MetaCoq Run (gen_motive "treeKMo" tree DCtreeF).
Print treeKMo.

MetaCoq Run (gen_induction tree treeF treeKMo "TreeFi").
Print TreeFi.
