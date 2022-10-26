(** * Well-Founded WordsBy, using Equations *)
(** As discussed in paper (Section 3.2), we implement [WordsBy] using the
[Equations] package.*)
Require Import Program Coq.Lists.List Psatz.
From Equations Require Import Equations Signature.
Local Open Scope list_scope.

Require Import WordsByWf.
Require Import NatWf.

Section WordsByEq.

  Variable A : Set.
  Variable p : A -> bool.

Definition inspect {A} (a : A) : {b | a = b} :=
  exist _ a eq_refl.

Equations? wordsByE (l:list A) : list (list A) by wf (length l) lt :=
 wordsByE nil := nil ;
 wordsByE (hd::tl) with p hd => {
   | true := wordsByE tl;
   | false with inspect (break A p tl) => {
     | exist ?(_) (w,z) e  := (hd::w)::(wordsByE z)
     }
   }.
apply Lt.le_lt_n_Sm.
apply (span_snd_smaller A (fun x => negb (p x)) tl w z).
unfold break in e; assumption.
  Qed.

Equations? wordsByEn (l:list A) : list (list A) by wf l (ltof (list A) (@length A)) :=
 wordsByEn nil := nil ;
 wordsByEn (hd::tl) with p hd => {
   | true := wordsByEn tl;
   | false with inspect (break A p tl) => {
     | exist ?(_) (w,z) e  := (hd::w)::(wordsByEn z)
     }
   }.
+ unfold ltof; simpl; lia.
+ unfold ltof; simpl. apply Lt.le_lt_n_Sm. apply (span_snd_smaller A (fun x => negb (p x)) tl w z).
  unfold break in e; assumption.
  Qed.

(*
Print wordsByE. (* 3 *)
Print wordsByE_functional. (* 8 *)
Print wordsByE_clause_2. (* 10 *)
Print wordsByE_obligation_1. (* 5 *)
Print wordsByE_clause_2_clause_2. (* 13 *)
Print wordsByE_obligation_2. (* 11 *)
*)

End WordsByEq.

Arguments wordsByE{A}.
Arguments wordsByEn{A}.
