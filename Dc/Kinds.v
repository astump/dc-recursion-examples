(** * Kinds *)
(** Both algebras and subsidiary algebras have kind [KAlg]. [KAlgi] is its
dependent counterpart. *)

Definition KAlg  : Type := (Set -> Set) -> Set.

Section Ind.
 Variable I : Set.
 Definition kMo := I -> Prop.
 Definition KAlgi := (kMo -> kMo) -> Set.
End Ind.
