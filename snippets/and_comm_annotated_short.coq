(** The [∧] operator commutes: **)
Lemma and_comm : ∀ A B, A ∧ B → B ∧ A.
  intros A B ab.
  (** <<
  A, B : Prop
  ab : A ∧ B
  ============================
  B ∧ A >> **)
  destruct ab as (a, b). …
