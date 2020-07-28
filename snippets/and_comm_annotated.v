Require Import Coq.Unicode.Utf8. (* .none *)
Lemma and_comm : ∀ A B, A ∧ B → B ∧ A.
  intros A B ab.
  (* A, B: Prop, ab: A ∧ B |- B ∧ A *)
  destruct ab as (a, b).
  (* A, B: Prop, a: A, b: B |- B ∧ A *)
  constructor.
  - (* A, B: Prop, a: A, b: B |- B *)
    apply b.
  - (* A, B: Prop, a: A, b: B |- A *)
    apply a.
Abort.
