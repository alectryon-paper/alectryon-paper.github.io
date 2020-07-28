Require Import Coq.Unicode.Utf8. (* .none *)
Lemma and_comm0 : ∀ A B, A ∧ B → B ∧ A.
  intros A B ab.
  destruct ab as (a, b).
  constructor. apply b. apply a.
Qed.

Lemma and_comm1 : ∀ A B, A ∧ B → B ∧ A.
  intros ? ? (? & ?).
  split. all: assumption.
Qed.

Lemma and_comm2 : ∀ A B, A ∧ B → B ∧ A.
  tauto.
Qed.
