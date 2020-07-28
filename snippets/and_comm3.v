Require Import Coq.Unicode.Utf8. (* .none *)
Lemma and_comm : ∀ A B, A ∧ B → B ∧ A.
  tauto.
Qed.
