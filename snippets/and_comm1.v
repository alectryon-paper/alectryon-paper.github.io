Require Import Coq.Unicode.Utf8. (* .none *)
Lemma and_comm : ∀ A B, A ∧ B → B ∧ A.
  repeat match goal with
    | [          |- ∀ _, _ ] => intros
    | [          |- _ ∧ _  ] => split
    | [ H: _ ∧ _ |- _      ] => destruct H
    | [ H: ?a    |- ?a     ] => assumption
  end.
Qed.
