Require Import Coq.Unicode.Utf8. (* .none *)
Section classical. (* .none *)
  Context (excl: ∀ A, A ∨ ~ A).
  Goal ∀ A, ¬¬A → A.
    intros A notnot_A.
    Show Proof. (* .messages .unfold *)
    destruct (excl A) as [a | na].
    Show Proof. (* .messages .unfold *)
    - assumption.
      Show Proof. (* .messages .unfold *)
