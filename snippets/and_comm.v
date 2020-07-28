Require Import Coq.Unicode.Utf8. (* .none *)
Definition and_comm : ∀ A B, A ∧ B → B ∧ A :=
  fun A B ab => conj (proj2 ab) (proj1 ab).
