Require Import Coq.Unicode.Utf8. (* .none *)
Tactic Notation "…" := idtac. (* .none *)
Goal ∀ n: nat, n = n. (* .none *)
induction n.
- (* n ← 0 *) …. (* .in *)
  reflexivity. (* .none *)
- (* n ← S _ *) …. (* .in *)
  reflexivity. (* .none *)
Qed. (* .none *)
