Require Import Coq.Unicode.Utf8. (* .none *)
Lemma ge0 : ∀ n, 0 ≤ n.
  induction n. (* .unfold *)
  - (* n ← 0 *)
    constructor.
  - (* n ← S _ *)
    Fail exact IHn. (* .unfold .fails .no-goals *)
    constructor.
    assumption.
Qed.
