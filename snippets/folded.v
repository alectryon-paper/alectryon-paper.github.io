Require Import List. (* .none *)
Lemma rev_rev {A} (l: list A) : List.rev (List.rev l) = l.
Proof.
  induction l; cbn.
  - (* l ← [] *)
    reflexivity.
  - (* l ← _ :: _ *)
    rewrite rev_app_distr.
    rewrite IHl.
    cbn. reflexivity.
Qed.
