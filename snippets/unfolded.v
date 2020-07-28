Require Import List. (* .none *)
Lemma rev_rev {A} (l: list A) : List.rev (List.rev l) = l.
Proof.
  induction l; cbn.
  - (* l ← [] *)
    reflexivity.
  - (* l ← _ :: _ *) (* .unfold *)
    rewrite rev_app_distr. (* .unfold .no-hyps *)
    rewrite IHl. (* .unfold .no-hyps *)
    cbn. reflexivity.
Qed.
