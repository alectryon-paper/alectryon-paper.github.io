Require Import Coq.Unicode.Utf8. (* .none *)
Lemma and_comm : forall A B, A /\ B -> B /\ A.
  intros A B ab.
  destruct ab as (a, b).
  constructor. apply b. apply a.
Qed.
