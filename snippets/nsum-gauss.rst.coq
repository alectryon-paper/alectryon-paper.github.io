(*|
.. coq:: none
|*)

Require Import Coq.Unicode.Utf8. (* .none *)
Require Import NArith ArithRing.

Fixpoint nsum max f :=
  match max with
  | O => f 0
  | S max' => f max + nsum max' f
  end.

(*|
.. include:: latex.rest

.. coq:: none
|*)

Notation "'\ccNsum{' x '}{' max '}{' f '}'" :=
  (nsum max (fun x => f))
    (format "'\ccNsum{' x '}{' max '}{' f '}'").

(*||*)

Lemma Gauss: ∀ n,
    2 * (nsum n (fun i => i)) = n * (n + 1).
  induction n; cbn [nsum].
  - (* n ← 0 *)
    reflexivity.
  - (* n ← S _ *)
    rewrite Mult.mult_plus_distr_l.
    rewrite IHn.
    ring.
Qed.
