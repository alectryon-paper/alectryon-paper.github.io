Require Import Coq.Unicode.Utf8. (* .none *)
Require Import Coq.Arith.Arith. (* .none *)
Fixpoint sum upto := (* .none *)
  match upto with
  | O => 0
  | S upto' => upto + sum upto'
  end.
Lemma Gauss:
  ∀ n, 2 * (sum n) = n * (n + 1).
Proof.
  induction n.
  - (* n ← 0 *)
    reflexivity.
  - (* n ← S _ *)
    cbn [sum].
    rewrite Mult.mult_plus_distr_l.
    rewrite IHn.
    change (S n) with (1 + n).
    rewrite !Mult.mult_plus_distr_l.
    rewrite !Mult.mult_plus_distr_r.
    cbn [Nat.mul];
      rewrite !Nat.mul_1_r, !Nat.add_0_r.
    rewrite !Nat.add_assoc.
    change (1 + 1) with 2.
    rewrite !(Nat.add_comm _ 1).
    rewrite !Nat.add_assoc.
    change (1 + 1) with 2.
    reflexivity.
Qed.
