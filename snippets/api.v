Let inv b: negb (negb b) = b.
  destruct b. all: reflexivity.
Qed.
Print Assumptions inv.
