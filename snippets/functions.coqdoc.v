(** * Function types

Implications ([P → Q]) are
_universal quantifications_ ([∀ x, Q]): *)

Require Import Coq.Unicode.Utf8. (* .none *)
Set Printing All. (* .none *)
Check (False → True). (* .unfold *)
