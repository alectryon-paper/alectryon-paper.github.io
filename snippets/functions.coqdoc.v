(** * Function types

Implications ([P → Q]) are a kind of
_universal quantification_ ([∀ x, P]): *)

Require Import Coq.Unicode.Utf8. (* .none *)
Set Printing All. (* .none *)
Check (False → True). (* .unfold *)
