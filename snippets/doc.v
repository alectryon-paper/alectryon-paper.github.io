(*|
Booleans
========

The built-in :coqid:`Boolean <Coq.Init.Datatypes.bool>`
type has two constructors:
|*)

Print bool. (* .unfold .no-in *)

(*|
.. topic:: Induction principles

   Coq automatically defines an induction principle:
|*)

Require Import Coq.Unicode.Utf8. (* .none *)
Search (∀ b: bool, _ b) "_ind". (* .unfold *)
