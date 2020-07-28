(*|
Booleans
========

The built-in :coqid:`Boolean <Coq.Init.Datatypes.bool>`
type has two constructors:

.. coq:: unfold no-in
|*)

Print bool.

(*|
.. topic:: Induction principles

   Coq automatically defines an induction principle:

   .. coq:: unfold
|*)

Search (∀ b: bool, _ b) "_ind".
