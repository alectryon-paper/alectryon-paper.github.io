``Let`` introduces a local definition:

.. coq::

   Section A. Let a := 1. End A.
.. coq:: unfold fails

   Fail Check a.

.. note::

   Outside sections, ``Let`` will print a warning.

.. coq::

   Let a' := 1.
