.. raw:: html

   <!-- Emulate no CSS by dropping all stylesheets -->
   <script type="text/javascript">
     document.querySelectorAll('link').forEach(link => link.parentNode.removeChild(link));
   </script>

.. coq::

   Require Import List. (* .none *)

   Lemma rev_rev {A} (l: list A) : List.rev (List.rev l) = l.
     induction l; cbn.
     - (* l ← [] *)
       reflexivity.

     - (* l ← _ :: _ *)
       rewrite rev_app_distr. (* .no-hyps *)
       rewrite IHl. (* .no-hyps *)
       cbn. (* .no-hyps *)
       reflexivity.
   Qed.
