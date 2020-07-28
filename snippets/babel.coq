(* xyzT *)

(* [[file:~/documents/mit/plv/blog/alectryon/paper/demos/babel-coq.org::*xyz][xyz:1]] *)
Definition b := 1.
(* xyz:1 ends here *)

(* abc *)

(* [[file:~/documents/mit/plv/blog/alectryon/paper/demos/babel-coq.org::*abc][abc:1]] *)
Goal True ∧ True.
  split.
  - exact I.
  - enough (1 + 1 = 2).
    + exact I.
    + reflexivity.
Qed.
(* abc:1 ends here *)
