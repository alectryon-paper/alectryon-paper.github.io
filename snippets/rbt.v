(*|
.. coq:: none
|*)

Require Import
        Coq.MSets.MSetRBT
        Coq.Arith.Arith
        Coq.Structures.OrderedTypeEx
        Coq.Structures.OrdersAlt.

Require Import Coq.Lists.List.
Import ListNotations.

Module Nat_as_OT := Update_OT Nat_as_OT.

(*||*)

Module RBT := MSets.MSetRBT.Make Nat_as_OT.

(*|
.. coq:: none
|*)

Notation "'{' ''kind':' ''node'' ; ''color':' ''' color ''' ; ''value':' ''' value ''' ; ''left':' left ; ''right':' right '}'" :=
  (RBT.Raw.Node color left value right)
    (format  "'{'  ''kind':' ''node'' ;  ''color':'  ''' color ''' ;  ''value':'  ''' value ''' ;  ''left':'  left ;  ''right':'  right  '}'").

Notation "'{' ''kind':' ''leaf'' '}'" :=
  (RBT.Raw.Leaf).

Notation "'{' ''tree':' this '}'" :=
  {| RBT.this := this |}.

(* Require Import Extraction. *)
(* Extraction Language JSON. *)

Notation "v |> f" := (f v) (at level 10).
Arguments List.rev {A}.

(*||*)

Definition build_trees (leaves: list nat) :=
  List.fold_left (fun trs n =>
      RBT.add n (hd RBT.empty trs) :: trs)
    leaves [] |> List.rev.

Compute build_trees [1;2;3;4;5;6]. (* .unfold *)

Compute build_trees [2;1;4;3;6;5]. (* .unfold *)

Compute build_trees [6;5;4;1;2;3]. (* .unfold *)

(*|
.. raw:: html

   <script src="https://d3js.org/d3.v5.min.js" charset="utf-8"></script>
   <script src="https://dagrejs.github.io/project/dagre-d3/latest/dagre-d3.js"></script>

   <link rel="stylesheet" href="rbt.css">
   <script type="text/javascript" src="rbt.js"></script>
|*)
