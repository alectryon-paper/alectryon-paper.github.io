(*|
.. coq:: none
|*)

Require Import Int63.

Module Type Array.
  Axiom array: Type -> Type.

  Parameter make : forall A, int -> A -> array A.
  Arguments make {_} _ _.

  Parameter get : forall A, array A -> int -> A.
  Arguments get {_} _ _.

  Parameter default : forall A, array A -> A.
  Arguments default {_} _.

  Parameter set : forall A, array A -> int -> A -> array A.
  Arguments set {_} _ _ _.

  Parameter length : forall A, array A -> int.
  Arguments length {_} _.

  Parameter copy : forall A, array A -> array A.
  Arguments copy {_} _.

  Declare Scope array_scope.
  Delimit Scope array_scope with array.
  Notation "t .[ i ]" :=
    (get t i)
      (at level 2, left associativity, format "t .[ i ]").
  Notation "t .[ i <- a ]" :=
    (set t i a)
      (at level 2, left associativity, format "t .[ i <- a ]").

  (* Local Open Scope int63_scope. *)
  (* Axiom get_set_same : forall A t i (a:A), (i < length t) = true -> t.[i<-a].[i] = a. *)
  (* Axiom get_set_other : forall A t i j (a:A), i <> j -> t.[i<-a].[j] = t.[j]. *)
End Array.

Require Import Coq.Lists.List.

Module ListArray <: Array.
  Import ListNotations.

  Record _array {A: Type} :=
    { arr_data: list A;
      arr_default: A }.
  Arguments _array : clear implicits.
  Definition array := _array.

  Definition nat_of_int i := BinInt.Z.to_nat (Int63.to_Z i).
  Definition int_of_nat n := Int63.of_Z (BinInt.Z.of_nat n).

  Definition make {A: Type} (l: int) (a: A) : array A :=
    let mk :=
        fix mk (l: nat) {struct l} :=
          match l with
          | 0 => []
          | S l => a :: mk l
          end in
    {| arr_data := mk (nat_of_int l);
       arr_default := a |}.

  Local Open Scope int63_scope.

  Definition length {A} (x: array A) :=
    int_of_nat (List.length x.(arr_data)).

  Definition get {A} (x: array A) (i: int) :=
    let get :=
        fix get (l: list A) (i: int) {struct l} :=
          match l with
          | [] => x.(arr_default)
          | hd :: tl =>
            if i == 0 then hd else get tl (i - 1)
          end in
    get x.(arr_data) i.

  Definition default {A} (x: array A) :=
    x.(arr_default).

  Definition set {A} (x: array A) (i: int) (a: A) : array A :=
    let set :=
        fix set (i: int) (l: list A) {struct l} :=
          match l with
          | [] => []
          | hd :: tl =>
            if i == 0 then a :: tl else hd :: set (i - 1) tl
          end in
    {| arr_data := set i x.(arr_data);
       arr_default := x.(arr_default) |}.

  Definition copy {A} (x: array A) : array A := x.

  Declare Scope array_scope.
  Delimit Scope array_scope with array.
  Notation "t .[ i ]" :=
    (get t i)
      (at level 2, left associativity, format "t .[ i ]").
  Notation "t .[ i <- a ]" :=
    (set t i a)
      (at level 2, left associativity, format "t .[ i <- a ]").
End ListArray.

Import ListArray.

Definition board := array (array bool).

Definition bget (b: board) x y :=
  b.[y].[x].

Open Scope int63.
Import ListNotations.
Import Bool.

Definition bi (b: board) x y :=
  b2i (bget b x y).

Definition neighbors (b: board) x y :=
  [bget b (x - 1) (y - 1); bget b (x) (y - 1); bget b (x + 1) (y - 1);
   bget b (x - 1) (y)    ; bget b (x) (y)    ; bget b (x + 1) (y)    ;
   bget b (x - 1) (y + 1); bget b (x) (y + 1); bget b (x + 1) (y + 1)].

Definition live_neighbors (b: board) x y :=
  bi b (x - 1) (y - 1) + bi b (x) (y - 1) + bi b (x + 1) (y - 1) +
  bi b (x - 1) (y)     +                    bi b (x + 1) (y)     +
  bi b (x - 1) (y + 1) + bi b (x) (y + 1) + bi b (x + 1) (y + 1).

  (* List.fold_left *)
  (*   (fun acc (x: bool) => if x then (acc + 1) else acc) *)
  (*   (neighbors b x y) 0 *)

Definition step_one (b: board) x y :=
  let live := live_neighbors b x y in
  if bget b x y then
    orb (live == 2) (live == 3)
  else
    (live == 3).

Definition iter {B} (n: int) (b: B) (f: int -> B -> B) :=
  let it :=
      fix it (fuel: nat) (idx: int) (b: B) {struct fuel} :=
        match fuel with
        | 0 => b
        | S fuel => it fuel (idx - 1)%int63 (f idx b)
        end
  in it (nat_of_int n) (n - 1)%int63 b.

Definition make_board (sz: int) (f: int -> int -> bool) :=
  iter sz (make sz (make sz false))
       (fun y board =>
          set board y
              (iter sz (make sz false)
                    (fun x row =>
                       set row x (f x y)))).

Definition init (l: list (list bool)) :=
  make_board
    (int_of_nat (List.length l))
    (fun x y => List.nth_default
               false
               (List.nth_default [] l (nat_of_int y))
               (nat_of_int x)).

Definition flatten (b: board) :=
  List.map (fun row => row.(arr_data)) b.(arr_data).

Definition step (b: board) :=
  make_board (length b) (step_one b).

Definition conway_life b :=
  flatten (step (init b)).

Require Coq.Lists.Streams.

Module Streams.
  Import Coq.Lists.Streams.

  CoFixpoint iter {A} (f: A -> A) (init: A) :=
    Cons init (iter f (f init)).

  Fixpoint take {A} (n: nat) (s: Stream A) : list A :=
    match n with
    | 0 => []
    | S n => match s with
            | Cons hd tl => hd :: take n tl
            end
    end.
End Streams.

Import Streams.

Notation "0" := false.
Notation "1" := true.

Definition blinker3 := [[0;0;0];
                        [1;1;1];
                        [0;0;0]].
Compute take 3 (iter conway_life blinker3). (* .unfold *)

Definition glider6 := [[0;1;0;0;0;0];
                       [0;0;1;0;0;0];
                       [1;1;1;0;0;0];
                       [0;0;0;0;0;0];
                       [0;0;0;0;0;0];
                       [0;0;0;0;0;0]].
Compute take 12 (iter conway_life glider6). (* .unfold *)

Definition toad := [[0;0;0;0];
                    [0;1;1;1];
                    [1;1;1;0];
                    [0;0;0;0]].
Compute take 3 (iter conway_life toad). (* .unfold *)

Definition butterfly := [[0;0;0;1;0;0;0];
                         [0;1;0;1;0;0;0];
                         [0;0;0;0;0;1;0];
                         [1;1;1;1;1;0;0];
                         [0;0;0;0;0;1;0];
                         [0;1;0;1;0;0;0];
                         [0;0;0;1;0;0;0]].
Compute take 3 (iter conway_life butterfly). (* .unfold *)

(*||*)

Definition blinker := [[0;0;0;0;0];
                       [0;0;0;0;0];
                       [0;1;1;1;0];
                       [0;0;0;0;0];
                       [0;0;0;0;0]].
Compute take 3 (iter conway_life blinker). (* .unfold *)

Definition bipole := [[1;1;0;0;0];
                      [1;0;0;0;0];
                      [0;1;0;1;0];
                      [0;0;0;0;1];
                      [0;0;0;1;1]].
Compute take 3 (iter conway_life bipole). (* .unfold *)

Definition glider := [[0;1;0;0;0];
                      [0;0;1;0;0];
                      [1;1;1;0;0];
                      [0;0;0;0;0];
                      [0;0;0;0;0]].
Compute take 9 (iter conway_life glider). (* .unfold *)

(*|
.. raw:: html

   <script src="https://cdn.jsdelivr.net/npm/@svgdotjs/svg.js@3.0/dist/svg.min.js"></script>
   <link rel="stylesheet" href="life.css">
   <script type="text/javascript" src="life.js"></script>
|*)
