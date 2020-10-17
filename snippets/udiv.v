(*|
.. coq:: none
|*)

Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Coq.Init.Byte.
Import ListNotations.

Module Type TLock.
  Parameter LOCK : forall {A}, A -> A.
End TLock.

Module Lock : TLock.
  Definition LOCK {A} (a: A) := a.
End Lock.

Open Scope string_scope.

Module M.
  Import Byte.

  Definition udiv_c := "
#include ""stdint.h""

typedef struct {
  uint32_t quot;
  uint32_t rem;
} udiv_t;

udiv_t udiv(uint32_t num, uint32_t denom) {
  uint32_t q = 0;
  while (num >= denom) {
    num -= denom; ++q;
  }
  return (udiv_t) { .rem = num, .quot = q };
}
".

  Definition udiv_bytes :=
    [
      x7f; x45; x4c; x46; x01; x01; x01; x00; x00; x00; x00; x00; x00; x00; x00; x00; x02; x00; xf3; x00; x01; x00; x00; x00; x54; x00; x01; x00; x34; x00;
      x00; x00; x0c; x02; x00; x00; x00; x00; x00; x00; x34; x00; x20; x00; x01; x00; x28; x00; x06; x00; x05; x00; x01; x00; x00; x00; x00; x00; x00; x00;
      x00; x00; x01; x00; x00; x00; x01; x00; x7c; x00; x00; x00; x7c; x00; x00; x00; x05; x00; x00; x00; x00; x10; x00; x00; x93; x07; x05; x00; x13; x01;
      x01; xff; x13; x05; x00; x00; x63; xf8; xb7; x00; x93; x85; x07; x00; x13; x01; x01; x01; x67; x80; x00; x00; xb3; x87; xb7; x40; x13; x05; x15; x00;
      x6f; xf0; x9f; xfe; x47; x43; x43; x3a; x20; x28; x78; x50; x61; x63; x6b; x20; x47; x4e; x55; x20; x52; x49; x53; x43; x2d; x56; x20; x45; x6d; x62;
      x65; x64; x64; x65; x64; x20; x47; x43; x43; x2c; x20; x36; x34; x2d; x62; x69; x74; x29; x20; x38; x2e; x33; x2e; x30; x00; x00; x00; x00; x00; x00;
      x00; x00; x00; x00; x00; x00; x00; x00; x00; x00; x00; x00; x00; x00; x00; x00; x54; x00; x01; x00; x00; x00; x00; x00; x03; x00; x01; x00; x00; x00;
      x00; x00; x00; x00; x00; x00; x00; x00; x00; x00; x03; x00; x02; x00; x01; x00; x00; x00; x00; x00; x00; x00; x00; x00; x00; x00; x04; x00; xf1; xff;
      x08; x00; x00; x00; x7c; x18; x01; x00; x00; x00; x00; x00; x10; x00; xf1; xff; x1a; x00; x00; x00; x7c; x10; x01; x00; x00; x00; x00; x00; x10; x00;
      x01; x00; x2a; x00; x00; x00; x54; x00; x01; x00; x28; x00; x00; x00; x12; x00; x01; x00; x40; x00; x00; x00; x00; x00; x00; x00; x00; x00; x00; x00;
      x10; x00; x00; x00; x2f; x00; x00; x00; x7c; x10; x01; x00; x00; x00; x00; x00; x10; x00; x01; x00; x3b; x00; x00; x00; x7c; x10; x01; x00; x00; x00;
      x00; x00; x10; x00; x01; x00; x47; x00; x00; x00; x7c; x10; x01; x00; x00; x00; x00; x00; x10; x00; x01; x00; x56; x00; x00; x00; x7c; x10; x01; x00;
      x00; x00; x00; x00; x10; x00; x01; x00; x5d; x00; x00; x00; x7c; x10; x01; x00; x00; x00; x00; x00; x10; x00; x01; x00; x00; x75; x64; x69; x76; x2e;
      x63; x00; x5f; x5f; x67; x6c; x6f; x62; x61; x6c; x5f; x70; x6f; x69; x6e; x74; x65; x72; x24; x00; x5f; x5f; x53; x44; x41; x54; x41; x5f; x42; x45;
      x47; x49; x4e; x5f; x5f; x00; x75; x64; x69; x76; x00; x5f; x5f; x42; x53; x53; x5f; x45; x4e; x44; x5f; x5f; x00; x5f; x5f; x62; x73; x73; x5f; x73;
      x74; x61; x72; x74; x00; x5f; x5f; x44; x41; x54; x41; x5f; x42; x45; x47; x49; x4e; x5f; x5f; x00; x5f; x65; x64; x61; x74; x61; x00; x5f; x65; x6e;
      x64; x00; x00; x2e; x73; x79; x6d; x74; x61; x62; x00; x2e; x73; x74; x72; x74; x61; x62; x00; x2e; x73; x68; x73; x74; x72; x74; x61; x62; x00; x2e;
      x74; x65; x78; x74; x00; x2e; x63; x6f; x6d; x6d; x65; x6e; x74; x00; x00; x00; x00; x00; x00; x00; x00; x00; x00; x00; x00; x00; x00; x00; x00; x00;
      x00; x00; x00; x00; x00; x00; x00; x00; x00; x00; x00; x00; x00; x00; x00; x00; x00; x00; x00; x00; x00; x00; x00; x00; x1b; x00; x00; x00; x01; x00;
      x00; x00; x06; x00; x00; x00; x54; x00; x01; x00; x54; x00; x00; x00; x28; x00; x00; x00; x00; x00; x00; x00; x00; x00; x00; x00; x04; x00; x00; x00;
      x00; x00; x00; x00; x21; x00; x00; x00; x01; x00; x00; x00; x30; x00; x00; x00; x00; x00; x00; x00; x7c; x00; x00; x00; x33; x00; x00; x00; x00; x00;
      x00; x00; x00; x00; x00; x00; x01; x00; x00; x00; x01; x00; x00; x00; x01; x00; x00; x00; x02; x00; x00; x00; x00; x00; x00; x00; x00; x00; x00; x00;
      xb0; x00; x00; x00; xd0; x00; x00; x00; x04; x00; x00; x00; x04; x00; x00; x00; x04; x00; x00; x00; x10; x00; x00; x00; x09; x00; x00; x00; x03; x00;
      x00; x00; x00; x00; x00; x00; x00; x00; x00; x00; x80; x01; x00; x00; x62; x00; x00; x00; x00; x00; x00; x00; x00; x00; x00; x00; x01; x00; x00; x00;
      x00; x00; x00; x00; x11; x00; x00; x00; x03; x00; x00; x00; x00; x00; x00; x00; x00; x00; x00; x00; xe2; x01; x00; x00; x2a; x00; x00; x00; x00; x00;
      x00; x00; x00; x00; x00; x00; x01; x00; x00; x00; x00; x00; x00; x00
    ].
End M.

Record prog :=
  { c_source : string;
    riscv_elf : list Byte.byte }.

Notation "{c  x  c}" := (@Lock.LOCK string x).
Notation "{mc  x  mc}" := (@Lock.LOCK (list Byte.byte) x).

Definition udiv :=
  {| c_source := Lock.LOCK M.udiv_c;
     riscv_elf := Lock.LOCK M.udiv_bytes |}.

Module Disp.
  Import Byte.
  Notation "…" := x00.

(* Definition udiv := {| *)
(*   c_source := *)
(*     "#include ""stdint.h"" *)

(*      typedef struct { *)
(*        uint32_t quot; *)
(*        uint32_t rem; *)
(*      } udiv_t; *)
(*      …"; *)
(*   riscv_elf := *)
(*     [x7f; x45; x4c; x46; x01; x01; x01; x00; x00; x00; x00; x00; x00; x00; x00; x00; *)
(*      x02; x00; xf3; x00; x01; x00; x00; x00; x54; x00; x01; x00; x34; x00; x00; x00; *)
(*      x0c; x02; x00; x00; x00; x00; x00; x00; x34; x00; x20; x00; x01; x00; x28; x00; *)
(*      x06; x00; x05; x00; x01; x00; x00; x00; x00; x00; x00; x00; x00; x00; x01; x00; *)
(*      x00; x00; x01; x00; x7c; x00; x00; x00; x7c; x00; x00; x00; x05; x00; x00; x00; *)
(*      x00; x10; x00; x00; x93; x07; x05; x00; x13; x01; x01; xff; x13; x05; x00; … ] |}. *)


(*||*)

Definition udiv := {|
  c_source :=
    "#include ""stdint.h""

     typedef struct {
       uint32_t quot; …";
  riscv_elf :=
    [x7f; x45; x4c; x46; x01; x01; x01; x00; x00; x00; x00; x00; x00; x00; x00; x00;
     x02; x00; xf3; x00; x01; x00; x00; x00; x54; x00; x01; x00; x34; x00; x00; x00;
     x0c; x02; x00; x00; x00; x00; x00; x00; x34; x00; x20; x00; x01; x00; x28; x00;
     x06; x00; x05; x00; x01; x00; x00; x00; x00; x00; x00; x00; x00; x00; x01; … ] |}.
End Disp. (* .none *)

Compute udiv.(c_source). (* .unfold *)

Compute udiv.(riscv_elf). (* .unfold *)

(*|
.. raw:: html

   <link rel="stylesheet" href="udiv.css">
|*)
