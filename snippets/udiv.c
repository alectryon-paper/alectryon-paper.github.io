#include "stdint.h"

typedef struct {
  uint32_t quot;
  uint32_t rem;
} udiv_t;

udiv_t udiv(uint32_t num, uint32_t denom) {
  uint32_t q = 0;
  while (num >= denom) {
    num -= denom;
    ++q;
  }
  return (udiv_t) { .rem = num, .quot = q };
}

/* #include "stdio.h" */
/* #include <stdlib.h> */

/* int main() { */
/*   for (uint32_t x = 0; x < 500; x++) { */
/*     for (uint32_t y = 1; y < 500; y++) { */
/*       div_t d = div(x, y); */
/*       udiv_t ud = udiv(x, y); */
/*       if (d.quot != (int)ud.quot || d.rem != (int)ud.rem) { */
/*         printf("Error\n"); */
/*       } */
/*       /\* printf("%d == %d * %d + %d\n", x, y, d.quot, d.rem); *\/ */
/*       /\* printf("%u ?= %u * %u + %u\n", x, y, ud.quot, ud.rem); *\/ */
/*     } */
/*   } */
/* } */

// Compile with
// riscv-none-embed-gcc --std=c89 -g -Os -mstrict-align -nostartfiles -static -mabi=ilp32 -march=rv32i udiv.c -o udiv.o
// riscv-none-embed-objdump --disassemble udiv.o > udiv.dump
// echo '['; { xxd -p udiv.o | sed 's/../x\0; /g'; }; echo ']'
