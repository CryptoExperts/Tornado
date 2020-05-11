#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

#ifdef REF

#include "drygascon128_ref.h"
#include "drysponge_ref.h"
#define drygascon_round(x,c) gascon_permutation_round(x,c)

#elif defined(UA_V)

#include "drygascon_ua_vslice.c"
void drygascon_round(uint8_t text[40], int r) {
  uint64_t* input = (uint64_t*)text;
  uint64_t output[5];
  CoreRound__(input,r,output);
  memcpy(text,output,5*sizeof(uint64_t));
}

#else
#error Please define REF or UA_V
#endif


void test_drygascon() {

  // This seemigly random input is produced by encrypting full 0s plain
  uint8_t text[5*8] = { 0 };

  for (int i = 0; i < 11; i++) {
    drygascon_round(text, i);
  }

  for (int i = 0; i < 40; i++) {
    printf("0x%02x, ", text[i]);
  }

  uint8_t expected[40] = {
    0x6d, 0x21, 0x29, 0x00, 0xa0, 0x5c, 0x84, 0xa5,
    0x20, 0x6f, 0xac, 0xd9, 0x8d, 0xb4, 0x1d, 0xd5,
    0x6a, 0xa0, 0x1a, 0x6e, 0xfe, 0x2c, 0xfa, 0xeb,
    0xd4, 0xa7, 0x3d, 0xe6, 0x63, 0x16, 0x7e, 0x66,
    0x14, 0xc1, 0x9c, 0xc3, 0xe2, 0x1b, 0xdc, 0xf2 };

  if (memcmp(text, expected, 40) != 0) {
    fprintf(stderr, "Error encryption.\n");
    fprintf(stderr, "Expected : ");
    for (int i = 0; i < 5; i++) {
      for (int j = 0; j < 8; j++) fprintf(stderr, "0x%02x", expected[i*8+j]);
      fprintf(stderr, " ");
    }
    fprintf(stderr, "\nGot      : ");
    for (int i = 0; i < 5; i++) {
      for (int j = 0; j < 8; j++) fprintf(stderr, "0x%02x", text[i*8+j]);
      fprintf(stderr, " ");
    }
    fprintf(stderr, "\n");
    exit(EXIT_FAILURE);
  } else {
    fprintf(stderr, "Seems OK.\n");
  }
}


int main() {
  test_drygascon();
}
