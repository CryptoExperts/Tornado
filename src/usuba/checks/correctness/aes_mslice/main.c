
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <stdint.h>

/* Do NOT change the order of those define/include */

/* defining "BENCH" or "STD" */
/* (will impact the .h functions loaded by the .h) */
#define NO_RUNTIME
/* including the architecture specific .h */

#ifdef AVX
#include "AVX.h"
void orthogonalize(__m256i data[8]) {

  __m256i mask_l[3] = {
    _mm256_set1_epi64x(0xaaaaaaaaaaaaaaaaUL),
    _mm256_set1_epi64x(0xccccccccccccccccUL),
    _mm256_set1_epi64x(0xf0f0f0f0f0f0f0f0UL)
  
  };

  __m256i mask_r[3] = {
    _mm256_set1_epi64x(0x5555555555555555UL),
    _mm256_set1_epi64x(0x3333333333333333UL),
    _mm256_set1_epi64x(0x0f0f0f0f0f0f0f0fUL)
  };
  
  for (int i = 0; i < 3; i ++) {
    int n = (1UL << i);
    for (int j = 0; j < 8; j += (2 * n))
      for (int k = 0; k < n; k ++) {
        __m256i u = _mm256_and_si256(data[j + k], mask_l[i]);
        __m256i v = _mm256_and_si256(data[j + k], mask_r[i]);
        __m256i x = _mm256_and_si256(data[j + n + k], mask_l[i]);
        __m256i y = _mm256_and_si256(data[j + n + k], mask_r[i]);
        data[j + k] = _mm256_or_si256(u, _mm256_srli_epi64(x, n));
        data[j + n + k] = _mm256_or_si256(_mm256_slli_epi64(v, n), y);
      }
  }
}

#else // Not AVX

#include "SSE.h"
void orthogonalize(__m128i data[8]) {

  __m128i mask_l[3] = {
    _mm_set1_epi64x(0xaaaaaaaaaaaaaaaaUL),
    _mm_set1_epi64x(0xccccccccccccccccUL),
    _mm_set1_epi64x(0xf0f0f0f0f0f0f0f0UL)
  
  };

  __m128i mask_r[3] = {
    _mm_set1_epi64x(0x5555555555555555UL),
    _mm_set1_epi64x(0x3333333333333333UL),
    _mm_set1_epi64x(0x0f0f0f0f0f0f0f0fUL)
  };
  
  for (int i = 0; i < 3; i ++) {
    int n = (1UL << i);
    for (int j = 0; j < 8; j += (2 * n))
      for (int k = 0; k < n; k ++) {
        __m128i u = _mm_and_si128(data[j + k], mask_l[i]);
        __m128i v = _mm_and_si128(data[j + k], mask_r[i]);
        __m128i x = _mm_and_si128(data[j + n + k], mask_l[i]);
        __m128i y = _mm_and_si128(data[j + n + k], mask_r[i]);
        data[j + k] = _mm_or_si128(u, _mm_srli_epi64(x, n));
        data[j + n + k] = _mm_or_si128(_mm_slli_epi64(v, n), y);
      }
  }
}

#endif


#include "aes.c"


#ifndef NB_LOOP
#define NB_LOOP 16
#endif

#ifdef AVX
#define PARALLEL_BLOCK 16
#else
#define PARALLEL_BLOCK 8
#endif

#include "key_sched.c"

int main() {

  
  char key_base[16] = "0123456789ABCDEF";
  char* sched_key = key_sched(key_base);
  DATATYPE key[11][8];
  DATATYPE key_cst[11][8];
  for (int i = 0; i < 11; i++) {
    for (int j = 0; j < 8; j++)
#ifdef AVX      
      key[i][j] = key_cst[i][j] = _mm256_loadu2_m128i((__m128i*)&sched_key[i*16],
                                                      (__m128i*)&sched_key[i*16]);
#else
      key[i][j] = key_cst[i][j] = _mm_load_si128((__m128i*)&sched_key[i*16]);
#endif
    orthogonalize(key[i]);
    orthogonalize(key_cst[i]);
  }

  // Reading the input file
  FILE* fh_in = fopen("input.txt","rb");
  FILE* fh_out = fopen("output.txt","wb");
  
  // Allocating various stuffs
  DATATYPE plain[8];

  while (fread(plain,PARALLEL_BLOCK,16,fh_in) != 0) {
    for (int i = 0; i < 11; i++)
      for (int j = 0; j < 8; j++)
        key[i][j] = key_cst[i][j];
    DATATYPE cipher[8];
    orthogonalize(plain);
    AES__(plain,key,cipher);
    orthogonalize(cipher);
    fwrite(cipher,PARALLEL_BLOCK,16,fh_out);
  }

  fclose(fh_in);
  fclose(fh_out);

  return 0;
}
