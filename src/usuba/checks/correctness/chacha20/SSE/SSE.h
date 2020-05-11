/* ******************************************** *\
 * 
 * 
 *
\* ******************************************** */


/* Including headers */
#pragma once
#include <stdlib.h>
#include <x86intrin.h>
#include <stdint.h>

/* Defining 0 and 1 */
#define ZERO _mm_setzero_si128()
#define ONES _mm_set1_epi32(-1)

/* Defining macros */
#define REG_SIZE 128
#define CHUNK_SIZE 256

#define AND(a,b)  _mm_and_si128(a,b)
#define OR(a,b)   _mm_or_si128(a,b)
#define XOR(a,b)  _mm_xor_si128(a,b)
#define ANDN(a,b) _mm_andnot_si128(a,b)
#define NOT(a)    _mm_andnot_si128(a,ONES)

#define ADD(a,b,c) _mm_add_epi##c(a,b)

#define L_SHIFT(a,b,c)  _mm_slli_epi##c(a,b)
#define R_SHIFT(a,b,c)  _mm_srli_epi##c(a,b)

#define L_ROTATE(a,b,c)                                                 \
  b == 8 && c == 32 ?                                                   \
    _mm_shuffle_epi8(a,_mm_set_epi8(14,13,12,15,10,9,8,11,6,5,4,7,2,1,0,3)) : \
    b == 16 && c == 32 ?                                                \
    _mm_shuffle_epi8(a,_mm_set_epi8(13,12,15,14,9,8,11,10,5,4,7,6,1,0,3,2)) : \
    OR(L_SHIFT(a,b,c),R_SHIFT(a,c-b,c))
  
#define R_ROTATE(a,b,c)                                                 \
  b == 8 && c == 32 ?                                                   \
    _mm_shuffle_epi8(a,_mm_set_epi8(12,15,14,13,8,11,10,9,4,7,6,5,0,3,2,1)) : \
    b == 16 && c == 32 ?                                                \
    _mm_shuffle_epi8(a,_mm_set_epi8(13,12,15,14,9,8,11,10,5,4,7,6,1,0,3,2)) : \
    OR(R_SHIFT(a,b,c),L_SHIFT(a,c-b,c))

#define DATATYPE __m128i

#define SET_ALL_ONE()  ONES
#define SET_ALL_ZERO() ZERO

/* Note the reverse of the pattern. */
#define PERMUT_16(a,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16) \
  _mm_shuffle_epi8(a,_mm_set_epi8(x16,x15,x14,x13,x12,x11,x10,x9,x8,x7,x6,x5,x4,x3,x2,x1))
#define PERMUT_4(a,x1,x2,x3,x4) _mm_shuffle_epi32(a,(x4<<6)|(x3<<4)|(x2<<2)|x1)

#define ORTHOGONALIZE(in,out) orthogonalize(in,out)
#define UNORTHOGONALIZE(in,out) unorthogonalize(in,out)

#define ALLOC(size) aligned_alloc(32,size * sizeof(__m128i))


#ifndef NO_RUNTIME


/* Orthogonalization stuffs */
static uint64_t mask_l[6] = {
	0xaaaaaaaaaaaaaaaaUL,
	0xccccccccccccccccUL,
	0xf0f0f0f0f0f0f0f0UL,
	0xff00ff00ff00ff00UL,
	0xffff0000ffff0000UL,
	0xffffffff00000000UL
};

static uint64_t mask_r[6] = {
	0x5555555555555555UL,
	0x3333333333333333UL,
	0x0f0f0f0f0f0f0f0fUL,
	0x00ff00ff00ff00ffUL,
	0x0000ffff0000ffffUL,
	0x00000000ffffffffUL
};


void real_ortho(uint64_t data[]) {
  for (int i = 0; i < 6; i ++) {
    int n = (1UL << i);
    for (int j = 0; j < 64; j += (2 * n))
      for (int k = 0; k < n; k ++) {
        uint64_t u = data[j + k] & mask_l[i];
        uint64_t v = data[j + k] & mask_r[i];
        uint64_t x = data[j + n + k] & mask_l[i];
        uint64_t y = data[j + n + k] & mask_r[i];
        data[j + k] = u | (x >> n);
        data[j + n + k] = (v << n) | y;
      }
  }
}

void real_ortho_128x128(__m128i data[]) {

  __m128i mask_l[7] = {
    _mm_set1_epi64x(0xaaaaaaaaaaaaaaaaUL),
    _mm_set1_epi64x(0xccccccccccccccccUL),
    _mm_set1_epi64x(0xf0f0f0f0f0f0f0f0UL),
    _mm_set1_epi64x(0xff00ff00ff00ff00UL),
    _mm_set1_epi64x(0xffff0000ffff0000UL),
    _mm_set1_epi64x(0xffffffff00000000UL),
    _mm_set_epi64x(0x0000000000000000UL,0xffffffffffffffffUL),
  
  };

  __m128i mask_r[7] = {
    _mm_set1_epi64x(0x5555555555555555UL),
    _mm_set1_epi64x(0x3333333333333333UL),
    _mm_set1_epi64x(0x0f0f0f0f0f0f0f0fUL),
    _mm_set1_epi64x(0x00ff00ff00ff00ffUL),
    _mm_set1_epi64x(0x0000ffff0000ffffUL),
    _mm_set1_epi64x(0x00000000ffffffffUL),
    _mm_set_epi64x(0xffffffffffffffffUL,0x0000000000000000UL),
  };
  
  for (int i = 0; i < 7; i ++) {
    int n = (1UL << i);
    for (int j = 0; j < 128; j += (2 * n))
      for (int k = 0; k < n; k ++) {
        __m128i u = _mm_and_si128(data[j + k], mask_l[i]);
        __m128i v = _mm_and_si128(data[j + k], mask_r[i]);
        __m128i x = _mm_and_si128(data[j + n + k], mask_l[i]);
        __m128i y = _mm_and_si128(data[j + n + k], mask_r[i]);
        if (i <= 5) {
          data[j + k] = _mm_or_si128(u, _mm_srli_epi64(x, n));
          data[j + n + k] = _mm_or_si128(_mm_slli_epi64(v, n), y);
        } else {
          /* Note the "inversion" of srli and slli. */
          data[j + k] = _mm_or_si128(u, _mm_slli_si128(x, 8));
          data[j + n + k] = _mm_or_si128(_mm_srli_si128(v, 8), y);
        } 
      }
  }
}

void real_ortho_128x128_blend(__m128i data[]) {

  __m128i mask_l[7] = {
    _mm_set1_epi64x(0xaaaaaaaaaaaaaaaaUL),
    _mm_set1_epi64x(0xccccccccccccccccUL),
    _mm_set1_epi64x(0xf0f0f0f0f0f0f0f0UL),
    _mm_set1_epi64x(0xff00ff00ff00ff00UL),
    _mm_set1_epi64x(0xffff0000ffff0000UL),
    _mm_set1_epi64x(0xffffffff00000000UL),
    _mm_set_epi64x(0UL,-1UL),
  
  };

  __m128i mask_r[7] = {
    _mm_set1_epi64x(0x5555555555555555UL),
    _mm_set1_epi64x(0x3333333333333333UL),
    _mm_set1_epi64x(0x0f0f0f0f0f0f0f0fUL),
    _mm_set1_epi64x(0x00ff00ff00ff00ffUL),
    _mm_set1_epi64x(0x0000ffff0000ffffUL),
    _mm_set1_epi64x(0x00000000ffffffffUL),
    _mm_set_epi64x(-1UL,0UL),
  };
  
  for (int i = 0; i < 7; i ++) {
    int n = (1UL << i);
    for (int j = 0; j < 128; j += (2 * n))
      for (int k = 0; k < n; k ++) {
        if (i <= 3) {
          __m128i u = _mm_and_si128(data[j + k], mask_l[i]);
          __m128i v = _mm_and_si128(data[j + k], mask_r[i]);
          __m128i x = _mm_and_si128(data[j + n + k], mask_l[i]);
          __m128i y = _mm_and_si128(data[j + n + k], mask_r[i]);
          data[j + k] = _mm_or_si128(u, _mm_srli_epi64(x, n));
          data[j + n + k] = _mm_or_si128(_mm_slli_epi64(v, n), y);
        } else if (i == 4) {
          __m128i u = data[j + k];
          __m128i v = data[j + k];
          __m128i x = data[j + n + k];
          __m128i y = data[j + n + k];
          data[j + k] = _mm_blend_epi16(u,_mm_srli_epi64(x, n), 0b01010101);
          data[j + n + k] = _mm_blend_epi16(_mm_slli_epi64(v, n), y, 0b01010101);
        } else if (i == 5) {
          __m128i u = data[j + k];
          __m128i v = data[j + k];
          __m128i x = data[j + n + k];
          __m128i y = data[j + n + k];
          data[j + k] = _mm_blend_epi16(u,_mm_srli_epi64(x, n), 0b00110011);
          data[j + n + k] = _mm_blend_epi16(_mm_slli_epi64(v, n), y, 0b00110011);
        } else {
          __m128i u = data[j + k];
          __m128i v = data[j + k];
          __m128i x = data[j + n + k];
          __m128i y = data[j + n + k];
          /* Note the "inversion" of srli and slli. */
          data[j + k] = _mm_blend_epi16(u,_mm_slli_si128(x,8), 0b11110000);
          data[j + n + k] = _mm_blend_epi16(_mm_srli_si128(v, 8), y, 0b11110000);
        } 
      }
  }
}

#ifdef ORTHO

void orthogonalize_128x64(uint64_t* data, __m128i* out) {
  real_ortho(data);
  real_ortho(&(data[64]));
  for (int i = 0; i < 64; i++)
    out[i] = _mm_set_epi64x(data[i], data[64+i]);
}

void unorthogonalize_64x128(__m128i *in, uint64_t* data) {
  for (int i = 0; i < 64; i++) {
    uint64_t tmp[2];
    _mm_store_si128 ((__m128i*)tmp, in[i]);
    data[i] = tmp[1];
    data[64+i] = tmp[0];
  }
  real_ortho(data);
  real_ortho(&(data[64]));
}

void orthogonalize_128x128(uint64_t* data, __m128i* out) {
  for (int i = 0; i < 128; i++)
    out[i] = _mm_set_epi64x(data[i], data[128+i]);
  real_ortho_128x128(out);
}

void unorthogonalize_128x128(__m128i *in, uint64_t* data) {
  real_ortho_128x128(in);
  for (int i = 0; i < 128; i++) {
    uint64_t tmp[2];
    _mm_store_si128 ((__m128i*)tmp, in[i]);
    data[i] = tmp[1];
    data[128+i] = tmp[0];
  }
}

void orthogonalize(uint64_t* data, __m128i* out) {
  orthogonalize_128x128(data,out);
}
void unorthogonalize(__m128i *in, uint64_t* data) {
  unorthogonalize_128x128(in,data);
}

#else

void orthogonalize(uint64_t *in, __m128i *out) {
  for (int i = 0; i < 128; i++)
    out[i] = _mm_set_epi64x (in[i*2], in[i*2+1]);
}

void unorthogonalize(__m128i *in, uint64_t *out) {
  for (int i = 0; i < 128; i++)
    _mm_store_si128 ((__m128i*)&(out[i*2]), in[i]);
}

#endif /* ORTHO */

#endif /* NO_RUNTIME */
