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

#ifndef AVX
#define AVX
#endif

#ifndef BITS_PER_REG
#define BITS_PER_REG 256
#endif

/* Defining 0 and 1 */
#define ZERO _mm256_setzero_si256()
#define ONES _mm256_set1_epi32(-1)

/* Defining macros */
#define REG_SIZE 256
#define CHUNK_SIZE 1024

#define AND(a,b)  _mm256_and_si256(a,b)
#define OR(a,b)   _mm256_or_si256(a,b)
#define XOR(a,b)  _mm256_xor_si256(a,b)
#define ANDN(a,b) _mm256_andnot_si256(a,b)
#define NOT(a)    _mm256_xor_si256(ONES,a)

#define ADD(a,b,c) _mm256_add_epi##c(a,b)

#define L_SHIFT(a,b,c)  _mm256_slli_epi##c(a,b)
#define R_SHIFT(a,b,c)  _mm256_srli_epi##c(a,b)

#define L_ROTATE(a,b,c)                                                 \
  b == 8 && c == 32 ?                                                   \
    _mm256_shuffle_epi8(a,_mm256_set_epi8(14,13,12,15,10,9,8,11,6,5,4,7,2,1,0,3, \
                                          14,13,12,15,10,9,8,11,6,5,4,7,2,1,0,3)) : \
    b == 16 && c == 32 ?                                                \
    _mm256_shuffle_epi8(a,_mm256_set_epi8(13,12,15,14,9,8,11,10,5,4,7,6,1,0,3,2, \
                                          13,12,15,14,9,8,11,10,5,4,7,6,1,0,3,2)) : \
    OR(L_SHIFT(a,b,c),R_SHIFT(a,c-b,c))
  
#define R_ROTATE(a,b,c)                                                 \
  b == 8 && c == 32 ?                                                   \
    _mm256_shuffle_epi8(a,_mm256_set_epi8(12,15,14,13,8,11,10,9,4,7,6,5,0,3,2,1, \
                                          12,15,14,13,8,11,10,9,4,7,6,5,0,3,2,1)) : \
    b == 16 && c == 32 ?                                                \
    _mm256_shuffle_epi8(a,_mm256_set_epi8(13,12,15,14,9,8,11,10,5,4,7,6,1,0,3,2, \
                                          13,12,15,14,9,8,11,10,5,4,7,6,1,0,3,2)) : \
    OR(R_SHIFT(a,b,c),L_SHIFT(a,c-b,c))


#define LIFT_8(x)  _mm256_set1_epi8(x)
#define LIFT_16(x) _mm256_set1_epi16(x)
#define LIFT_32(x) _mm256_set1_epi32(x)
#define LIFT_64(x) _mm256_set1_epi64x(x)

#define DATATYPE __m256i

#define SET_ALL_ONE()  ONES
#define SET_ALL_ZERO() ZERO

/* Note the reverse of the pattern. */
#define PERMUT_16(a,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16) \
  _mm256_shuffle_epi8(a,_mm256_set_epi8(x16,x15,x14,x13,x12,x11,x10,x9,x8,x7,x6,x5,x4,x3,x2,x1,\
                                        x16,x15,x14,x13,x12,x11,x10,x9,x8,x7,x6,x5,x4,x3,x2,x1))
#define PERMUT_4(a,x1,x2,x3,x4) _mm256_shuffle_epi32(a,(x4<<6)|(x3<<4)|(x2<<2)|x1)


#define ORTHOGONALIZE(in,out) orthogonalize(in,out)
#define UNORTHOGONALIZE(in,out) unorthogonalize(in,out)

#define ALLOC(size) aligned_alloc(32,size * sizeof(__m256i))


#ifdef RUNTIME


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

void real_ortho_256x256(__m256i data[]) {

  __m256i mask_l[8] = {
    _mm256_set1_epi64x(0xaaaaaaaaaaaaaaaaUL),
    _mm256_set1_epi64x(0xccccccccccccccccUL),
    _mm256_set1_epi64x(0xf0f0f0f0f0f0f0f0UL),
    _mm256_set1_epi64x(0xff00ff00ff00ff00UL),
    _mm256_set1_epi64x(0xffff0000ffff0000UL),
    _mm256_set1_epi64x(0xffffffff00000000UL),
    _mm256_set_epi64x(0UL,-1UL,0UL,-1UL),
    _mm256_set_epi64x(0UL,0UL,-1UL,-1UL),
  
  };

  __m256i mask_r[8] = {
    _mm256_set1_epi64x(0x5555555555555555UL),
    _mm256_set1_epi64x(0x3333333333333333UL),
    _mm256_set1_epi64x(0x0f0f0f0f0f0f0f0fUL),
    _mm256_set1_epi64x(0x00ff00ff00ff00ffUL),
    _mm256_set1_epi64x(0x0000ffff0000ffffUL),
    _mm256_set1_epi64x(0x00000000ffffffffUL),
    _mm256_set_epi64x(-1UL,0UL,-1UL,0UL),
    _mm256_set_epi64x(-1UL,-1UL,0UL,0UL),
  };
  
  for (int i = 0; i < 8; i ++) {
    int n = (1UL << i);
    for (int j = 0; j < 256; j += (2 * n))
      for (int k = 0; k < n; k ++) {
        __m256i u = _mm256_and_si256(data[j + k], mask_l[i]);
        __m256i v = _mm256_and_si256(data[j + k], mask_r[i]);
        __m256i x = _mm256_and_si256(data[j + n + k], mask_l[i]);
        __m256i y = _mm256_and_si256(data[j + n + k], mask_r[i]);
        if (i <= 5) {
          data[j + k] = _mm256_or_si256(u, _mm256_srli_epi64(x, n));
          data[j + n + k] = _mm256_or_si256(_mm256_slli_epi64(v, n), y);
        } else if (i == 6) {
          /* Note the "inversion" of srli and slli. */
          data[j + k] = _mm256_or_si256(u, _mm256_slli_si256(x, 8));
          data[j + n + k] = _mm256_or_si256(_mm256_srli_si256(v, 8), y);
        } else {
          data[j + k] = _mm256_or_si256(u, _mm256_permute2x128_si256( x , x , 1));
          data[j + n + k] = _mm256_or_si256(_mm256_permute2x128_si256( v , v , 1), y);
        }
      }
  }
}

#ifdef ORTHO

void orthogonalize_256x64(uint64_t* data, __m256i* out) {
  real_ortho(data);
  real_ortho(&(data[64]));
  real_ortho(&(data[128]));
  real_ortho(&(data[192]));
  for (int i = 0; i < 64; i++)
    out[i] = _mm256_set_epi64x(data[i], data[64+i], data[128+i], data[192+i]);
}

void unorthogonalize_64x256(__m256i *in, uint64_t* data) {
  for (int i = 0; i < 64; i++) {
    uint64_t tmp[4];
    _mm256_store_si256 ((__m256i*)tmp, in[i]);
    data[i] = tmp[3];
    data[64+i] = tmp[2];
    data[128+i] = tmp[1];
    data[192+i] = tmp[0];
  }
  real_ortho(data);
  real_ortho(&(data[64]));
  real_ortho(&(data[128]));
  real_ortho(&(data[192]));
}

void orthogonalize_256x256(uint64_t* data, __m256i* out) {
  for (int i = 0; i < 256; i++)
    out[i] = _mm256_set_epi64x(data[i], data[256+i], data[512+i], data[768+i]);
  real_ortho_256x256(out);
}

void unorthogonalize_256x256(__m256i *in, uint64_t* data) {
  real_ortho_256x256(in);
  for (int i = 0; i < 256; i++) {
    uint64_t tmp[4];
    _mm256_store_si256 ((__m256i*)tmp, in[i]);
    data[i] = tmp[3];
    data[256+i] = tmp[2];
    data[512+i] = tmp[1];
    data[768+i] = tmp[0];
  }
}

void orthogonalize(uint64_t* data, __m256i* out) {
  orthogonalize_256x256(data,out);
}
void unorthogonalize(__m256i *in, uint64_t* data) {
  unorthogonalize_256x256(in,data);
}

#else

void orthogonalize_256x64(uint64_t *in, __m256i *out) {
  for (int i = 0; i < 64; i++)
    out[i] = _mm256_set_epi64x (in[i*4], in[i*4+1], in[i*4+2], in[i*4+3]);
}

void unorthogonalize_64x256(__m256i *in, uint64_t *out) {
  for (int i = 0; i < 64; i++)
    _mm256_store_si256 ((__m256i*)&(out[i*4]), in[i]);
}

void orthogonalize(uint64_t *in, __m256i *out) {
  for (int i = 0; i < 256; i++)
    out[i] = _mm256_set_epi64x (in[i*4], in[i*4+1], in[i*4+2], in[i*4+3]);
}

void unorthogonalize(__m256i *in, uint64_t *out) {
  for (int i = 0; i < 256; i++)
    _mm256_store_si256 ((__m256i*)&(out[i*4]), in[i]);
}

#endif /* ORTHO */

#endif /* NO_RUNTIME */
