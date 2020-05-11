/* ******************************************** *\
 * 
 * 
 *
\* ******************************************** */


/* Including headers */
#pragma once
#include <stdlib.h>
#include <stdint.h>


#ifndef BITS_PER_REG
#define BITS_PER_REG 64
#endif
#ifndef LOG2_BITS_PER_REG
#define LOG2_BITS_PER_REG 6
#endif

/* Defining macros */
#define REG_SIZE BITS_PER_REG
#define CHUNK_SIZE 64

#define AND(a,b)  ((a) & (b))
#define OR(a,b)   ((a) | (b))
#define XOR(a,b)  ((a) ^ (b))
#define ANDN(a,b) (~(a) & (b))
#define NOT(a)    (~(a))

#define ADD(a,b,c) ((a) + (b))

#define L_SHIFT(a,b,c) ((a) << (b))
#define R_SHIFT(a,b,c) ((a) >> (b))
#define L_ROTATE(a,b,c) ((a << b) | (a >> (c-b)))
#define R_ROTATE(a,b,c) ((a >> b) | (a << (c-b)))


#ifndef DATATYPE
#if BITS_PER_REG == 32
#define DATATYPE unsigned int
#else
#define DATATYPE uint64_t
#endif
#endif

#define SET_ALL_ONE()  -1
#define SET_ALL_ZERO() 0

#define ORTHOGONALIZE(in,out)   orthogonalize(in,out)
#define UNORTHOGONALIZE(in,out) unorthogonalize(in,out)

#define ALLOC(size) malloc(size * sizeof(uint64_t))



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

#ifdef ORTHO

void orthogonalize(uint64_t* data, uint64_t* out) {
  for (int i = 0; i < 64; i++)
    out[i] = data[i];
  real_ortho(out);
}

void unorthogonalize(uint64_t *in, uint64_t* data) {
  for (int i = 0; i < 64; i++)
    data[i] = in[i];
  real_ortho(data);
}

#else

void orthogonalize(uint64_t* data, uint64_t* out) {
  for (int i = 0; i < 64; i++)
    out[i] = data[i];
}

void unorthogonalize(uint64_t *in, uint64_t* data) {
  for (int i = 0; i < 64; i++)
    data[i] = in[i];
}


#endif /* ORTHO */

#endif /* NO_RUNTIME */
