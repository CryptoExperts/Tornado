/* ******************************************** *\
 *
 *
 *
\* ******************************************** */


/* Including headers */
#pragma once
#include <stdlib.h>
#include <stdio.h>
#include <stdint.h>
#include <time.h>

#ifndef MASKING_ORDER
#error MASKING_ORDER not defined.
#endif

#ifndef BITS_PER_REG
#define BITS_PER_REG 32
#endif

#ifndef DATATYPE
#if BITS_PER_REG == 4
#define DATATYPE uint8_t
#define SDATATYPE int8_t
#elif BITS_PER_REG == 8
#define DATATYPE uint8_t
#define SDATATYPE int8_t
#elif BITS_PER_REG == 16
#define DATATYPE uint16_t
#define SDATATYPE int16_t
#elif BITS_PER_REG == 32
#define DATATYPE uint32_t
#define SDATATYPE int32_t
#else
#define DATATYPE uint64_t
#define SDATATYPE int64_t
#endif
#endif

#define SET_ALL_ONE()  ((DATATYPE)-1)
#define SET_ALL_ZERO() ((DATATYPE)0)

#define LIFT_8(x) (x)
#define LIFT_16(x) (x)
#define LIFT_32(x) (x)
#define LIFT_64(x) (x)


#define ROTATE_MASK(x)                                                  \
  (x == 64 ? -1ULL : x == 32 ? -1 : x == 16 ? 0xFFFF :                  \
   ({ fprintf(stderr,"Not implemented rotate [uint%d_t]. Exiting.\n",x); \
     exit(1); 1; }))

#define L_SHIFT(r,a,b,c)                                                \
  for (int i_In_Header = 0; i_In_Header < MASKING_ORDER; i_In_Header++) \
    r[i_In_Header] = (c == 4 ? (a[i_In_Header] << b) & 0xf :  a[i_In_Header] << b);

#define R_SHIFT(r,a,b,c)                                                \
  for (int i_In_Header = 0; i_In_Header < MASKING_ORDER; i_In_Header++) \
    r[i_In_Header] = a[i_In_Header] >> b;

#define RA_SHIFT(r,a,b,c)                                               \
  for (int i_In_Header = 0; i_In_Header < MASKING_ORDER; i_In_Header++) \
    r[i_In_Header] = ((SDATATYPE)(a[i_In_Header])) >> b;

#define L_ROTATE(r,a,b,c)                                               \
  for (int i_In_Header = 0; i_In_Header < MASKING_ORDER; i_In_Header++) \
    r[i_In_Header] = (a[i_In_Header] << b) | ((a[i_In_Header]&ROTATE_MASK(c)) >> (c-b))

#define R_ROTATE(r,a,b,c)                                               \
  for (int i_In_Header = 0; i_In_Header < MASKING_ORDER; i_In_Header++) \
    r[i_In_Header] = ((a[i_In_Header]&ROTATE_MASK(c)) >> b) | (a[i_In_Header] << (c-b))

/* Defining 0 and 1 */
#define ZERO 0
#define ONES -1


/* Defining operators */

#define AND(r,a,b)  isw_mult(r,a,b)
#define AND_CST(r,a,b)                                                  \
  for (int i_In_Header = 0; i_In_Header < MASKING_ORDER; i_In_Header++) \
    r[i_In_Header] = a[i_In_Header] & b[0];


#define OR(r,a,b) {                             \
    DATATYPE nota[MASKING_ORDER], notb[MASKING_ORDER], notr[MASKING_ORDER]; \
    NOT(nota,a);                                                        \
    NOT(notb,b);                                                        \
    AND(notr,nota,notb);                                                \
    NOT(r,notr);                                                        \
  }
#define OR_CST(r,a,b)                                                   \
  for (int i_In_Header = 0; i_In_Header < MASKING_ORDER; i_In_Header++) \
    r[i_In_Header] = a[i_In_Header] | b[0];


#define XOR(r,a,b)                                                      \
  for (int i_In_Header = 0; i_In_Header < MASKING_ORDER; i_In_Header++) \
    r[i_In_Header] = a[i_In_Header] ^ b[i_In_Header];
#define XOR_CST XOR

#define NOT(r,a)                                                        \
  r[0] = ~a[0];                                                         \
  for (int i_In_Header = 1; i_In_Header < MASKING_ORDER; i_In_Header++) \
    r[i_In_Header] = a[i_In_Header];

#define ASGN(r,a)                                                       \
  for (int i_In_Header = 0; i_In_Header < MASKING_ORDER; i_In_Header++) \
    r[i_In_Header] = a[i_In_Header];

#define ASGN_CST(r,cst)                                                 \
  r[0] = cst;                                                           \
  for (int i_In_Header = 1; i_In_Header < MASKING_ORDER; i_In_Header++) \
    r[i_In_Header] = 0;



/* Multiplication and refresh */

#ifdef NUCLEO
volatile int __rand = 0;

static DATATYPE get_random() {
  return __rand;
}
#else
static DATATYPE get_random() {
  srand(time(NULL));
  return rand();
}
#endif

static void isw_mult(DATATYPE *res, const DATATYPE *op1, const DATATYPE *op2) {
  int i,j;
  DATATYPE rnd;

  for (i=0; i<MASKING_ORDER; i++) {
    res[i] = 0;
  }

  for (i=0; i<MASKING_ORDER; i++) {
    res[i] ^= op1[i] & op2[i];

    for (j=i+1; j<MASKING_ORDER; j++) {
      rnd = get_random();
      res[i] ^= rnd;
      res[j] ^= (rnd ^ (op1[i] & op2[j])) ^ (op1[j] & op2[i]);
    }
  }
}

#define REFRESH isw_refresh

static void isw_refresh(DATATYPE *res, const DATATYPE *in) {
  int i,j;
  DATATYPE rnd;

  for (i=0; i<MASKING_ORDER; i++) {
    res[i] = in[i];
  }

  for (i=0; i<MASKING_ORDER; i++) {
    for (j=i+1; j<MASKING_ORDER; j++) {
      rnd = get_random();
      res[i] ^= rnd;
      res[j] ^= rnd;
    }
  }
}
