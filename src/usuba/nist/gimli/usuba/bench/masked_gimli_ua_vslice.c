/* This code was generated by Usuba.
   See https://github.com/DadaIsCrazy/usuba.
   From the file "nist/gimli/usuba/ua/gimli.ua" (included below). */

#include <stdint.h>

/* Do NOT change the order of those define/include */

#ifndef BITS_PER_REG
#define BITS_PER_REG 32
#endif
/* including the architecture specific .h */
#include "MASKED_UA.h"

/* auxiliary functions */
void SPbox_Rx__V32 (/*inputs*/ DATATYPE col__0__[MASKING_ORDER],DATATYPE col__1__[MASKING_ORDER],DATATYPE col__2__[MASKING_ORDER], /*outputs*/ DATATYPE colR__0__[MASKING_ORDER],DATATYPE colR__1__[MASKING_ORDER],DATATYPE colR__2__[MASKING_ORDER]) {

  // Variables declaration
  DATATYPE _tmp10_;
  DATATYPE _tmp1_;
  DATATYPE _tmp2_[MASKING_ORDER];
  DATATYPE _tmp3_[MASKING_ORDER];
  DATATYPE _tmp4_;
  DATATYPE _tmp5_[MASKING_ORDER];
  DATATYPE _tmp6_[MASKING_ORDER];
  DATATYPE _tmp7_;
  DATATYPE _tmp8_[MASKING_ORDER];
  DATATYPE _tmp9_[MASKING_ORDER];
  DATATYPE x__[MASKING_ORDER];
  DATATYPE x_R__[MASKING_ORDER];
  DATATYPE y__[MASKING_ORDER];

  // Instructions (body)
  for (int _mask_idx = 0; _mask_idx <= (MASKING_ORDER - 1); _mask_idx++) {
    x__[_mask_idx] = L_ROTATE(col__0__[_mask_idx],24,32);
    y__[_mask_idx] = L_ROTATE(col__1__[_mask_idx],9,32);
    _tmp1_ = L_SHIFT(col__2__[_mask_idx],1,32);
    _tmp2_[_mask_idx] = XOR(x__[_mask_idx],_tmp1_);
    _tmp5_[_mask_idx] = XOR(y__[_mask_idx],x__[_mask_idx]);
    _tmp8_[_mask_idx] = XOR(col__2__[_mask_idx],y__[_mask_idx]);
  }
  REFRESH(x_R__,x__);
  MASKED_AND(_tmp3_,y__,col__2__);
  for (int _mask_idx = 0; _mask_idx <= (MASKING_ORDER - 1); _mask_idx++) {
    _tmp4_ = L_SHIFT(_tmp3_[_mask_idx],2,32);
    colR__2__[_mask_idx] = XOR(_tmp2_[_mask_idx],_tmp4_);
  }
  MASKED_OR(_tmp6_,x_R__,col__2__);
  for (int _mask_idx = 0; _mask_idx <= (MASKING_ORDER - 1); _mask_idx++) {
    _tmp7_ = L_SHIFT(_tmp6_[_mask_idx],1,32);
    colR__1__[_mask_idx] = XOR(_tmp5_[_mask_idx],_tmp7_);
  }
  MASKED_AND(_tmp9_,x_R__,y__);
  for (int _mask_idx = 0; _mask_idx <= (MASKING_ORDER - 1); _mask_idx++) {
    _tmp10_ = L_SHIFT(_tmp9_[_mask_idx],3,32);
    colR__0__[_mask_idx] = XOR(_tmp8_[_mask_idx],_tmp10_);
  }

}

void SPbox_Rxy__V32 (/*inputs*/ DATATYPE col__0__[MASKING_ORDER],DATATYPE col__1__[MASKING_ORDER],DATATYPE col__2__[MASKING_ORDER], /*outputs*/ DATATYPE colR__0__[MASKING_ORDER],DATATYPE colR__1__[MASKING_ORDER],DATATYPE colR__2__[MASKING_ORDER]) {

  // Variables declaration
  DATATYPE _tmp11_;
  DATATYPE _tmp12_[MASKING_ORDER];
  DATATYPE _tmp13_[MASKING_ORDER];
  DATATYPE _tmp14_;
  DATATYPE _tmp15_[MASKING_ORDER];
  DATATYPE _tmp16_[MASKING_ORDER];
  DATATYPE _tmp17_;
  DATATYPE _tmp18_[MASKING_ORDER];
  DATATYPE _tmp19_[MASKING_ORDER];
  DATATYPE _tmp20_;
  DATATYPE x__[MASKING_ORDER];
  DATATYPE x_R__[MASKING_ORDER];
  DATATYPE y__[MASKING_ORDER];
  DATATYPE y_R__[MASKING_ORDER];

  // Instructions (body)
  for (int _mask_idx = 0; _mask_idx <= (MASKING_ORDER - 1); _mask_idx++) {
    x__[_mask_idx] = L_ROTATE(col__0__[_mask_idx],24,32);
    y__[_mask_idx] = L_ROTATE(col__1__[_mask_idx],9,32);
    _tmp11_ = L_SHIFT(col__2__[_mask_idx],1,32);
    _tmp12_[_mask_idx] = XOR(x__[_mask_idx],_tmp11_);
    _tmp15_[_mask_idx] = XOR(y__[_mask_idx],x__[_mask_idx]);
    _tmp18_[_mask_idx] = XOR(col__2__[_mask_idx],y__[_mask_idx]);
  }
  REFRESH(x_R__,x__);
  REFRESH(y_R__,y__);
  MASKED_AND(_tmp13_,y_R__,col__2__);
  for (int _mask_idx = 0; _mask_idx <= (MASKING_ORDER - 1); _mask_idx++) {
    _tmp14_ = L_SHIFT(_tmp13_[_mask_idx],2,32);
    colR__2__[_mask_idx] = XOR(_tmp12_[_mask_idx],_tmp14_);
  }
  MASKED_OR(_tmp16_,x_R__,col__2__);
  for (int _mask_idx = 0; _mask_idx <= (MASKING_ORDER - 1); _mask_idx++) {
    _tmp17_ = L_SHIFT(_tmp16_[_mask_idx],1,32);
    colR__1__[_mask_idx] = XOR(_tmp15_[_mask_idx],_tmp17_);
  }
  MASKED_AND(_tmp19_,x_R__,y_R__);
  for (int _mask_idx = 0; _mask_idx <= (MASKING_ORDER - 1); _mask_idx++) {
    _tmp20_ = L_SHIFT(_tmp19_[_mask_idx],3,32);
    colR__0__[_mask_idx] = XOR(_tmp18_[_mask_idx],_tmp20_);
  }

}

void NonlinearLayer_Rx__V32 (/*inputs*/ DATATYPE state__[3][4][MASKING_ORDER], /*outputs*/ DATATYPE stateR__[3][4][MASKING_ORDER]) {

  // Variables declaration
  ;

  // Instructions (body)
  for (int i__ = 0; i__ <= 3; i__++) {
    SPbox_Rx__V32(state__[0][i__],state__[1][i__],state__[2][i__],stateR__[0][i__],stateR__[1][i__],stateR__[2][i__]);
  }

}

void NonlinearLayer_Rxy__V32 (/*inputs*/ DATATYPE state__[3][4][MASKING_ORDER], /*outputs*/ DATATYPE stateR__[3][4][MASKING_ORDER]) {

  // Variables declaration
  ;

  // Instructions (body)
  for (int i__ = 0; i__ <= 3; i__++) {
    SPbox_Rxy__V32(state__[0][i__],state__[1][i__],state__[2][i__],stateR__[0][i__],stateR__[1][i__],stateR__[2][i__]);
  }

}

void SmallSwap__V32 (/*inputs*/ DATATYPE state__[3][4][MASKING_ORDER], /*outputs*/ DATATYPE stateR__[3][4][MASKING_ORDER]) {

  // Variables declaration
  ;

  // Instructions (body)
  for (int _mask_idx = 0; _mask_idx <= (MASKING_ORDER - 1); _mask_idx++) {
    stateR__[0][0][_mask_idx] = state__[0][1][_mask_idx];
    stateR__[0][1][_mask_idx] = state__[0][0][_mask_idx];
    stateR__[0][2][_mask_idx] = state__[0][3][_mask_idx];
    stateR__[0][3][_mask_idx] = state__[0][2][_mask_idx];
    stateR__[1][0][_mask_idx] = state__[1][0][_mask_idx];
    stateR__[1][1][_mask_idx] = state__[1][1][_mask_idx];
    stateR__[1][2][_mask_idx] = state__[1][2][_mask_idx];
    stateR__[1][3][_mask_idx] = state__[1][3][_mask_idx];
    stateR__[2][0][_mask_idx] = state__[2][0][_mask_idx];
    stateR__[2][1][_mask_idx] = state__[2][1][_mask_idx];
    stateR__[2][2][_mask_idx] = state__[2][2][_mask_idx];
    stateR__[2][3][_mask_idx] = state__[2][3][_mask_idx];
  }

}

void BigSwap__V32 (/*inputs*/ DATATYPE state__[3][4][MASKING_ORDER], /*outputs*/ DATATYPE stateR__[3][4][MASKING_ORDER]) {

  // Variables declaration
  ;

  // Instructions (body)
  for (int _mask_idx = 0; _mask_idx <= (MASKING_ORDER - 1); _mask_idx++) {
    stateR__[0][0][_mask_idx] = state__[0][2][_mask_idx];
    stateR__[0][1][_mask_idx] = state__[0][3][_mask_idx];
    stateR__[0][2][_mask_idx] = state__[0][0][_mask_idx];
    stateR__[0][3][_mask_idx] = state__[0][1][_mask_idx];
    stateR__[1][0][_mask_idx] = state__[1][0][_mask_idx];
    stateR__[1][1][_mask_idx] = state__[1][1][_mask_idx];
    stateR__[1][2][_mask_idx] = state__[1][2][_mask_idx];
    stateR__[1][3][_mask_idx] = state__[1][3][_mask_idx];
    stateR__[2][0][_mask_idx] = state__[2][0][_mask_idx];
    stateR__[2][1][_mask_idx] = state__[2][1][_mask_idx];
    stateR__[2][2][_mask_idx] = state__[2][2][_mask_idx];
    stateR__[2][3][_mask_idx] = state__[2][3][_mask_idx];
  }

}

void AddRC__V32 (/*inputs*/ DATATYPE state__[3][4][MASKING_ORDER],DATATYPE rc__[MASKING_ORDER], /*outputs*/ DATATYPE stateR__[3][4][MASKING_ORDER]) {

  // Variables declaration
  DATATYPE _tmp21_;

  // Instructions (body)
  for (int _mask_idx = 0; _mask_idx <= (MASKING_ORDER - 1); _mask_idx++) {
    _tmp21_ = XOR(state__[0][0][_mask_idx],rc__[_mask_idx]);
    stateR__[0][0][_mask_idx] = _tmp21_;
    stateR__[0][1][_mask_idx] = state__[0][1][_mask_idx];
    stateR__[0][2][_mask_idx] = state__[0][2][_mask_idx];
    stateR__[0][3][_mask_idx] = state__[0][3][_mask_idx];
    stateR__[1][0][_mask_idx] = state__[1][0][_mask_idx];
    stateR__[1][1][_mask_idx] = state__[1][1][_mask_idx];
    stateR__[1][2][_mask_idx] = state__[1][2][_mask_idx];
    stateR__[1][3][_mask_idx] = state__[1][3][_mask_idx];
    stateR__[2][0][_mask_idx] = state__[2][0][_mask_idx];
    stateR__[2][1][_mask_idx] = state__[2][1][_mask_idx];
    stateR__[2][2][_mask_idx] = state__[2][2][_mask_idx];
    stateR__[2][3][_mask_idx] = state__[2][3][_mask_idx];
  }

}

/* main function */
void gimli__ (/*inputs*/ DATATYPE state__[3][4][MASKING_ORDER], /*outputs*/ DATATYPE stateR__[3][4][MASKING_ORDER]) {

  // Variables declaration
  DATATYPE _tmp28_[3][4][MASKING_ORDER];
  DATATYPE _tmp29_[3][4][MASKING_ORDER];
  DATATYPE _tmp30_[3][4][MASKING_ORDER];
  DATATYPE _tmp31_[3][4][MASKING_ORDER];
  DATATYPE _tmp32_[3][4][MASKING_ORDER];
  DATATYPE _tmp33_[3][4][MASKING_ORDER];
  DATATYPE rc__[6][MASKING_ORDER];
  DATATYPE round__[3][4][MASKING_ORDER];

  // Instructions (body)
  rc__[0][0] = LIFT_32(2654435608);
  for (int _mask_idx = 1; _mask_idx <= (MASKING_ORDER - 1); _mask_idx++) {
    rc__[0][_mask_idx] = LIFT_32(0);
    rc__[1][_mask_idx] = LIFT_32(0);
    rc__[2][_mask_idx] = LIFT_32(0);
    rc__[3][_mask_idx] = LIFT_32(0);
    rc__[4][_mask_idx] = LIFT_32(0);
    rc__[5][_mask_idx] = LIFT_32(0);
  }
  rc__[1][0] = LIFT_32(2654435604);
  rc__[2][0] = LIFT_32(2654435600);
  rc__[3][0] = LIFT_32(2654435596);
  rc__[4][0] = LIFT_32(2654435592);
  rc__[5][0] = LIFT_32(2654435588);
  for (int _mask_idx = 0; _mask_idx <= (MASKING_ORDER - 1); _mask_idx++) {
    round__[0][0][_mask_idx] = state__[0][0][_mask_idx];
    round__[0][1][_mask_idx] = state__[0][1][_mask_idx];
    round__[0][2][_mask_idx] = state__[0][2][_mask_idx];
    round__[0][3][_mask_idx] = state__[0][3][_mask_idx];
    round__[1][0][_mask_idx] = state__[1][0][_mask_idx];
    round__[1][1][_mask_idx] = state__[1][1][_mask_idx];
    round__[1][2][_mask_idx] = state__[1][2][_mask_idx];
    round__[1][3][_mask_idx] = state__[1][3][_mask_idx];
    round__[2][0][_mask_idx] = state__[2][0][_mask_idx];
    round__[2][1][_mask_idx] = state__[2][1][_mask_idx];
    round__[2][2][_mask_idx] = state__[2][2][_mask_idx];
    round__[2][3][_mask_idx] = state__[2][3][_mask_idx];
  }
  for (int r__ = 0; r__ <= 5; r__++) {
    NonlinearLayer_Rx__V32(round__,_tmp28_);
    SmallSwap__V32(_tmp28_,_tmp29_);
    AddRC__V32(_tmp29_,rc__[r__],_tmp30_);
    NonlinearLayer_Rxy__V32(_tmp30_,_tmp31_);
    NonlinearLayer_Rx__V32(_tmp31_,_tmp32_);
    BigSwap__V32(_tmp32_,_tmp33_);
    NonlinearLayer_Rx__V32(_tmp33_,round__);
  }
  for (int _mask_idx = 0; _mask_idx <= (MASKING_ORDER - 1); _mask_idx++) {
    stateR__[0][0][_mask_idx] = round__[0][0][_mask_idx];
    stateR__[0][1][_mask_idx] = round__[0][1][_mask_idx];
    stateR__[0][2][_mask_idx] = round__[0][2][_mask_idx];
    stateR__[0][3][_mask_idx] = round__[0][3][_mask_idx];
    stateR__[1][0][_mask_idx] = round__[1][0][_mask_idx];
    stateR__[1][1][_mask_idx] = round__[1][1][_mask_idx];
    stateR__[1][2][_mask_idx] = round__[1][2][_mask_idx];
    stateR__[1][3][_mask_idx] = round__[1][3][_mask_idx];
    stateR__[2][0][_mask_idx] = round__[2][0][_mask_idx];
    stateR__[2][1][_mask_idx] = round__[2][1][_mask_idx];
    stateR__[2][2][_mask_idx] = round__[2][2][_mask_idx];
    stateR__[2][3][_mask_idx] = round__[2][3][_mask_idx];
  }

}

/* Additional functions */
uint32_t bench_speed() {
  /* inputs */
  DATATYPE state__[3][4][MASKING_ORDER] = { 0 };
  /* outputs */
  DATATYPE stateR__[3][4][MASKING_ORDER] = { 0 };
  /* fun call */
  gimli__(state__,stateR__);

  /* Returning the number of encrypted bytes */
  return 48;
}

/* **************************************************************** */
/*                            Usuba source                          */
/*                                                                  */
/*

 node SPbox_Rx(col :  u32[3] :: base)
  returns colR :  u32[3] :: base
vars
  x :  u32 :: base,
  y :  u32 :: base,
  z :  u32 :: base,
  x_R :  u32 :: base
let
  (x) = (col[0] <<< 24);
  (y) = (col[1] <<< 9);
  (z) = col[2];
  (x_R) = refresh(x);
  (colR[2]) = ((x ^ (z << 1)) ^ ((y & z) << 2));
  (colR[1]) = ((y ^ x) ^ ((x_R | z) << 1));
  (colR[0]) = ((z ^ y) ^ ((x_R & y) << 3))
tel

 node SPbox_Rxy(col :  u32[3] :: base)
  returns colR :  u32[3] :: base
vars
  x :  u32 :: base,
  y :  u32 :: base,
  z :  u32 :: base,
  x_R :  u32 :: base,
  y_R :  u32 :: base
let
  (x) = (col[0] <<< 24);
  (y) = (col[1] <<< 9);
  (z) = col[2];
  (x_R) = refresh(x);
  (y_R) = refresh(y);
  (colR[2]) = ((x ^ (z << 1)) ^ ((y_R & z) << 2));
  (colR[1]) = ((y ^ x) ^ ((x_R | z) << 1));
  (colR[0]) = ((z ^ y) ^ ((x_R & y_R) << 3))
tel

 node NonlinearLayer_Rx(state :  u32x4[3] :: base)
  returns stateR :  u32x4[3] :: base
vars

let
  forall i in [0,3] {
    (stateR[0 .. 2][i]) = SPbox_Rx(state[0 .. 2][i])
  }
tel

 node NonlinearLayer_Rxy(state :  u32x4[3] :: base)
  returns stateR :  u32x4[3] :: base
vars

let
  forall i in [0,3] {
    (stateR[0 .. 2][i]) = SPbox_Rxy(state[0 .. 2][i])
  }
tel

 node SmallSwap(state :  u32x4[3] :: base)
  returns stateR :  u32x4[3] :: base
vars

let
  (stateR) = (state[0][1,0,3,2],state[1,2][0 .. 3])
tel

 node BigSwap(state :  u32x4[3] :: base)
  returns stateR :  u32x4[3] :: base
vars

let
  (stateR) = (state[0][2,3,0,1],state[1,2][0 .. 3])
tel

 node AddRC(state :  u32x4[3] :: base,rc :  u32 :: base)
  returns stateR :  u32x4[3] :: base
vars

let
  (stateR) = ((state[0][0] ^ rc),state[0][1 .. 3],state[1,2])
tel

 node gimli(state :  u32x4[3] :: base)
  returns stateR :  u32x4[3] :: base
vars
  rc :  u32[6] :: base,
  round :  u32x4[7][3] :: base
let
  (rc) = (2654435608,2654435604,2654435600,2654435596,2654435592,2654435588);
  (round[0]) = state;
  forall r in [0,5] {
    (round[(r + 1)]) = NonlinearLayer_Rx(BigSwap(NonlinearLayer_Rx(NonlinearLayer_Rxy(AddRC(SmallSwap(NonlinearLayer_Rx(round[r])),rc[r])))))
  };
  (stateR) = round[6]
tel

*/
 