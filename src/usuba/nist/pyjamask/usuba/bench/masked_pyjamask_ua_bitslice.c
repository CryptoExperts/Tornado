/* This code was generated by Usuba.
   See https://github.com/DadaIsCrazy/usuba.
   From the file "nist/pyjamask/usuba/ua/pyjamask_bitslice.ua" (included below). */

#include <stdint.h>

/* Do NOT change the order of those define/include */

#ifndef BITS_PER_REG
#define BITS_PER_REG 32
#endif
/* including the architecture specific .h */
#include "MASKED_UA.h"

/* auxiliary functions */
void SubBytes__B1 (/*inputs*/ DATATYPE s0[MASKING_ORDER],DATATYPE s1[MASKING_ORDER],DATATYPE s2[MASKING_ORDER],DATATYPE s3[MASKING_ORDER], /*outputs*/ DATATYPE ret0__[MASKING_ORDER],DATATYPE ret1__[MASKING_ORDER],DATATYPE ret2__[MASKING_ORDER],DATATYPE ret3__[MASKING_ORDER]) {

  // Variables declaration
  DATATYPE _shadow_s01_[MASKING_ORDER];
  DATATYPE _shadow_s03_[MASKING_ORDER];
  DATATYPE _shadow_s14_[MASKING_ORDER];
  DATATYPE _shadow_s17_;
  DATATYPE _shadow_s25_;
  DATATYPE _shadow_s26_;
  DATATYPE _shadow_s32_[MASKING_ORDER];
  DATATYPE _shadow_s38_[MASKING_ORDER];
  DATATYPE _tmp1_[MASKING_ORDER];
  DATATYPE _tmp2_[MASKING_ORDER];
  DATATYPE _tmp3_[MASKING_ORDER];
  DATATYPE _tmp4_[MASKING_ORDER];

  // Instructions (body)
  for (int _mask_idx = 0; _mask_idx <= (MASKING_ORDER - 1); _mask_idx++) {
    _shadow_s01_[_mask_idx] = XOR(s0[_mask_idx],s3[_mask_idx]);
  }
  MASKED_AND(_tmp1_,_shadow_s01_,s1);
  for (int _mask_idx = 0; _mask_idx <= (MASKING_ORDER - 1); _mask_idx++) {
    _shadow_s32_[_mask_idx] = XOR(s3[_mask_idx],_tmp1_[_mask_idx]);
  }
  MASKED_AND(_tmp2_,s1,s2);
  for (int _mask_idx = 0; _mask_idx <= (MASKING_ORDER - 1); _mask_idx++) {
    _shadow_s03_[_mask_idx] = XOR(_shadow_s01_[_mask_idx],_tmp2_[_mask_idx]);
    ret0__[_mask_idx] = _shadow_s03_[_mask_idx];
  }
  MASKED_AND(_tmp3_,s2,_shadow_s32_);
  for (int _mask_idx = 0; _mask_idx <= (MASKING_ORDER - 1); _mask_idx++) {
    _shadow_s14_[_mask_idx] = XOR(s1[_mask_idx],_tmp3_[_mask_idx]);
    _shadow_s17_ = XOR(_shadow_s14_[_mask_idx],_shadow_s03_[_mask_idx]);
    ret1__[_mask_idx] = _shadow_s17_;
  }
  MASKED_AND(_tmp4_,_shadow_s03_,_shadow_s32_);
  for (int _mask_idx = 0; _mask_idx <= (MASKING_ORDER - 1); _mask_idx++) {
    _shadow_s25_ = XOR(s2[_mask_idx],_tmp4_[_mask_idx]);
    _shadow_s26_ = XOR(_shadow_s25_,_shadow_s14_[_mask_idx]);
    ret3__[_mask_idx] = _shadow_s26_;
  }
  _shadow_s38_[0] = NOT(_shadow_s32_[0]);
  for (int _mask_idx = 1; _mask_idx <= (MASKING_ORDER - 1); _mask_idx++) {
    _shadow_s38_[_mask_idx] = _shadow_s32_[_mask_idx];
  }
  for (int _mask_idx = 0; _mask_idx <= (MASKING_ORDER - 1); _mask_idx++) {
    ret2__[_mask_idx] = _shadow_s38_[_mask_idx];
  }

}

void AddRoundKey__B1 (/*inputs*/ DATATYPE i__[128][MASKING_ORDER],DATATYPE k__[128][MASKING_ORDER], /*outputs*/ DATATYPE o__[128][MASKING_ORDER]) {

  // Variables declaration
  ;

  // Instructions (body)
  for (int _mask_idx = 0; _mask_idx <= (MASKING_ORDER - 1); _mask_idx++) {
    o__[0][_mask_idx] = XOR(i__[0][_mask_idx],k__[0][_mask_idx]);
    o__[1][_mask_idx] = XOR(i__[1][_mask_idx],k__[1][_mask_idx]);
    o__[2][_mask_idx] = XOR(i__[2][_mask_idx],k__[2][_mask_idx]);
    o__[3][_mask_idx] = XOR(i__[3][_mask_idx],k__[3][_mask_idx]);
    o__[4][_mask_idx] = XOR(i__[4][_mask_idx],k__[4][_mask_idx]);
    o__[5][_mask_idx] = XOR(i__[5][_mask_idx],k__[5][_mask_idx]);
    o__[6][_mask_idx] = XOR(i__[6][_mask_idx],k__[6][_mask_idx]);
    o__[7][_mask_idx] = XOR(i__[7][_mask_idx],k__[7][_mask_idx]);
    o__[8][_mask_idx] = XOR(i__[8][_mask_idx],k__[8][_mask_idx]);
    o__[9][_mask_idx] = XOR(i__[9][_mask_idx],k__[9][_mask_idx]);
    o__[10][_mask_idx] = XOR(i__[10][_mask_idx],k__[10][_mask_idx]);
    o__[11][_mask_idx] = XOR(i__[11][_mask_idx],k__[11][_mask_idx]);
    o__[12][_mask_idx] = XOR(i__[12][_mask_idx],k__[12][_mask_idx]);
    o__[13][_mask_idx] = XOR(i__[13][_mask_idx],k__[13][_mask_idx]);
    o__[14][_mask_idx] = XOR(i__[14][_mask_idx],k__[14][_mask_idx]);
    o__[15][_mask_idx] = XOR(i__[15][_mask_idx],k__[15][_mask_idx]);
    o__[16][_mask_idx] = XOR(i__[16][_mask_idx],k__[16][_mask_idx]);
    o__[17][_mask_idx] = XOR(i__[17][_mask_idx],k__[17][_mask_idx]);
    o__[18][_mask_idx] = XOR(i__[18][_mask_idx],k__[18][_mask_idx]);
    o__[19][_mask_idx] = XOR(i__[19][_mask_idx],k__[19][_mask_idx]);
    o__[20][_mask_idx] = XOR(i__[20][_mask_idx],k__[20][_mask_idx]);
    o__[21][_mask_idx] = XOR(i__[21][_mask_idx],k__[21][_mask_idx]);
    o__[22][_mask_idx] = XOR(i__[22][_mask_idx],k__[22][_mask_idx]);
    o__[23][_mask_idx] = XOR(i__[23][_mask_idx],k__[23][_mask_idx]);
    o__[24][_mask_idx] = XOR(i__[24][_mask_idx],k__[24][_mask_idx]);
    o__[25][_mask_idx] = XOR(i__[25][_mask_idx],k__[25][_mask_idx]);
    o__[26][_mask_idx] = XOR(i__[26][_mask_idx],k__[26][_mask_idx]);
    o__[27][_mask_idx] = XOR(i__[27][_mask_idx],k__[27][_mask_idx]);
    o__[28][_mask_idx] = XOR(i__[28][_mask_idx],k__[28][_mask_idx]);
    o__[29][_mask_idx] = XOR(i__[29][_mask_idx],k__[29][_mask_idx]);
    o__[30][_mask_idx] = XOR(i__[30][_mask_idx],k__[30][_mask_idx]);
    o__[31][_mask_idx] = XOR(i__[31][_mask_idx],k__[31][_mask_idx]);
    o__[32][_mask_idx] = XOR(i__[32][_mask_idx],k__[32][_mask_idx]);
    o__[33][_mask_idx] = XOR(i__[33][_mask_idx],k__[33][_mask_idx]);
    o__[34][_mask_idx] = XOR(i__[34][_mask_idx],k__[34][_mask_idx]);
    o__[35][_mask_idx] = XOR(i__[35][_mask_idx],k__[35][_mask_idx]);
    o__[36][_mask_idx] = XOR(i__[36][_mask_idx],k__[36][_mask_idx]);
    o__[37][_mask_idx] = XOR(i__[37][_mask_idx],k__[37][_mask_idx]);
    o__[38][_mask_idx] = XOR(i__[38][_mask_idx],k__[38][_mask_idx]);
    o__[39][_mask_idx] = XOR(i__[39][_mask_idx],k__[39][_mask_idx]);
    o__[40][_mask_idx] = XOR(i__[40][_mask_idx],k__[40][_mask_idx]);
    o__[41][_mask_idx] = XOR(i__[41][_mask_idx],k__[41][_mask_idx]);
    o__[42][_mask_idx] = XOR(i__[42][_mask_idx],k__[42][_mask_idx]);
    o__[43][_mask_idx] = XOR(i__[43][_mask_idx],k__[43][_mask_idx]);
    o__[44][_mask_idx] = XOR(i__[44][_mask_idx],k__[44][_mask_idx]);
    o__[45][_mask_idx] = XOR(i__[45][_mask_idx],k__[45][_mask_idx]);
    o__[46][_mask_idx] = XOR(i__[46][_mask_idx],k__[46][_mask_idx]);
    o__[47][_mask_idx] = XOR(i__[47][_mask_idx],k__[47][_mask_idx]);
    o__[48][_mask_idx] = XOR(i__[48][_mask_idx],k__[48][_mask_idx]);
    o__[49][_mask_idx] = XOR(i__[49][_mask_idx],k__[49][_mask_idx]);
    o__[50][_mask_idx] = XOR(i__[50][_mask_idx],k__[50][_mask_idx]);
    o__[51][_mask_idx] = XOR(i__[51][_mask_idx],k__[51][_mask_idx]);
    o__[52][_mask_idx] = XOR(i__[52][_mask_idx],k__[52][_mask_idx]);
    o__[53][_mask_idx] = XOR(i__[53][_mask_idx],k__[53][_mask_idx]);
    o__[54][_mask_idx] = XOR(i__[54][_mask_idx],k__[54][_mask_idx]);
    o__[55][_mask_idx] = XOR(i__[55][_mask_idx],k__[55][_mask_idx]);
    o__[56][_mask_idx] = XOR(i__[56][_mask_idx],k__[56][_mask_idx]);
    o__[57][_mask_idx] = XOR(i__[57][_mask_idx],k__[57][_mask_idx]);
    o__[58][_mask_idx] = XOR(i__[58][_mask_idx],k__[58][_mask_idx]);
    o__[59][_mask_idx] = XOR(i__[59][_mask_idx],k__[59][_mask_idx]);
    o__[60][_mask_idx] = XOR(i__[60][_mask_idx],k__[60][_mask_idx]);
    o__[61][_mask_idx] = XOR(i__[61][_mask_idx],k__[61][_mask_idx]);
    o__[62][_mask_idx] = XOR(i__[62][_mask_idx],k__[62][_mask_idx]);
    o__[63][_mask_idx] = XOR(i__[63][_mask_idx],k__[63][_mask_idx]);
    o__[64][_mask_idx] = XOR(i__[64][_mask_idx],k__[64][_mask_idx]);
    o__[65][_mask_idx] = XOR(i__[65][_mask_idx],k__[65][_mask_idx]);
    o__[66][_mask_idx] = XOR(i__[66][_mask_idx],k__[66][_mask_idx]);
    o__[67][_mask_idx] = XOR(i__[67][_mask_idx],k__[67][_mask_idx]);
    o__[68][_mask_idx] = XOR(i__[68][_mask_idx],k__[68][_mask_idx]);
    o__[69][_mask_idx] = XOR(i__[69][_mask_idx],k__[69][_mask_idx]);
    o__[70][_mask_idx] = XOR(i__[70][_mask_idx],k__[70][_mask_idx]);
    o__[71][_mask_idx] = XOR(i__[71][_mask_idx],k__[71][_mask_idx]);
    o__[72][_mask_idx] = XOR(i__[72][_mask_idx],k__[72][_mask_idx]);
    o__[73][_mask_idx] = XOR(i__[73][_mask_idx],k__[73][_mask_idx]);
    o__[74][_mask_idx] = XOR(i__[74][_mask_idx],k__[74][_mask_idx]);
    o__[75][_mask_idx] = XOR(i__[75][_mask_idx],k__[75][_mask_idx]);
    o__[76][_mask_idx] = XOR(i__[76][_mask_idx],k__[76][_mask_idx]);
    o__[77][_mask_idx] = XOR(i__[77][_mask_idx],k__[77][_mask_idx]);
    o__[78][_mask_idx] = XOR(i__[78][_mask_idx],k__[78][_mask_idx]);
    o__[79][_mask_idx] = XOR(i__[79][_mask_idx],k__[79][_mask_idx]);
    o__[80][_mask_idx] = XOR(i__[80][_mask_idx],k__[80][_mask_idx]);
    o__[81][_mask_idx] = XOR(i__[81][_mask_idx],k__[81][_mask_idx]);
    o__[82][_mask_idx] = XOR(i__[82][_mask_idx],k__[82][_mask_idx]);
    o__[83][_mask_idx] = XOR(i__[83][_mask_idx],k__[83][_mask_idx]);
    o__[84][_mask_idx] = XOR(i__[84][_mask_idx],k__[84][_mask_idx]);
    o__[85][_mask_idx] = XOR(i__[85][_mask_idx],k__[85][_mask_idx]);
    o__[86][_mask_idx] = XOR(i__[86][_mask_idx],k__[86][_mask_idx]);
    o__[87][_mask_idx] = XOR(i__[87][_mask_idx],k__[87][_mask_idx]);
    o__[88][_mask_idx] = XOR(i__[88][_mask_idx],k__[88][_mask_idx]);
    o__[89][_mask_idx] = XOR(i__[89][_mask_idx],k__[89][_mask_idx]);
    o__[90][_mask_idx] = XOR(i__[90][_mask_idx],k__[90][_mask_idx]);
    o__[91][_mask_idx] = XOR(i__[91][_mask_idx],k__[91][_mask_idx]);
    o__[92][_mask_idx] = XOR(i__[92][_mask_idx],k__[92][_mask_idx]);
    o__[93][_mask_idx] = XOR(i__[93][_mask_idx],k__[93][_mask_idx]);
    o__[94][_mask_idx] = XOR(i__[94][_mask_idx],k__[94][_mask_idx]);
    o__[95][_mask_idx] = XOR(i__[95][_mask_idx],k__[95][_mask_idx]);
    o__[96][_mask_idx] = XOR(i__[96][_mask_idx],k__[96][_mask_idx]);
    o__[97][_mask_idx] = XOR(i__[97][_mask_idx],k__[97][_mask_idx]);
    o__[98][_mask_idx] = XOR(i__[98][_mask_idx],k__[98][_mask_idx]);
    o__[99][_mask_idx] = XOR(i__[99][_mask_idx],k__[99][_mask_idx]);
    o__[100][_mask_idx] = XOR(i__[100][_mask_idx],k__[100][_mask_idx]);
    o__[101][_mask_idx] = XOR(i__[101][_mask_idx],k__[101][_mask_idx]);
    o__[102][_mask_idx] = XOR(i__[102][_mask_idx],k__[102][_mask_idx]);
    o__[103][_mask_idx] = XOR(i__[103][_mask_idx],k__[103][_mask_idx]);
    o__[104][_mask_idx] = XOR(i__[104][_mask_idx],k__[104][_mask_idx]);
    o__[105][_mask_idx] = XOR(i__[105][_mask_idx],k__[105][_mask_idx]);
    o__[106][_mask_idx] = XOR(i__[106][_mask_idx],k__[106][_mask_idx]);
    o__[107][_mask_idx] = XOR(i__[107][_mask_idx],k__[107][_mask_idx]);
    o__[108][_mask_idx] = XOR(i__[108][_mask_idx],k__[108][_mask_idx]);
    o__[109][_mask_idx] = XOR(i__[109][_mask_idx],k__[109][_mask_idx]);
    o__[110][_mask_idx] = XOR(i__[110][_mask_idx],k__[110][_mask_idx]);
    o__[111][_mask_idx] = XOR(i__[111][_mask_idx],k__[111][_mask_idx]);
    o__[112][_mask_idx] = XOR(i__[112][_mask_idx],k__[112][_mask_idx]);
    o__[113][_mask_idx] = XOR(i__[113][_mask_idx],k__[113][_mask_idx]);
    o__[114][_mask_idx] = XOR(i__[114][_mask_idx],k__[114][_mask_idx]);
    o__[115][_mask_idx] = XOR(i__[115][_mask_idx],k__[115][_mask_idx]);
    o__[116][_mask_idx] = XOR(i__[116][_mask_idx],k__[116][_mask_idx]);
    o__[117][_mask_idx] = XOR(i__[117][_mask_idx],k__[117][_mask_idx]);
    o__[118][_mask_idx] = XOR(i__[118][_mask_idx],k__[118][_mask_idx]);
    o__[119][_mask_idx] = XOR(i__[119][_mask_idx],k__[119][_mask_idx]);
    o__[120][_mask_idx] = XOR(i__[120][_mask_idx],k__[120][_mask_idx]);
    o__[121][_mask_idx] = XOR(i__[121][_mask_idx],k__[121][_mask_idx]);
    o__[122][_mask_idx] = XOR(i__[122][_mask_idx],k__[122][_mask_idx]);
    o__[123][_mask_idx] = XOR(i__[123][_mask_idx],k__[123][_mask_idx]);
    o__[124][_mask_idx] = XOR(i__[124][_mask_idx],k__[124][_mask_idx]);
    o__[125][_mask_idx] = XOR(i__[125][_mask_idx],k__[125][_mask_idx]);
    o__[126][_mask_idx] = XOR(i__[126][_mask_idx],k__[126][_mask_idx]);
    o__[127][_mask_idx] = XOR(i__[127][_mask_idx],k__[127][_mask_idx]);
  }

}

void SubBytesAll__B1 (/*inputs*/ DATATYPE input__[128][MASKING_ORDER], /*outputs*/ DATATYPE output__[4][32][MASKING_ORDER]) {

  // Variables declaration
  ;

  // Instructions (body)
  for (int i__ = 0; i__ <= 31; i__++) {
    SubBytes__B1(input__[(0 + i__)],input__[(32 + i__)],input__[(64 + i__)],input__[(96 + i__)],output__[0][i__],output__[1][i__],output__[2][i__],output__[3][i__]);
  }

}

void col_mult__B1 (/*inputs*/ DATATYPE a__[32][MASKING_ORDER],DATATYPE b__[32][MASKING_ORDER], /*outputs*/ DATATYPE r__[MASKING_ORDER]) {

  // Variables declaration
  DATATYPE _tmp5_[MASKING_ORDER];
  DATATYPE acc__[MASKING_ORDER];

  // Instructions (body)
  for (int _mask_idx = 0; _mask_idx <= (MASKING_ORDER - 1); _mask_idx++) {
    acc__[_mask_idx] = AND(a__[0][_mask_idx],b__[0][0]);
  }
  for (int i__ = 1; i__ <= 31; i__++) {
    for (int _mask_idx = 0; _mask_idx <= (MASKING_ORDER - 1); _mask_idx++) {
      _tmp5_[_mask_idx] = AND(a__[i__][_mask_idx],b__[i__][0]);
      acc__[_mask_idx] = XOR(acc__[_mask_idx],_tmp5_[_mask_idx]);
    }
  }
  for (int _mask_idx = 0; _mask_idx <= (MASKING_ORDER - 1); _mask_idx++) {
    r__[_mask_idx] = acc__[_mask_idx];
  }

}

void MixRows__B1 (/*inputs*/ DATATYPE input__[4][32][MASKING_ORDER], /*outputs*/ DATATYPE output__[128][MASKING_ORDER]) {

  // Variables declaration
  DATATYPE M__[4][33][32][MASKING_ORDER];

  // Instructions (body)
  M__[0][0][0][0] = SET_ALL_ONE();
  for (int _mask_idx = 1; _mask_idx <= (MASKING_ORDER - 1); _mask_idx++) {
    M__[0][0][0][_mask_idx] = SET_ALL_ZERO();
    M__[0][0][1][_mask_idx] = SET_ALL_ZERO();
    M__[0][0][2][_mask_idx] = SET_ALL_ZERO();
    M__[0][0][3][_mask_idx] = SET_ALL_ZERO();
    M__[0][0][4][_mask_idx] = SET_ALL_ZERO();
    M__[0][0][5][_mask_idx] = SET_ALL_ZERO();
    M__[0][0][6][_mask_idx] = SET_ALL_ZERO();
    M__[0][0][7][_mask_idx] = SET_ALL_ZERO();
    M__[0][0][8][_mask_idx] = SET_ALL_ZERO();
    M__[0][0][9][_mask_idx] = SET_ALL_ZERO();
    M__[0][0][10][_mask_idx] = SET_ALL_ZERO();
    M__[0][0][11][_mask_idx] = SET_ALL_ZERO();
    M__[0][0][12][_mask_idx] = SET_ALL_ZERO();
    M__[0][0][13][_mask_idx] = SET_ALL_ZERO();
    M__[0][0][14][_mask_idx] = SET_ALL_ZERO();
    M__[0][0][15][_mask_idx] = SET_ALL_ZERO();
    M__[0][0][16][_mask_idx] = SET_ALL_ZERO();
    M__[0][0][17][_mask_idx] = SET_ALL_ZERO();
    M__[0][0][18][_mask_idx] = SET_ALL_ZERO();
    M__[0][0][19][_mask_idx] = SET_ALL_ZERO();
    M__[0][0][20][_mask_idx] = SET_ALL_ZERO();
    M__[0][0][21][_mask_idx] = SET_ALL_ZERO();
    M__[0][0][22][_mask_idx] = SET_ALL_ZERO();
    M__[0][0][23][_mask_idx] = SET_ALL_ZERO();
    M__[0][0][24][_mask_idx] = SET_ALL_ZERO();
    M__[0][0][25][_mask_idx] = SET_ALL_ZERO();
    M__[0][0][26][_mask_idx] = SET_ALL_ZERO();
    M__[0][0][27][_mask_idx] = SET_ALL_ZERO();
    M__[0][0][28][_mask_idx] = SET_ALL_ZERO();
    M__[0][0][29][_mask_idx] = SET_ALL_ZERO();
    M__[0][0][30][_mask_idx] = SET_ALL_ZERO();
    M__[0][0][31][_mask_idx] = SET_ALL_ZERO();
    M__[1][0][0][_mask_idx] = SET_ALL_ZERO();
    M__[1][0][1][_mask_idx] = SET_ALL_ZERO();
    M__[1][0][2][_mask_idx] = SET_ALL_ZERO();
    M__[1][0][3][_mask_idx] = SET_ALL_ZERO();
    M__[1][0][4][_mask_idx] = SET_ALL_ZERO();
    M__[1][0][5][_mask_idx] = SET_ALL_ZERO();
    M__[1][0][6][_mask_idx] = SET_ALL_ZERO();
    M__[1][0][7][_mask_idx] = SET_ALL_ZERO();
    M__[1][0][8][_mask_idx] = SET_ALL_ZERO();
    M__[1][0][9][_mask_idx] = SET_ALL_ZERO();
    M__[1][0][10][_mask_idx] = SET_ALL_ZERO();
    M__[1][0][11][_mask_idx] = SET_ALL_ZERO();
    M__[1][0][12][_mask_idx] = SET_ALL_ZERO();
    M__[1][0][13][_mask_idx] = SET_ALL_ZERO();
    M__[1][0][14][_mask_idx] = SET_ALL_ZERO();
    M__[1][0][15][_mask_idx] = SET_ALL_ZERO();
    M__[1][0][16][_mask_idx] = SET_ALL_ZERO();
    M__[1][0][17][_mask_idx] = SET_ALL_ZERO();
    M__[1][0][18][_mask_idx] = SET_ALL_ZERO();
    M__[1][0][19][_mask_idx] = SET_ALL_ZERO();
    M__[1][0][20][_mask_idx] = SET_ALL_ZERO();
    M__[1][0][21][_mask_idx] = SET_ALL_ZERO();
    M__[1][0][22][_mask_idx] = SET_ALL_ZERO();
    M__[1][0][23][_mask_idx] = SET_ALL_ZERO();
    M__[1][0][24][_mask_idx] = SET_ALL_ZERO();
    M__[1][0][25][_mask_idx] = SET_ALL_ZERO();
    M__[1][0][26][_mask_idx] = SET_ALL_ZERO();
    M__[1][0][27][_mask_idx] = SET_ALL_ZERO();
    M__[1][0][28][_mask_idx] = SET_ALL_ZERO();
    M__[1][0][29][_mask_idx] = SET_ALL_ZERO();
    M__[1][0][30][_mask_idx] = SET_ALL_ZERO();
    M__[1][0][31][_mask_idx] = SET_ALL_ZERO();
    M__[2][0][0][_mask_idx] = SET_ALL_ZERO();
    M__[2][0][1][_mask_idx] = SET_ALL_ZERO();
    M__[2][0][2][_mask_idx] = SET_ALL_ZERO();
    M__[2][0][3][_mask_idx] = SET_ALL_ZERO();
    M__[2][0][4][_mask_idx] = SET_ALL_ZERO();
    M__[2][0][5][_mask_idx] = SET_ALL_ZERO();
    M__[2][0][6][_mask_idx] = SET_ALL_ZERO();
    M__[2][0][7][_mask_idx] = SET_ALL_ZERO();
    M__[2][0][8][_mask_idx] = SET_ALL_ZERO();
    M__[2][0][9][_mask_idx] = SET_ALL_ZERO();
    M__[2][0][10][_mask_idx] = SET_ALL_ZERO();
    M__[2][0][11][_mask_idx] = SET_ALL_ZERO();
    M__[2][0][12][_mask_idx] = SET_ALL_ZERO();
    M__[2][0][13][_mask_idx] = SET_ALL_ZERO();
    M__[2][0][14][_mask_idx] = SET_ALL_ZERO();
    M__[2][0][15][_mask_idx] = SET_ALL_ZERO();
    M__[2][0][16][_mask_idx] = SET_ALL_ZERO();
    M__[2][0][17][_mask_idx] = SET_ALL_ZERO();
    M__[2][0][18][_mask_idx] = SET_ALL_ZERO();
    M__[2][0][19][_mask_idx] = SET_ALL_ZERO();
    M__[2][0][20][_mask_idx] = SET_ALL_ZERO();
    M__[2][0][21][_mask_idx] = SET_ALL_ZERO();
    M__[2][0][22][_mask_idx] = SET_ALL_ZERO();
    M__[2][0][23][_mask_idx] = SET_ALL_ZERO();
    M__[2][0][24][_mask_idx] = SET_ALL_ZERO();
    M__[2][0][25][_mask_idx] = SET_ALL_ZERO();
    M__[2][0][26][_mask_idx] = SET_ALL_ZERO();
    M__[2][0][27][_mask_idx] = SET_ALL_ZERO();
    M__[2][0][28][_mask_idx] = SET_ALL_ZERO();
    M__[2][0][29][_mask_idx] = SET_ALL_ZERO();
    M__[2][0][30][_mask_idx] = SET_ALL_ZERO();
    M__[2][0][31][_mask_idx] = SET_ALL_ZERO();
    M__[3][0][0][_mask_idx] = SET_ALL_ZERO();
    M__[3][0][1][_mask_idx] = SET_ALL_ZERO();
    M__[3][0][2][_mask_idx] = SET_ALL_ZERO();
    M__[3][0][3][_mask_idx] = SET_ALL_ZERO();
    M__[3][0][4][_mask_idx] = SET_ALL_ZERO();
    M__[3][0][5][_mask_idx] = SET_ALL_ZERO();
    M__[3][0][6][_mask_idx] = SET_ALL_ZERO();
    M__[3][0][7][_mask_idx] = SET_ALL_ZERO();
    M__[3][0][8][_mask_idx] = SET_ALL_ZERO();
    M__[3][0][9][_mask_idx] = SET_ALL_ZERO();
    M__[3][0][10][_mask_idx] = SET_ALL_ZERO();
    M__[3][0][11][_mask_idx] = SET_ALL_ZERO();
    M__[3][0][12][_mask_idx] = SET_ALL_ZERO();
    M__[3][0][13][_mask_idx] = SET_ALL_ZERO();
    M__[3][0][14][_mask_idx] = SET_ALL_ZERO();
    M__[3][0][15][_mask_idx] = SET_ALL_ZERO();
    M__[3][0][16][_mask_idx] = SET_ALL_ZERO();
    M__[3][0][17][_mask_idx] = SET_ALL_ZERO();
    M__[3][0][18][_mask_idx] = SET_ALL_ZERO();
    M__[3][0][19][_mask_idx] = SET_ALL_ZERO();
    M__[3][0][20][_mask_idx] = SET_ALL_ZERO();
    M__[3][0][21][_mask_idx] = SET_ALL_ZERO();
    M__[3][0][22][_mask_idx] = SET_ALL_ZERO();
    M__[3][0][23][_mask_idx] = SET_ALL_ZERO();
    M__[3][0][24][_mask_idx] = SET_ALL_ZERO();
    M__[3][0][25][_mask_idx] = SET_ALL_ZERO();
    M__[3][0][26][_mask_idx] = SET_ALL_ZERO();
    M__[3][0][27][_mask_idx] = SET_ALL_ZERO();
    M__[3][0][28][_mask_idx] = SET_ALL_ZERO();
    M__[3][0][29][_mask_idx] = SET_ALL_ZERO();
    M__[3][0][30][_mask_idx] = SET_ALL_ZERO();
    M__[3][0][31][_mask_idx] = SET_ALL_ZERO();
  }
  M__[0][0][1][0] = SET_ALL_ZERO();
  M__[0][0][2][0] = SET_ALL_ONE();
  M__[0][0][3][0] = SET_ALL_ZERO();
  M__[0][0][4][0] = SET_ALL_ZERO();
  M__[0][0][5][0] = SET_ALL_ZERO();
  M__[0][0][6][0] = SET_ALL_ONE();
  M__[0][0][7][0] = SET_ALL_ONE();
  M__[0][0][8][0] = SET_ALL_ONE();
  M__[0][0][9][0] = SET_ALL_ZERO();
  M__[0][0][10][0] = SET_ALL_ZERO();
  M__[0][0][11][0] = SET_ALL_ZERO();
  M__[0][0][12][0] = SET_ALL_ZERO();
  M__[0][0][13][0] = SET_ALL_ONE();
  M__[0][0][14][0] = SET_ALL_ONE();
  M__[0][0][15][0] = SET_ALL_ZERO();
  M__[0][0][16][0] = SET_ALL_ZERO();
  M__[0][0][17][0] = SET_ALL_ZERO();
  M__[0][0][18][0] = SET_ALL_ZERO();
  M__[0][0][19][0] = SET_ALL_ONE();
  M__[0][0][20][0] = SET_ALL_ZERO();
  M__[0][0][21][0] = SET_ALL_ZERO();
  M__[0][0][22][0] = SET_ALL_ZERO();
  M__[0][0][23][0] = SET_ALL_ZERO();
  M__[0][0][24][0] = SET_ALL_ONE();
  M__[0][0][25][0] = SET_ALL_ZERO();
  M__[0][0][26][0] = SET_ALL_ZERO();
  M__[0][0][27][0] = SET_ALL_ZERO();
  M__[0][0][28][0] = SET_ALL_ZERO();
  M__[0][0][29][0] = SET_ALL_ONE();
  M__[0][0][30][0] = SET_ALL_ZERO();
  M__[0][0][31][0] = SET_ALL_ONE();
  M__[1][0][0][0] = SET_ALL_ZERO();
  M__[1][0][1][0] = SET_ALL_ONE();
  M__[1][0][2][0] = SET_ALL_ONE();
  M__[1][0][3][0] = SET_ALL_ZERO();
  M__[1][0][4][0] = SET_ALL_ZERO();
  M__[1][0][5][0] = SET_ALL_ZERO();
  M__[1][0][6][0] = SET_ALL_ONE();
  M__[1][0][7][0] = SET_ALL_ONE();
  M__[1][0][8][0] = SET_ALL_ZERO();
  M__[1][0][9][0] = SET_ALL_ONE();
  M__[1][0][10][0] = SET_ALL_ZERO();
  M__[1][0][11][0] = SET_ALL_ZERO();
  M__[1][0][12][0] = SET_ALL_ZERO();
  M__[1][0][13][0] = SET_ALL_ZERO();
  M__[1][0][14][0] = SET_ALL_ZERO();
  M__[1][0][15][0] = SET_ALL_ONE();
  M__[1][0][16][0] = SET_ALL_ZERO();
  M__[1][0][17][0] = SET_ALL_ONE();
  M__[1][0][18][0] = SET_ALL_ONE();
  M__[1][0][19][0] = SET_ALL_ONE();
  M__[1][0][20][0] = SET_ALL_ZERO();
  M__[1][0][21][0] = SET_ALL_ZERO();
  M__[1][0][22][0] = SET_ALL_ZERO();
  M__[1][0][23][0] = SET_ALL_ZERO();
  M__[1][0][24][0] = SET_ALL_ZERO();
  M__[1][0][25][0] = SET_ALL_ZERO();
  M__[1][0][26][0] = SET_ALL_ONE();
  M__[1][0][27][0] = SET_ALL_ZERO();
  M__[1][0][28][0] = SET_ALL_ZERO();
  M__[1][0][29][0] = SET_ALL_ZERO();
  M__[1][0][30][0] = SET_ALL_ZERO();
  M__[1][0][31][0] = SET_ALL_ONE();
  M__[2][0][0][0] = SET_ALL_ZERO();
  M__[2][0][1][0] = SET_ALL_ONE();
  M__[2][0][2][0] = SET_ALL_ONE();
  M__[2][0][3][0] = SET_ALL_ZERO();
  M__[2][0][4][0] = SET_ALL_ONE();
  M__[2][0][5][0] = SET_ALL_ZERO();
  M__[2][0][6][0] = SET_ALL_ZERO();
  M__[2][0][7][0] = SET_ALL_ONE();
  M__[2][0][8][0] = SET_ALL_ZERO();
  M__[2][0][9][0] = SET_ALL_ZERO();
  M__[2][0][10][0] = SET_ALL_ONE();
  M__[2][0][11][0] = SET_ALL_ZERO();
  M__[2][0][12][0] = SET_ALL_ONE();
  M__[2][0][13][0] = SET_ALL_ONE();
  M__[2][0][14][0] = SET_ALL_ZERO();
  M__[2][0][15][0] = SET_ALL_ZERO();
  M__[2][0][16][0] = SET_ALL_ONE();
  M__[2][0][17][0] = SET_ALL_ONE();
  M__[2][0][18][0] = SET_ALL_ONE();
  M__[2][0][19][0] = SET_ALL_ONE();
  M__[2][0][20][0] = SET_ALL_ZERO();
  M__[2][0][21][0] = SET_ALL_ZERO();
  M__[2][0][22][0] = SET_ALL_ONE();
  M__[2][0][23][0] = SET_ALL_ZERO();
  M__[2][0][24][0] = SET_ALL_ONE();
  M__[2][0][25][0] = SET_ALL_ZERO();
  M__[2][0][26][0] = SET_ALL_ZERO();
  M__[2][0][27][0] = SET_ALL_ZERO();
  M__[2][0][28][0] = SET_ALL_ZERO();
  M__[2][0][29][0] = SET_ALL_ZERO();
  M__[2][0][30][0] = SET_ALL_ZERO();
  M__[2][0][31][0] = SET_ALL_ZERO();
  M__[3][0][0][0] = SET_ALL_ZERO();
  M__[3][0][1][0] = SET_ALL_ONE();
  M__[3][0][2][0] = SET_ALL_ZERO();
  M__[3][0][3][0] = SET_ALL_ZERO();
  M__[3][0][4][0] = SET_ALL_ONE();
  M__[3][0][5][0] = SET_ALL_ZERO();
  M__[3][0][6][0] = SET_ALL_ZERO();
  M__[3][0][7][0] = SET_ALL_ZERO();
  M__[3][0][8][0] = SET_ALL_ONE();
  M__[3][0][9][0] = SET_ALL_ZERO();
  M__[3][0][10][0] = SET_ALL_ONE();
  M__[3][0][11][0] = SET_ALL_ZERO();
  M__[3][0][12][0] = SET_ALL_ZERO();
  M__[3][0][13][0] = SET_ALL_ONE();
  M__[3][0][14][0] = SET_ALL_ZERO();
  M__[3][0][15][0] = SET_ALL_ONE();
  M__[3][0][16][0] = SET_ALL_ZERO();
  M__[3][0][17][0] = SET_ALL_ONE();
  M__[3][0][18][0] = SET_ALL_ZERO();
  M__[3][0][19][0] = SET_ALL_ZERO();
  M__[3][0][20][0] = SET_ALL_ONE();
  M__[3][0][21][0] = SET_ALL_ZERO();
  M__[3][0][22][0] = SET_ALL_ZERO();
  M__[3][0][23][0] = SET_ALL_ZERO();
  M__[3][0][24][0] = SET_ALL_ZERO();
  M__[3][0][25][0] = SET_ALL_ZERO();
  M__[3][0][26][0] = SET_ALL_ZERO();
  M__[3][0][27][0] = SET_ALL_ONE();
  M__[3][0][28][0] = SET_ALL_ZERO();
  M__[3][0][29][0] = SET_ALL_ZERO();
  M__[3][0][30][0] = SET_ALL_ONE();
  M__[3][0][31][0] = SET_ALL_ONE();
  for (int col__ = 0; col__ <= 3; col__++) {
    for (int idx__ = 0; idx__ <= 31; idx__++) {
      col_mult__B1(input__[col__],M__[col__][idx__],output__[((col__ * 32) + idx__)]);
      for (int _mask_idx = 0; _mask_idx <= (MASKING_ORDER - 1); _mask_idx++) {
        M__[col__][(idx__ + 1)][0][_mask_idx] = M__[col__][idx__][31][_mask_idx];
        M__[col__][(idx__ + 1)][1][_mask_idx] = M__[col__][idx__][0][_mask_idx];
        M__[col__][(idx__ + 1)][2][_mask_idx] = M__[col__][idx__][1][_mask_idx];
        M__[col__][(idx__ + 1)][3][_mask_idx] = M__[col__][idx__][2][_mask_idx];
        M__[col__][(idx__ + 1)][4][_mask_idx] = M__[col__][idx__][3][_mask_idx];
        M__[col__][(idx__ + 1)][5][_mask_idx] = M__[col__][idx__][4][_mask_idx];
        M__[col__][(idx__ + 1)][6][_mask_idx] = M__[col__][idx__][5][_mask_idx];
        M__[col__][(idx__ + 1)][7][_mask_idx] = M__[col__][idx__][6][_mask_idx];
        M__[col__][(idx__ + 1)][8][_mask_idx] = M__[col__][idx__][7][_mask_idx];
        M__[col__][(idx__ + 1)][9][_mask_idx] = M__[col__][idx__][8][_mask_idx];
        M__[col__][(idx__ + 1)][10][_mask_idx] = M__[col__][idx__][9][_mask_idx];
        M__[col__][(idx__ + 1)][11][_mask_idx] = M__[col__][idx__][10][_mask_idx];
        M__[col__][(idx__ + 1)][12][_mask_idx] = M__[col__][idx__][11][_mask_idx];
        M__[col__][(idx__ + 1)][13][_mask_idx] = M__[col__][idx__][12][_mask_idx];
        M__[col__][(idx__ + 1)][14][_mask_idx] = M__[col__][idx__][13][_mask_idx];
        M__[col__][(idx__ + 1)][15][_mask_idx] = M__[col__][idx__][14][_mask_idx];
        M__[col__][(idx__ + 1)][16][_mask_idx] = M__[col__][idx__][15][_mask_idx];
        M__[col__][(idx__ + 1)][17][_mask_idx] = M__[col__][idx__][16][_mask_idx];
        M__[col__][(idx__ + 1)][18][_mask_idx] = M__[col__][idx__][17][_mask_idx];
        M__[col__][(idx__ + 1)][19][_mask_idx] = M__[col__][idx__][18][_mask_idx];
        M__[col__][(idx__ + 1)][20][_mask_idx] = M__[col__][idx__][19][_mask_idx];
        M__[col__][(idx__ + 1)][21][_mask_idx] = M__[col__][idx__][20][_mask_idx];
        M__[col__][(idx__ + 1)][22][_mask_idx] = M__[col__][idx__][21][_mask_idx];
        M__[col__][(idx__ + 1)][23][_mask_idx] = M__[col__][idx__][22][_mask_idx];
        M__[col__][(idx__ + 1)][24][_mask_idx] = M__[col__][idx__][23][_mask_idx];
        M__[col__][(idx__ + 1)][25][_mask_idx] = M__[col__][idx__][24][_mask_idx];
        M__[col__][(idx__ + 1)][26][_mask_idx] = M__[col__][idx__][25][_mask_idx];
        M__[col__][(idx__ + 1)][27][_mask_idx] = M__[col__][idx__][26][_mask_idx];
        M__[col__][(idx__ + 1)][28][_mask_idx] = M__[col__][idx__][27][_mask_idx];
        M__[col__][(idx__ + 1)][29][_mask_idx] = M__[col__][idx__][28][_mask_idx];
        M__[col__][(idx__ + 1)][30][_mask_idx] = M__[col__][idx__][29][_mask_idx];
        M__[col__][(idx__ + 1)][31][_mask_idx] = M__[col__][idx__][30][_mask_idx];
      }
    }
  }

}

/* main function */
void pyjamask__ (/*inputs*/ DATATYPE plaintext__[4][32][MASKING_ORDER],DATATYPE key__[15][128][MASKING_ORDER], /*outputs*/ DATATYPE ciphertext__[128][MASKING_ORDER]) {

  // Variables declaration
  DATATYPE _tmp134_[128][MASKING_ORDER];
  DATATYPE _tmp135_[4][32][MASKING_ORDER];
  DATATYPE round__[128][MASKING_ORDER];

  // Instructions (body)
  for (int _mask_idx = 0; _mask_idx <= (MASKING_ORDER - 1); _mask_idx++) {
    round__[0][_mask_idx] = plaintext__[0][0][_mask_idx];
    round__[1][_mask_idx] = plaintext__[0][1][_mask_idx];
    round__[2][_mask_idx] = plaintext__[0][2][_mask_idx];
    round__[3][_mask_idx] = plaintext__[0][3][_mask_idx];
    round__[4][_mask_idx] = plaintext__[0][4][_mask_idx];
    round__[5][_mask_idx] = plaintext__[0][5][_mask_idx];
    round__[6][_mask_idx] = plaintext__[0][6][_mask_idx];
    round__[7][_mask_idx] = plaintext__[0][7][_mask_idx];
    round__[8][_mask_idx] = plaintext__[0][8][_mask_idx];
    round__[9][_mask_idx] = plaintext__[0][9][_mask_idx];
    round__[10][_mask_idx] = plaintext__[0][10][_mask_idx];
    round__[11][_mask_idx] = plaintext__[0][11][_mask_idx];
    round__[12][_mask_idx] = plaintext__[0][12][_mask_idx];
    round__[13][_mask_idx] = plaintext__[0][13][_mask_idx];
    round__[14][_mask_idx] = plaintext__[0][14][_mask_idx];
    round__[15][_mask_idx] = plaintext__[0][15][_mask_idx];
    round__[16][_mask_idx] = plaintext__[0][16][_mask_idx];
    round__[17][_mask_idx] = plaintext__[0][17][_mask_idx];
    round__[18][_mask_idx] = plaintext__[0][18][_mask_idx];
    round__[19][_mask_idx] = plaintext__[0][19][_mask_idx];
    round__[20][_mask_idx] = plaintext__[0][20][_mask_idx];
    round__[21][_mask_idx] = plaintext__[0][21][_mask_idx];
    round__[22][_mask_idx] = plaintext__[0][22][_mask_idx];
    round__[23][_mask_idx] = plaintext__[0][23][_mask_idx];
    round__[24][_mask_idx] = plaintext__[0][24][_mask_idx];
    round__[25][_mask_idx] = plaintext__[0][25][_mask_idx];
    round__[26][_mask_idx] = plaintext__[0][26][_mask_idx];
    round__[27][_mask_idx] = plaintext__[0][27][_mask_idx];
    round__[28][_mask_idx] = plaintext__[0][28][_mask_idx];
    round__[29][_mask_idx] = plaintext__[0][29][_mask_idx];
    round__[30][_mask_idx] = plaintext__[0][30][_mask_idx];
    round__[31][_mask_idx] = plaintext__[0][31][_mask_idx];
    round__[32][_mask_idx] = plaintext__[1][0][_mask_idx];
    round__[33][_mask_idx] = plaintext__[1][1][_mask_idx];
    round__[34][_mask_idx] = plaintext__[1][2][_mask_idx];
    round__[35][_mask_idx] = plaintext__[1][3][_mask_idx];
    round__[36][_mask_idx] = plaintext__[1][4][_mask_idx];
    round__[37][_mask_idx] = plaintext__[1][5][_mask_idx];
    round__[38][_mask_idx] = plaintext__[1][6][_mask_idx];
    round__[39][_mask_idx] = plaintext__[1][7][_mask_idx];
    round__[40][_mask_idx] = plaintext__[1][8][_mask_idx];
    round__[41][_mask_idx] = plaintext__[1][9][_mask_idx];
    round__[42][_mask_idx] = plaintext__[1][10][_mask_idx];
    round__[43][_mask_idx] = plaintext__[1][11][_mask_idx];
    round__[44][_mask_idx] = plaintext__[1][12][_mask_idx];
    round__[45][_mask_idx] = plaintext__[1][13][_mask_idx];
    round__[46][_mask_idx] = plaintext__[1][14][_mask_idx];
    round__[47][_mask_idx] = plaintext__[1][15][_mask_idx];
    round__[48][_mask_idx] = plaintext__[1][16][_mask_idx];
    round__[49][_mask_idx] = plaintext__[1][17][_mask_idx];
    round__[50][_mask_idx] = plaintext__[1][18][_mask_idx];
    round__[51][_mask_idx] = plaintext__[1][19][_mask_idx];
    round__[52][_mask_idx] = plaintext__[1][20][_mask_idx];
    round__[53][_mask_idx] = plaintext__[1][21][_mask_idx];
    round__[54][_mask_idx] = plaintext__[1][22][_mask_idx];
    round__[55][_mask_idx] = plaintext__[1][23][_mask_idx];
    round__[56][_mask_idx] = plaintext__[1][24][_mask_idx];
    round__[57][_mask_idx] = plaintext__[1][25][_mask_idx];
    round__[58][_mask_idx] = plaintext__[1][26][_mask_idx];
    round__[59][_mask_idx] = plaintext__[1][27][_mask_idx];
    round__[60][_mask_idx] = plaintext__[1][28][_mask_idx];
    round__[61][_mask_idx] = plaintext__[1][29][_mask_idx];
    round__[62][_mask_idx] = plaintext__[1][30][_mask_idx];
    round__[63][_mask_idx] = plaintext__[1][31][_mask_idx];
    round__[64][_mask_idx] = plaintext__[2][0][_mask_idx];
    round__[65][_mask_idx] = plaintext__[2][1][_mask_idx];
    round__[66][_mask_idx] = plaintext__[2][2][_mask_idx];
    round__[67][_mask_idx] = plaintext__[2][3][_mask_idx];
    round__[68][_mask_idx] = plaintext__[2][4][_mask_idx];
    round__[69][_mask_idx] = plaintext__[2][5][_mask_idx];
    round__[70][_mask_idx] = plaintext__[2][6][_mask_idx];
    round__[71][_mask_idx] = plaintext__[2][7][_mask_idx];
    round__[72][_mask_idx] = plaintext__[2][8][_mask_idx];
    round__[73][_mask_idx] = plaintext__[2][9][_mask_idx];
    round__[74][_mask_idx] = plaintext__[2][10][_mask_idx];
    round__[75][_mask_idx] = plaintext__[2][11][_mask_idx];
    round__[76][_mask_idx] = plaintext__[2][12][_mask_idx];
    round__[77][_mask_idx] = plaintext__[2][13][_mask_idx];
    round__[78][_mask_idx] = plaintext__[2][14][_mask_idx];
    round__[79][_mask_idx] = plaintext__[2][15][_mask_idx];
    round__[80][_mask_idx] = plaintext__[2][16][_mask_idx];
    round__[81][_mask_idx] = plaintext__[2][17][_mask_idx];
    round__[82][_mask_idx] = plaintext__[2][18][_mask_idx];
    round__[83][_mask_idx] = plaintext__[2][19][_mask_idx];
    round__[84][_mask_idx] = plaintext__[2][20][_mask_idx];
    round__[85][_mask_idx] = plaintext__[2][21][_mask_idx];
    round__[86][_mask_idx] = plaintext__[2][22][_mask_idx];
    round__[87][_mask_idx] = plaintext__[2][23][_mask_idx];
    round__[88][_mask_idx] = plaintext__[2][24][_mask_idx];
    round__[89][_mask_idx] = plaintext__[2][25][_mask_idx];
    round__[90][_mask_idx] = plaintext__[2][26][_mask_idx];
    round__[91][_mask_idx] = plaintext__[2][27][_mask_idx];
    round__[92][_mask_idx] = plaintext__[2][28][_mask_idx];
    round__[93][_mask_idx] = plaintext__[2][29][_mask_idx];
    round__[94][_mask_idx] = plaintext__[2][30][_mask_idx];
    round__[95][_mask_idx] = plaintext__[2][31][_mask_idx];
    round__[96][_mask_idx] = plaintext__[3][0][_mask_idx];
    round__[97][_mask_idx] = plaintext__[3][1][_mask_idx];
    round__[98][_mask_idx] = plaintext__[3][2][_mask_idx];
    round__[99][_mask_idx] = plaintext__[3][3][_mask_idx];
    round__[100][_mask_idx] = plaintext__[3][4][_mask_idx];
    round__[101][_mask_idx] = plaintext__[3][5][_mask_idx];
    round__[102][_mask_idx] = plaintext__[3][6][_mask_idx];
    round__[103][_mask_idx] = plaintext__[3][7][_mask_idx];
    round__[104][_mask_idx] = plaintext__[3][8][_mask_idx];
    round__[105][_mask_idx] = plaintext__[3][9][_mask_idx];
    round__[106][_mask_idx] = plaintext__[3][10][_mask_idx];
    round__[107][_mask_idx] = plaintext__[3][11][_mask_idx];
    round__[108][_mask_idx] = plaintext__[3][12][_mask_idx];
    round__[109][_mask_idx] = plaintext__[3][13][_mask_idx];
    round__[110][_mask_idx] = plaintext__[3][14][_mask_idx];
    round__[111][_mask_idx] = plaintext__[3][15][_mask_idx];
    round__[112][_mask_idx] = plaintext__[3][16][_mask_idx];
    round__[113][_mask_idx] = plaintext__[3][17][_mask_idx];
    round__[114][_mask_idx] = plaintext__[3][18][_mask_idx];
    round__[115][_mask_idx] = plaintext__[3][19][_mask_idx];
    round__[116][_mask_idx] = plaintext__[3][20][_mask_idx];
    round__[117][_mask_idx] = plaintext__[3][21][_mask_idx];
    round__[118][_mask_idx] = plaintext__[3][22][_mask_idx];
    round__[119][_mask_idx] = plaintext__[3][23][_mask_idx];
    round__[120][_mask_idx] = plaintext__[3][24][_mask_idx];
    round__[121][_mask_idx] = plaintext__[3][25][_mask_idx];
    round__[122][_mask_idx] = plaintext__[3][26][_mask_idx];
    round__[123][_mask_idx] = plaintext__[3][27][_mask_idx];
    round__[124][_mask_idx] = plaintext__[3][28][_mask_idx];
    round__[125][_mask_idx] = plaintext__[3][29][_mask_idx];
    round__[126][_mask_idx] = plaintext__[3][30][_mask_idx];
    round__[127][_mask_idx] = plaintext__[3][31][_mask_idx];
  }
  for (int i__ = 0; i__ <= 13; i__++) {
    AddRoundKey__B1(round__,key__[i__],_tmp134_);
    SubBytesAll__B1(_tmp134_,_tmp135_);
    MixRows__B1(_tmp135_,round__);
  }
  AddRoundKey__B1(round__,key__[14],ciphertext__);

}

/* Additional functions */
uint32_t bench_speed() {
  /* inputs */
  DATATYPE plaintext__[4][32][MASKING_ORDER] = { 0 };
  DATATYPE key__[15][128][MASKING_ORDER] = { 0 };
  /* outputs */
  DATATYPE ciphertext__[128][MASKING_ORDER] = { 0 };
  /* fun call */
  pyjamask__(plaintext__, key__,ciphertext__);

  /* Returning the number of encrypted bytes */
  return 512;
}

/* **************************************************************** */
/*                            Usuba source                          */
/*                                                                  */
/*

 _no_inline table SubBytes(i :  b4 :: base)
  returns o :  b4 :: base
{
  2, 13, 3, 9, 7, 11, 10, 6, 14, 0, 15, 4, 8, 5, 1, 12
}


_no_inline node AddRoundKey(i :  b128 :: base,k :  b128 :: base)
  returns o :  b128 :: base
vars

let
  (o) = (i ^ k)
tel

_no_inline node SubBytesAll(input :  b32[4] :: base)
  returns output :  b32[4] :: base
vars

let
  forall i in [0,31] {
    (output[0 .. 3][i]) = SubBytes(input[0 .. 3][i])
  }
tel

 node col_mult(a :  b32 :: base,b : const b32 :: base)
  returns r :  b1 :: base
vars
  acc :  b32 :: base
let
  (acc[0]) = (a[0] & b[0]);
  forall i in [1,31] {
    (acc[i]) = (acc[(i - 1)] ^ (a[i] & b[i]))
  };
  (r) = acc[31]
tel

_no_inline node MixRows(input :  b32[4] :: base)
  returns output :  b32[4] :: base
vars
  M : const b32[4][33] :: base
let
  (M[0][0]) = (1,0,1,0,0,0,1,1,1,0,0,0,0,1,1,0,0,0,0,1,0,0,0,0,1,0,0,0,0,1,0,1);
  (M[1][0]) = (0,1,1,0,0,0,1,1,0,1,0,0,0,0,0,1,0,1,1,1,0,0,0,0,0,0,1,0,0,0,0,1);
  (M[2][0]) = (0,1,1,0,1,0,0,1,0,0,1,0,1,1,0,0,1,1,1,1,0,0,1,0,1,0,0,0,0,0,0,0);
  (M[3][0]) = (0,1,0,0,1,0,0,0,1,0,1,0,0,1,0,1,0,1,0,0,1,0,0,0,0,0,0,1,0,0,1,1);
  forall col in [0,3] {
    forall idx in [0,31] {
      (output[col][idx]) = col_mult(input[col],M[col][idx]);
      (M[col][(idx + 1)]) = (M[col][idx] >>> 1)
    }
  }
tel

 node pyjamask(plaintext :  b32[4] :: base,key :  b32[15][4] :: base)
  returns ciphertext :  b32[4] :: base
vars
  round :  b32[15][4] :: base
let
  (round[0]) = plaintext;
  forall i in [0,13] {
    (round[(i + 1)]) = MixRows(SubBytesAll(AddRoundKey(round[i],key[i])))
  };
  (ciphertext) = AddRoundKey(round[14],key[14])
tel

*/
 