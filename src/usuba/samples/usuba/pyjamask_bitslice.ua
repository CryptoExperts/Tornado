# We use a different source for pyjamask bitslice and vslice because
# col_mult in Vslicing uses an arithmetic shift to convert a bit into
# a register full of this bit. This is not doable, nor needed in
# bitslicing.

_no_inline table SubBytes (i:b4) returns (o:b4) {
  0x2, 0xd, 0x3, 0x9, 0x7, 0xb, 0xa, 0x6, 0xe, 0x0, 0xf, 0x4, 0x8, 0x5, 0x1, 0xc
}

_no_inline node AddRoundKey (i,k:b128) returns (o:b128)
let
    o = i ^ k
tel

_no_inline node SubBytesAll (input:b32[4]) returns (output:b32[4])
let
    forall i in [0, 31] {
       output[0..3][i] = SubBytes(input[0..3][i])
    }
tel

node col_mult (a:b32,b:const b32) returns (r:b1)
vars
    acc:b32
let
    acc[0] = a[0] & b[0];
    forall i in [1,31] {
        acc[i] = acc[i-1] ^ (a[i] & b[i])
    }
    r = acc[31]
tel

_no_inline node MixRows (input:b32[4]) returns (output:b32[4])
vars
    M: const b32[4][33]
let
    # Manually unrolling the loop over M so that M can be partially linearized away...
    M[0][0] = (1,0,1,0,0,0,1,1,1,0,0,0,0,1,1,0,0,0,0,1,0,0,0,0,1,0,0,0,0,1,0,1);
    forall idx in [0,31] {
        output[0][idx] = col_mult(input[0], M[0][idx]);
        M[0][idx+1] = M[0][idx] >>> 1
    }
    M[1][0] = (0,1,1,0,0,0,1,1,0,1,0,0,0,0,0,1,0,1,1,1,0,0,0,0,0,0,1,0,0,0,0,1);
    forall idx in [0,31] {
        output[1][idx] = col_mult(input[1], M[1][idx]);
        M[1][idx+1] = M[1][idx] >>> 1
    }
    M[2][0] = (0,1,1,0,1,0,0,1,0,0,1,0,1,1,0,0,1,1,1,1,0,0,1,0,1,0,0,0,0,0,0,0);
    forall idx in [0,31] {
        output[2][idx] = col_mult(input[2], M[2][idx]);
        M[2][idx+1] = M[2][idx] >>> 1
    }
    M[3][0] = (0,1,0,0,1,0,0,0,1,0,1,0,0,1,0,1,0,1,0,0,1,0,0,0,0,0,0,1,0,0,1,1);
    forall idx in [0,31] {
        output[3][idx] = col_mult(input[3], M[3][idx]);
        M[3][idx+1] = M[3][idx] >>> 1
    }
tel

node pyjamask (plaintext:b32[4], key:b32[15][4]) returns (ciphertext:b32[4])
vars
    round: b32[15][4]
let
    round[0] = plaintext;
    forall i in [0, 13] {
        round[i+1] = MixRows(SubBytesAll(AddRoundKey(round[i], key[i])))
    }
    ciphertext = AddRoundKey(round[14], key[14])
tel
