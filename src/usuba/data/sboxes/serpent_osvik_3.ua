_no_opt node s3 (r0:v1,r1:v1,r2:v1,r3:v1) returns (r5:v1,r6:v1,r7:v1,r8:v1)
vars
    r4 : v1
let
  r4 = r0;
  r0 |:= r3;
  r3 ^:= r1;
  r1 &:= r4;
  r4 ^:= r2;
  r2 ^:= r3;
  r3 &:= r0;
  r4 |:= r1;
  r3 ^:= r4;
  r0 ^:= r1;
  r4 &:= r0;
  r1 ^:= r3;
  r4 ^:= r2;
  r1 |:= r0;
  r1 ^:= r2;
  r0 ^:= r3;
  r2 := r1;
  r1 |:= r3;
  r1 ^:= r0;
  r5 = r1;
  r6 = r2;
  r7 = r3;
  r8 = r4
tel