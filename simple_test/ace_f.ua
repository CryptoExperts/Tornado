# This function is the |f| function from the ACE cipher. In n-slicing,
# it requires a refresh, which Tornado automatically inserts.

node f(x:u32) returns (y:u32)
let
    y = ((x <<< 5) & x) ^ (x <<< 1)
tel