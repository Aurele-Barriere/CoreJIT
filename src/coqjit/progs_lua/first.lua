local v = 0;
v = v+1+0;
assert(v~=2)
assert(v~=true)
local r = assert(v==1);

assert(nil == nil)

assert ((nil and nil) == nil)
assert ((false and 13) == false)
assert ((true and 13) == 13)
assert ((true and nil) == nil)
assert ((true and false) == false)
assert ((true and true) == true)
assert ((1 and 1) == 1)
assert ((0 and 1) == 1)
assert ((1 and true) == true)
assert ((1 and nil) == nil)

assert ((nil or nil) == nil)
assert ((nil or true) == true)
assert ((nil or false) == false)
assert ((nil or 1) == 1)
assert ((nil or 0) == 0)
assert ((false or 13) == 13)
assert ((true or 13) == true)
assert ((1 or 1) == 1)
assert ((0 or 1) == 0)
assert ((12 or true) == 12)
assert ((12 or nil) == 12)

a = 1
assert ((-a) == -1)
a = true
assert ((~a) == false)
a = false
assert ((~a) == true)
a = 1
assert ((~a) == false)
a = nil
assert ((~a) == true)
