a = {1,2,3}

local test = function(x)
  assert(a[-1]==nil)
  assert(a[0]==nil)
  assert(a[1]==1)
  assert(a[2]==x)
  assert(a[3]==3)
  assert(a[4]==nil)
  assert(a[5]==nil)
  assert(a[6]==nil)
  assert(a[7]==nil)
end

local write = function(x)
  for i=1,1 do
    a[2] = x
  end
end

test(2)
test(2)
a[2] = 42
test(42)
a[2] = a
test(a)

write(12)
test(12)
