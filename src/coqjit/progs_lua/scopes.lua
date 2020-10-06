a=nil
print(a);
b = 1;
local f = function()
  b = 13
  local f2 = function()
    x = 10
    b = 42
  end
  local x = 9;
  print(b)
  f2()
  print(x)
  print(b)
end
r = f()
print(b)
print(r)

local sub = function(a,b)
  return a-b
end
print(sub(1234,34))
