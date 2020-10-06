local f = function(a)
  local x = a+1
  __hint_int(a)
  return 0
end
t = 1
f(t)
f(t)
f(t)
f(t)
