local f = function(a)
  __hint_int(a)
  return 1+a
end
f(1)
f(1)
f(1)
f(1)


local f2 = function(a)
  __hint_val(a,2)
  return 1+a
end
f2(2)
f2(2)
f2(2)
f2(2)
