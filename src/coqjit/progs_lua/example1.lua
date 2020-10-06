local function apply(a,b)
  __hint_int(a)
  __hint_val(b,1)
  return (a*a)+b
end

apply(1,1)
apply(2,1)
apply(3,1)
apply(4,1)
apply(5,1)
