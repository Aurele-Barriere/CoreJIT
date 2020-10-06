local a = 0
if true then
  a = 1
end
assert(a==1)
if false then
  a = 2
end
assert(a==1)
