local function bubbleSort(A)
  __hint_tbl(A)
  local itemCount=#A
  local hasChanged
  repeat
    hasChanged = false
    itemCount=itemCount - 1
    for i = 1, itemCount do
      local l,r = A[i],A[i+1]
      __hint_int(l)
      __hint_int(r)
      if l > r then
        A[i], A[i + 1] = r,l
        hasChanged = true
      end
    end
  until hasChanged == false
end


list_in = {5,6,1,2,9,14,2,15,97,5,6,1,2,9,14,2,15,6,7,8,97,5,6,1,2,9,14,2,15,6,7,8,97}
list = {0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,}

iter = 500
iter2 = 1000

local function test()
  for i = 1, #list_in do
    list[i] = list_in[i]
  end
  for i = 1, iter do
    bubbleSort(list)
    i = i+1
  end
end

for i = 1, iter2 do
  test()
end

local i = 1
while i <= #list do
  print(list[i])
  i = i+1
end

