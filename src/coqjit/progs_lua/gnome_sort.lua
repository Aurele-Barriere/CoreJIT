local function gnomeSort(a)
    local i, j = 2, 3
    __hint_tbl(a)
    while i <= #a do
        local l, r = a[i-1], a[i]
        local le

        __hint_int(l)
        __hint_int(r)

        if       l == nil   then   le = true
        elseif   r == nil   then   le = false
        elseif   l == false then   le = true
        elseif   r == false then   le = false
        elseif   l == true  then   le = true
        elseif   r == true  then   le = false
        else                       le = l <= r
        end

        if le then
            i = j
            j = j + 1
        else
            a[i-1], a[i] = r,l -- swap
            i = i - 1
            if i == 1 then -- 1 instead of 0
                i = j
                j = j + 1
            end
        end
    end
end

list_in = {5,6,2,9,14,2,15,7,8,97,5,6,1,2,9,14,2,15,6,7,8,97,5,6,1,2,9,14,2,15,6,7,8,97,5,6,1,2,9,14,2,15,6,7,8,97}
list = {0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0}

iter = 150
iter2 = 20000

local function test()
  for i = 1, #list_in do
    list[i] = list_in[i]
  end
  for i = 1, iter do
    gnomeSort(list)
    i = i+1
  end
end

for i = 1, iter2 do
  test()
end

local i = 1
while i < #list do
  assert(list[i]<=list[i+1])
  i = i+1
end
