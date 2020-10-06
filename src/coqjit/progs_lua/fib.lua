-- Naive recursive
local function fibonacci_naive(n)
  local function inner(m)
    if m < 2 then
      return m
    end
    return inner(m-1) + inner(m-2)
  end
  return inner(n)
end

-- Tail-optimized recursive
local function fibonacci_tail_call(n)
  local function inner(m, a, b)
    if m == 0 then
      return a
    end
    return inner(m-1, b, a+b)
  end
  return inner(n, 0, 1)
end

local val = 16

local res1 = fibonacci_naive(val)
local res2 = fibonacci_tail_call(val)

assert(res1 == res2)

memo = {nil,nil,nil,nil,nil,nil,nil,nil,nil,nil,nil,nil,nil,nil,nil,nil,nil,nil,nil,nil,nil,nil,nil,nil,nil,nil,nil,nil,nil,nil,nil,nil,nil,nil,nil,nil,nil,nil,nil,nil,nil,nil,nil,nil,nil,nil,nil,nil,nil,nil,nil,nil,nil,nil,nil,nil,nil,nil,nil,nil,nil,nil,nil,nil,nil,nil,nil,nil,nil,nil}
local function fibonacci_memoized(n)
  local function inner(m)
    if m < 2 then
      return m
    end

    if memo[m] then
      return memo[m]
    else
      local res = inner(m-1) + inner(m-2)
      memo[m] = res
      return res
    end
  end
  return inner(n)
end

res3 = fibonacci_memoized(val)
assert(res1 == res3)


local function fibonacci_iterative(n)
  local a, b = 0, 1
  local i = 1

  while i <= n do
    a, b, i = b, a + b, i + 1
  end
  return a
end

res4 = fibonacci_iterative(val)
assert(res1 == res4)
res4 = fibonacci_iterative(val)
assert(res1 == res4)
res4 = fibonacci_iterative(val)
assert(res1 == res4)
res4 = fibonacci_iterative(val)
assert(res1 == res4)

print(res1)
return res1
