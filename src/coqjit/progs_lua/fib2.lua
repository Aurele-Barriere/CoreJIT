local function fib(n)
  __hint_int(n)
  if n < 2 then
    return n
  end
  return fib(n-1) + fib(n-2)
end

return fib(39)
