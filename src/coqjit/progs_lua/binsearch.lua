    do
       -- Avoid heap allocs for performance
       local default_fcompval = function( value ) return value end
       local fcompf = function( a,b ) return a < b end
       local fcompr = function( a,b ) return a > b end
       function table.binsearch( tbl,value,fcompval,reversed )
          -- Initialise functions
          local fcompval = fcompval or default_fcompval
          local fcomp = reversed and fcompr or fcompf
          --  Initialise numbers
          local iStart,iEnd,iMid = 1,#tbl,0
          -- Binary Search
          while iStart <= iEnd do
             -- calculate middle
             iMid = (iStart+iEnd)/2
             -- get compare value
             local value2 = fcompval( tbl[iMid] )
             -- get all values that match
             if value == value2 then
                local tfound,num = { iMid,iMid },iMid - 1
                while value == fcompval( tbl[num] ) do -- ERROR: this may cause fail in fcompval if num is out of range and tbl[num] is nil
                   tfound[1],num = num,num - 1
                end
                num = iMid + 1
                while value == fcompval( tbl[num] ) do -- ERROR: this may cause fail in fcompval if num is out of range and tbl[num] is nil
                   tfound[2],num = num,num + 1
                end
                return tfound
             -- keep searching
             elseif fcomp( value,value2 ) then
                iEnd = iMid - 1
             else
                iStart = iMid + 1
             end
          end
       end
    end

    t = {}
    local v = table.binsearch(t, 5); assert(v == nil)
