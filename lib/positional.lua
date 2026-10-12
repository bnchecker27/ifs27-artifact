---
---

local util = require "lib.util"


local spaces = {[" "]=true, ["\n"]=true, ["\t"]=true}

local function make_positional(input, from, to)
    local result = {}
    while from and from <= #input and spaces[input:sub(from, from)] do
        from = from + 1
    end
    while to and to >= 1 and spaces[input:sub(to, to)] do
        to = to - 1
    end
    result.input = input
    result.from = from
    result.to = to
    result.text = input:sub(from, to)
    function result:get_input()
        return self.input
    end
    function result:get_from()
        return self.from
    end
    function result:get_to()
        return self.to
    end
    function result:get_from_line_column()
        if self.from then
            return util.index_to_line_and_column(self.input, self.from)
        else
            return nil, nil
        end
    end
    function result:get_to_line_column()
        if self.to then
            return util.index_to_line_and_column(self.input, self.to)
        else
            return nil, nil
        end
    end
    return result
end

return make_positional
