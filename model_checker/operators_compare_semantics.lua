---
---
local result = {
    ["less"] = function(op1, op2)
        return op1 < op2
    end,
    ["less_or_equal"] = function(op1, op2)
        return op1 <= op2
    end,
    ["equal"] = function(op1, op2)
        return op1 == op2
    end,
    ["greater_or_equal"] = function(op1, op2)
        return op1 >= op2
    end,
    ["greater"] = function(op1, op2)
        return op1 > op2
    end
}

return result
