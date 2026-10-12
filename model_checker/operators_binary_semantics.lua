---
---
local result = {
    ["not"] = function(operand)
        return not operand
    end,
    ["and"] = function(op1, op2)
        return op1 and op2
    end,
    ["nand"] = function(op1, op2)
        return not (op1 and op2)
    end,
    ["or"] = function(op1, op2)
        return op1 or op2
    end,
    ["nor"] = function(op1, op2)
        return not (op1 or op2)
    end,
    ["implication"] = function(op1, op2)
        return not op1 or op2
    end,
    ["biimplication"] = function(op1, op2)
        return op1 == op2
    end,
    ["xor"] = function(op1, op2)
        return op1 ~= op2
    end
}

return result
