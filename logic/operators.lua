---
---

local operators = {}

function operators.is_operator(object)
    if type(object) ~= "table" then
        return false
    end
    if not object.is_operator then
        return false
    end
    return true
end

local function write_protect(object)
    local meta = getmetatable(object)
    if not meta then
        meta = {}
        setmetatable(object, meta)
    end
    function meta.__newindex()
        error("protected")
    end
end

local function protect_list(list)
    for _,object in ipairs(list) do
        write_protect(object)
    end
end

operators.logical_operators = {
    {
        is_operator=true,
        name="not",
        sep_kind="psep",
        rhs_slot="bool",
        symbols={"¬", "!"},
        default_symbol="¬",
        arity=1,
        precedence=5,
        notation="prefix",
        operand_suppress={"varterm"},
        left_needs="bool"
    },
    {
        is_operator=true,
        name="and",
        sep_kind="sep",
        rhs_slot="bool",
        symbols={"∧", "&&"},
        default_symbol="∧",
        associativity="right",
        associative=true,
        arity=2,
        precedence=4,
        notation="infix",
        operand_suppress={"varterm"},
        left_needs="bool"
    },
    {
        is_operator=true,
        name="nand",
        sep_kind="sep",
        rhs_slot="bool",
        symbols={"↑"},
        default_symbol="↑",
        associativity="right",
        associative=true,
        arity=2,
        precedence=4,
        notation="infix",
        operand_suppress={"varterm"},
        left_needs="bool"
    },
    {
        is_operator=true,
        name="or",
        sep_kind="sep",
        rhs_slot="bool",
        symbols={"∨", "||"},
        default_symbol="∨",
        associativity="right",
        associative=true,
        arity=2,
        precedence=3,
        notation="infix",
        operand_suppress={"varterm"},
        left_needs="bool"
    },
    {
        is_operator=true,
        name="nor",
        sep_kind="sep",
        rhs_slot="bool",
        symbols={"↓"},
        default_symbol="↓",
        associativity="right",
        associative=true,
        arity=2,
        precedence=3,
        notation="infix",
        operand_suppress={"varterm"},
        left_needs="bool"
    },
    {
        is_operator=true,
        name="implication",
        sep_kind="sep",
        rhs_slot="bool",
        symbols={"→", "->"},
        default_symbol="→",
        associativity="right",
        associative=false,
        arity=2,
        precedence=2,
        notation="infix",
        operand_suppress={"varterm"},
        left_needs="bool"
    },
    {
        is_operator=true,
        name="biimplication",
        sep_kind="sep",
        rhs_slot="bool",
        symbols={"↔", "<->"},
        default_symbol="↔",
        associativity="right",
        associative=false,
        arity=2,
        precedence=1,
        notation="infix",
        operand_suppress={"varterm"},
        left_needs="bool"
    },
    {
        is_operator=true,
        name="xor",
        sep_kind="sep",
        rhs_slot="bool",
        symbols={"⊕"},
        default_symbol="⊕",
        associativity="right",
        associative=false,
        arity=2,
        precedence=1,
        notation="infix",
        operand_suppress={"varterm"},
        left_needs="bool"
    },

    --    {
    --      is_operator=true,
    --    name="prob",
    --   arity=1,
    --    precedence=8,
    -- },

}

protect_list(operators.logical_operators)

operators.arithmetic_operators = {
    {
        is_operator = true,
        name = "times",
        left_needs="numeric",
        sep_kind = "csep",
        csep_cls = "arith",
        rhs_slot = "arith",
        symbols = { "*", "×" },
        default_symbol = "×",
        arity = 2,
        precedence = 11,
        notation = "infix",
        associativity = "left",
        associative = true
    },
    {
        is_operator = true,
        name = "minus",
        left_needs="numeric",
        sep_kind = "csep",
        csep_cls = "arith",
        rhs_slot = "arith",
        symbols = { "-", "−" },
        default_symbol = "−",
        arity = 2,
        precedence = 10,
        notation = "infix",
        associativity = "left",
        associative = false
    },
    -- "+" and "÷" were gated behind the "arith" feature while "−"/"×"
    -- were built-in — an asymmetry with no syntactic reason (no unary
    -- "+", no "/" collision), so all four scalar operators are builtin
    {
        is_operator = true,
        name = "plus",
        left_needs="numeric",
        sep_kind = "csep",
        csep_cls = "arith",
        rhs_slot = "arith",
        symbols = { "+" },
        default_symbol = "+",
        arity = 2,
        precedence = 10,
        notation = "infix",
        associativity = "left",
        associative = true
    },
    {
        is_operator = true,
        name = "divide",
        left_needs="numeric",
        sep_kind = "csep",
        csep_cls = "arith",
        rhs_slot = "arith",
        symbols = { "÷", "/" },
        default_symbol = "÷",
        arity = 2,
        precedence = 11,
        notation = "infix",
        associativity = "left",
        associative = false
    }

}

protect_list(operators.arithmetic_operators)

-- kept as an empty alias: the "arith" feature flag still parses (older
-- command lines and ?features= links name it) and numvar's grammar
-- appends this list — everything it gated is builtin now
operators.extra_arithmetic_operators = {}

protect_list(operators.extra_arithmetic_operators)

operators.modify_probability = {
    {
        is_operator=true,
        name="modify_probability",
        left_needs="intervenable",
        arity=1,
        precedence=12,
        notation="postfix",
        suggest_symbol="["
    },
}

protect_list(operators.modify_probability)

-- "term | claim": the conditional operator.  Tighter than the Boolean
-- connectives (a && b | c = a && (b|c)) but looser than negation and the
-- atom-level comparisons, so "X | B = x" reads "X | (B = x)" — the
-- condition claim captures the comparison.  Only added to the grammar
-- when the "cond" feature is enabled.
operators.conditional_operators = {
    {
        is_operator=true,
        name="conditional",
        left_needs="termish",
        sep_kind="pbar",
        rhs_slot="bool",
        rhs_in_cond=true,
        symbols={"|"},
        default_symbol="|",
        arity=2,
        precedence=4.5,
        notation="infix",
        associativity="left",
        associative=false,
    },
}

protect_list(operators.conditional_operators)

operators.compare_operators = {
    {
        is_operator=true,
        name="less",
        left_needs="term",
        sep_kind="csep",
        csep_cls="cmp",
        rhs_slot="compare",
        symbols={"<"},
        default_symbol="<",
        arity=2,
        precedence=6,
        notation="infix",
        associativity="none",
        associative=false,
    },
    {
        is_operator=true,
        name="less_or_equal",
        left_needs="term",
        sep_kind="csep",
        csep_cls="cmp",
        rhs_slot="compare",
        symbols={"≤", "<="},
        default_symbol="≤",
        arity=2,
        precedence=6,
        notation="infix",
        associativity="none",
        associative=false,
    },
    {
        is_operator=true,
        name="equal",
        left_needs="term",
        sep_kind="csep",
        csep_cls="cmp",
        rhs_slot="compare",
        symbols={"="},
        default_symbol="=",
        arity=2,
        precedence=6,
        notation="infix",
        associativity="none",
        associative=false,
    },
    {
        is_operator=true,
        name="greater_or_equal",
        left_needs="term",
        sep_kind="csep",
        csep_cls="cmp",
        rhs_slot="compare",
        symbols={"≥", ">="},
        default_symbol="≥",
        arity=2,
        precedence=6,
        notation="infix",
        associativity="none",
        associative=false,
    },
    {
        is_operator=true,
        name="greater",
        left_needs="term",
        sep_kind="csep",
        csep_cls="cmp",
        rhs_slot="compare",
        symbols={">"},
        default_symbol=">",
        arity=2,
        precedence=6,
        notation="infix",
        associativity="none",
        associative=false,
    },
}

protect_list(operators.compare_operators)

function operators.make_symbol_to_operator_map(ops)
    assert(type(ops) == "table")
    local result = {}
    for _,op in ipairs(ops) do
        if op.symbols then
            for _,symbol in ipairs(op.symbols) do
                result[symbol] = op
            end
        end
    end
    return result
end

function operators.make_name_to_operator_map(ops)
    assert(type(ops) == "table")
    local result = {}
    for _,op in ipairs(ops) do
        result[op.name] = op
    end
    return result
end

return operators
