---
---

local operators = require "logic.operators"

local logic = {}

local function child_needs_braces(what, child)
    local need_braces = true
    if logic.is_identifier(child) then
        need_braces = false
    end
    if logic.is_value(child) then
        need_braces = false
    end
    if logic.is_box(child) then
        need_braces = false
    end
    if logic.is_operator(child) and what.operator.precedence <= child.operator.precedence
            and what.operator.associative and child.operator.associative then
        need_braces = false
    end
    if logic.is_operator(child) and child.operator.associativity == "none" then
        need_braces = false
    end
    if logic.is_operator(child) and child.operator.arity == 1 then
        need_braces = false
    end
    return need_braces
end

local function standard_operator_to_string(what)
    local operator = what.operator
    local symbol = operator.default_symbol
    if not symbol then
        assert(operator.compute_symbol_string)
        symbol = operator:compute_symbol_string()
        assert(symbol)
    end
    local result = {}
    if operator.arity == 1 then
        local need_braces = child_needs_braces(what, what.children[1])
        if operator.notation == "prefix" then
            table.insert(result, symbol)
        end
        if need_braces then
            table.insert(result, "(")
        end
        table.insert(result, tostring(what.children[1]))
        if need_braces then
            table.insert(result, ")")
        end
        if operator.notation == "postfix" then
            table.insert(result, symbol)
        end
    elseif operator.arity == 2 then
        if operator.notation == "infix" then
            for _,child in ipairs(what.children) do
                local need_braces = child_needs_braces(what, child)
                if need_braces then
                    table.insert(result, "(")
                end
                table.insert(result, tostring(child))
                if need_braces then
                    table.insert(result, ")")
                end
                table.insert(result, symbol)
            end
            result[#result] = nil
        else
            error("not implemented")
        end
    else
        error("not implemented")
    end
    result = table.concat(result)
    return result
end


local function is_formula(object)
    if type(object) ~= "table" then
        return false
    end
    if not object.is_formula then
        return false
    end
    return true
end

function logic.is_identifier(object)
    if not is_formula(object) then
        return false
    end
    if object.type ~= "identifier" then
        return false
    end
    return true
end

function logic.is_box(object)
    if not is_formula(object) then
        return false
    end
    if object.type ~= "box" then
        return false
    end
    return true
end

function logic.is_value(object)
    if not is_formula(object) then
        return false
    end
    if object.type ~= "value" then
        return false
    end
    return true
end

function logic.is_operator(object)
    if not is_formula(object) then
        return false
    end
    if object.type ~= "operator" then
        return false
    end
    return true
end

function logic.make_identifier(name, positional)
    local result = {}
    result.type = "identifier"
    result.identifier = name
    result.is_formula = true
    result.positional = positional
    function result:get_type()
        return self.type
    end
    function result:get_identifier()
        return self.identifier
    end
    function result:get_positional()
        return self.positional
    end
    local meta = {}
    function meta.__tostring(what)
        return tostring(what.identifier)
    end
    function meta.__newindex(_)
        error()
    end
    setmetatable(result, meta)
    return result
end

-- A box ("□", entered as \box) is a placeholder leaf: it parses wherever
-- a formula, identifier or numeric operand is expected, so formulas can
-- be edited piecemeal through the tree view.  It is syntactically valid
-- but marks the formula incomplete; model checking rejects it.
function logic.make_box(positional)
    local result = {}
    result.type = "box"
    result.is_formula = true
    result.positional = positional
    function result:get_type()
        return self.type
    end
    -- identifier-list consumers (MAP query variables, IDP/INFL arguments)
    -- call get_identifier() on their children; the box reports its symbol
    -- so those lists stay well-formed while still being recognisably a box
    function result:get_identifier()
        return "□"
    end
    function result:get_positional()
        return self.positional
    end
    local meta = {}
    function meta.__tostring(_)
        return "□"
    end
    function meta.__newindex(_)
        error()
    end
    setmetatable(result, meta)
    return result
end

function logic.make_value(value, positional)
    local result = {}
    result.type = "value"
    result.value = value
    result.is_formula = true
    result.positional = positional
    function result:get_type()
        return self.type
    end
    function result:get_value()
        return self.value
    end
    function result:get_positional()
        return self.positional
    end
    local meta = {}
    function meta.__tostring(what)
        return tostring(what.value)
    end
    function meta.__newindex(_)
        error()
    end
    setmetatable(result, meta)
    return result
end

function logic.make_operator(children, operator, positional)
    assert(type(children) == "table")
    for _,child in ipairs(children) do
        assert(child)
        assert(is_formula(child))
    end
    assert(operators.is_operator(operator))
    assert(operator.arity == #children)
    local result = {}
    result.is_formula = true
    result.children = {}
    result.type = "operator"
    result.positional = positional
    for _,child in ipairs(children) do
        table.insert(result.children, child)
    end
    result.operator = operator
    function result:get_type()
        return self.type
    end
    function result:get_operator()
        return self.operator
    end
    function result:get_operator_name()
        return self:get_operator().name
    end
    function result:get_num_children()
        return #self.children
    end
    function result:get_child(number)
        assert(type(number) == "number")
        assert(self.children[number])
        return self.children[number]
    end
    function result:get_children()
        return self.children
    end
    function result:get_child_or_nil(number)
        assert(type(number) == "number")
        return self.children[number]
    end
    function result:get_positional()
        return self.positional
    end
    local meta = {}
    if operator.tostring then
        meta.__tostring = operator.tostring
    else
        meta.__tostring = standard_operator_to_string
    end
    function meta.__newindex(_)
        error()
    end
    setmetatable(result, meta)
    return result
end

function logic.make_nullary_operator(operator, positional)
    return logic.make_operator({}, operator, positional)
end

function logic.make_unary_operator(inner, operator, positional)
    assert(is_formula(inner))
    return logic.make_operator({inner}, operator, positional)
end

function logic.make_binary_operator(left, right, operator, positional)
    assert(is_formula(left), left)
    assert(is_formula(right), right)
    operators.is_operator(operator)
    return logic.make_operator({left, right}, operator, positional)
end

return logic
