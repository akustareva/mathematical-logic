class Expression:
    def __init__(self, name="expression", op=None, args=None):
        self.__name = name
        self.__operation = op
        self.__args = args

    def get_type(self):
        return str(self.__name)

    def get_operation(self):
        return self.__operation

    def get_args(self):
        return self.__args


class UnaryOperations(Expression):
    def __init__(self, arg: Expression, op: str):
        Expression.__init__(self, "unary_expression", op, tuple([arg]))
        self.__operation = op
        self.__argument = arg
        self.__hash = hash((self.__argument, self.__operation))

    def __str__(self):
        return str(self.__operation) + "(" + str(self.__argument) + ")"

    def __eq__(self, other: Expression):
        if self.__operation == other.get_operation() and [self.__argument] == list(other.get_args()) \
                and self.__hash__() == other.__hash__():
            return True
        return False

    def __hash__(self):
        return self.__hash

    def get_arg(self):
        return self.__argument


class BinaryOperations(Expression):
    def __init__(self, first: Expression, second: Expression, op: str):
        Expression.__init__(self, "binary_expression", op, (first, second))
        self.__operation = op
        self.__first = first
        self.__second = second
        self.__hash = hash((self.__first, self.__second, self.__operation))

    def __str__(self):
        return "((" + str(self.__first) + ")" + str(self.__operation) + "(" + str(self.__second) + "))"

    def __eq__(self, other: Expression):
        if self.__operation == other.get_operation() and (self.__first, self.__second) == other.get_args() \
                and self.__hash__() == other.__hash__():
            return True
        return False

    def __hash__(self):
        return self.__hash

    def get_first_arg(self):
        return self.__first

    def get_second_arg(self):
        return self.__second


class Increment(UnaryOperations):
    def __init__(self, arg: Expression):
        super(Increment, self).__init__(arg, "'")

    def __str__(self):
        if isinstance(self.get_arg(), Increment):
            return str(self.get_arg()) + "'"
        else:
            return "(" + str(self.get_arg()) + ")'"


class Negation(UnaryOperations):
    def __init__(self, arg: Expression):
        super(Negation, self).__init__(arg, "!")


class Disjunction(BinaryOperations):
    def __init__(self, first: Expression, second: Expression):
        super(Disjunction, self).__init__(first, second, "|")


class Conjunction(BinaryOperations):
    def __init__(self, first: Expression, second: Expression):
        super(Conjunction, self).__init__(first, second, "&")


class Implication(BinaryOperations):
    def __init__(self, first: Expression, second: Expression):
        super(Implication, self).__init__(first, second, "->")


class Addition(BinaryOperations):
    def __init__(self, first: Expression, second: Expression):
        super(Addition, self).__init__(first, second, "+")


class Multiply(BinaryOperations):
    def __init__(self, first: Expression, second: Expression):
        super(Multiply, self).__init__(first, second, "*")


class EqPredicate(Expression):
    def __init__(self, first: Expression, second: Expression):
        Expression.__init__(self, "equal_predicate", "=", (first, second))
        self.__first = first
        self.__second = second
        self.__hash = hash((self.__first, self.__second, "="))

    def __str__(self):
        return "((" + str(self.__first) + ")=(" + str(self.__second) + "))"

    def __eq__(self, other: Expression):
        if (self.__first, self.__second) == other.get_args() and self.__hash__() == other.__hash__():
            return True
        return False

    def __hash__(self):
        return self.__hash

    def get_first_arg(self):
        return self.__first

    def get_second_arg(self):
        return self.__second


class Predicate(Expression):
    def __init__(self, name: str, args: tuple):
        Expression.__init__(self, "predicate", name, args)
        self.__name = name
        self.__args = args
        self.__hash = hash((self.__args, self.__name))

    def __str__(self):
        res = ""
        if len(self.__args) > 0:
            for s in self.__args:
                res += str(s) + ","
            res = "(" + res[:-1] + ")"
            return "(" + str(self.__name) + res + ")"
        return str(self.__name)

    def __eq__(self, other: Expression):
        if self.__name == other.get_operation() and self.__args == other.get_args() \
                and self.__hash__() == other.__hash__():
            return True
        return False

    def __hash__(self):
        return self.__hash

    def get_name(self):
        return self.__name


class Variable(Expression):
    def __init__(self, name: str):
        Expression.__init__(self, "variable", op=name)
        self.__name = name
        self.__hash = hash(self.__name)

    def __str__(self):
        return str(self.__name)

    def __eq__(self, other: Expression):
        if self.__name == other.get_operation() and self.__hash__() == other.__hash__():
            return True
        return False

    def __hash__(self):
        return self.__hash

    def get_name(self):
        return self.__name


class Function(Expression):
    def __init__(self, name: str, args: tuple):
        Expression.__init__(self, "function", name, args)
        self.__name = name
        self.__args = args
        self.__hash = hash((self.__args, self.__name))

    def __str__(self):
        res = ""
        for s in self.__args:
            res += str(s) + ","
        return "(" + str(self.__name) + "(" + res[:-1] + "))"

    def __eq__(self, other: Expression):
        if self.__name == other.get_operation() and self.__args == other.get_args() \
                and self.__hash__() == other.__hash__():
            return True
        return False

    def __hash__(self):
        return self.__hash

    def get_name(self):
        return self.__name


class Quantifier(Expression):
    def __init__(self, name: str, var: Variable, expr: Expression):
        Expression.__init__(self, "quantifier", str(name + str(var)), tuple([expr]))
        self.__name = name
        self.__variable = var
        self.__expression = expr
        self.__hash = hash((self.__name, self.__variable, self.__expression))

    def __str__(self):
        return "(" + str(self.__name) + str(self.__variable) + "(" + str(self.__expression) + "))"

    def __eq__(self, other: Expression):
        if str(self.__name + str(self.__variable)) == other.get_operation() \
                and self.get_args() == other.get_args() and self.__hash__() == other.__hash__():
            return True
        return False

    def __hash__(self):
        return self.__hash

    def get_name(self):
        return self.__name

    def get_variable(self):
        return self.__variable

    def get_expression(self):
        return self.__expression


class ExQuantifier(Quantifier):
    def __init__(self, var: Variable, exp: Expression):
        super(ExQuantifier, self).__init__("?", var, exp)


class UnQuantifier(Quantifier):
    def __init__(self, var: Variable, exp: Expression):
        super(UnQuantifier, self).__init__("@", var, exp)
