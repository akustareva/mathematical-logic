from entities import *


class ParsingError(Exception):
    def __init__(self, value: str):
        super(ParsingError, self).__init__("parse_error")
        self.value = value


class ClassicalParser:
    import re

    def __init__(self):
        self.__expression = ""
        self.__index = 0

    def parse_expression(self, expr: str):
        self.__expression = expr
        self.__index = 0
        return self.__parse_priority_zero()

    def __parse_priority_zero(self):  # implication
        first = self.__parse_priority_first()
        if self.__index < len(self.__expression) and self.__expression[self.__index] == "-":
            self.__index += 2
            return Implication(first, self.__parse_priority_zero())
        return first

    def __parse_priority_first(self):  # disjunction
        first = self.__parse_priority_second()
        while self.__index < len(self.__expression) and self.__expression[self.__index] == "|":
            self.__index += 1
            first = Disjunction(first, self.__parse_priority_third())
        return first

    def __parse_priority_second(self):  # conjunction
        first = self.__parse_priority_third()
        while self.__index < len(self.__expression) and self.__expression[self.__index] == "&":
            self.__index += 1
            first = Conjunction(first, self.__parse_priority_third())
        return first

    __is_var = re.compile('[A-Z]+[0-9]*')

    def __parse_priority_third(self):  # negation
        res = self.__is_var.match(self.__expression, self.__index)
        if res is not None:
            self.__index = res.end()
            return Variable(res.group())
        elif self.__expression[self.__index] == "!":
            self.__index += 1
            return Negation(self.__parse_priority_third())
        else:
            self.__index += 1
            answer = self.__parse_priority_zero()
            self.__index += 1
            return answer


class FormalParser:
    import re

    def __init__(self):
        self.__expression = ""
        self.__index = 0

    def parse_expression(self, expr: str):
        self.__expression = expr
        self.__index = 0
        return self.__parse_priority_zero()

    def parse_part_of_expression(self, expr: str, ind: int):
        self.__expression = expr
        self.__index = ind
        return self.__parse_priority_zero(), self.__index

    def __parse_priority_zero(self):  # implication
        first = self.__parse_priority_first()
        if self.__index < len(self.__expression) and self.__expression[self.__index] == "-":
            self.__index += 2
            return Implication(first, self.__parse_priority_zero())
        else:
            return first

    def __parse_priority_first(self):  # disjunction
        first = self.__parse_priority_second()
        while self.__index < len(self.__expression) and self.__expression[self.__index] == "|":
            self.__index += 1
            first = Disjunction(first, self.__parse_priority_second())
        return first

    def __parse_priority_second(self):  # conjunction
        first = self.__parse_priority_third()
        while self.__index < len(self.__expression) and self.__expression[self.__index] == "&":
            self.__index += 1
            first = Conjunction(first, self.__parse_priority_third())
        return first

    __is_var = re.compile('[a-z][0-9]*')

    def __parse_priority_third(self):  # unary operations
        if self.__expression[self.__index] == "!":  # negation
            self.__index += 1
            return Negation(self.__parse_priority_third())
        tmp_index = self.__index
        try:                                    # predicate
            return self.__try_parse_predicate()
        except ParsingError:
            self.__index = tmp_index
        if self.__expression[self.__index] == "(":
            self.__index += 1
            result = self.__parse_priority_zero()
            self.__index += 1
            return result
        if self.__expression[self.__index] == "?" or self.__expression[self.__index] == "@":    # quantifier
            q = self.__expression[self.__index]
            self.__index += 1
            res = self.__is_var.match(self.__expression, self.__index)
            self.__index = res.end()
            if q == "?":
                return ExQuantifier(Variable(res.group()), self.__parse_priority_third())
            else:
                return UnQuantifier(Variable(res.group()), self.__parse_priority_third())

    __is_predicate = re.compile('[A-Z][0-9]*')

    def __try_parse_predicate(self):
        res = self.__is_predicate.match(self.__expression, self.__index)
        if res is not None:                   # P(a, b, ...)
            var = res.group()
            self.__index = res.end()
            args = tuple()
            if self.__index < len(self.__expression) and self.__expression[self.__index] == "(":
                self.__index += 1
                args = self.__try_parse_args()
                if self.__expression[self.__index] != ")":
                    raise ParsingError("try_parse_predicate")
                else:
                    self.__index += 1
            return Predicate(var, args)
        else:                                   # term = term
            first = self.__try_parse_term()
            if self.__expression[self.__index] != "=":
                raise ParsingError("try_parse_predicate")
            else:
                self.__index += 1
            return EqPredicate(first, self.__try_parse_term())

    def __try_parse_args(self):
        args = [self.__try_parse_term()]
        while self.__index < len(self.__expression) and self.__expression[self.__index] == ",":
            self.__index += 1
            args.append(self.__try_parse_term())
        return tuple(args)

    def __try_parse_term(self):   # summand | term + summand
        first = self.__try_parse_summand()
        while self.__index < len(self.__expression) and self.__expression[self.__index] == "+":
            self.__index += 1
            first = Addition(first, self.__try_parse_summand())
        return first

    def __try_parse_summand(self):    # multiplied | summand * multiplied
        first = self.__try_parse_multiplied()
        while self.__index < len(self.__expression) and self.__expression[self.__index] == "*":
            self.__index += 1
            first = Multiply(first, self.__try_parse_multiplied())
        return first

    def __try_parse_multiplied(self):
        result = None
        if self.__expression[self.__index] == "0":
            self.__index += 1
            result = Variable("0")
        elif self.__expression[self.__index] == "(":    # ( term )
            self.__index += 1
            result = self.__try_parse_term()
            if self.__expression[self.__index] != ")":
                raise ParsingError("try_parse_multiplied")
            else:
                self.__index += 1
        else:
            res = self.__is_var.match(self.__expression, self.__index)
            if res is None:
                raise ParsingError("try_parse_multiplied")
            if res.end() != len(self.__expression) and self.__expression[res.end()] == "(":    # function
                self.__index = res.end() + 1
                result = Function(res.group(), self.__try_parse_args())
                self.__index += 1
            else:       # variable
                self.__index = res.end()
                result = Variable(res.group())
        while self.__index < len(self.__expression) and self.__expression[self.__index] == "'":
            self.__index += 1
            result = Increment(result)
        return result

