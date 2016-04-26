from entities import *
import parsers


class Checker:
    def __init__(self, ):
        self.hypothesis = []
        self.proofed = []
        self.proofed_implications = []
        self.classical_parser = parsers.ClassicalParser()
        self.formal_parser = parsers.FormalParser()
        self.classical_axioms = (
            self.classical_parser.parse_expression("A->B->A"),
            self.classical_parser.parse_expression("(A->B)->(A->B->C)->(A->C)"),
            self.classical_parser.parse_expression("A->B->A&B"),
            self.classical_parser.parse_expression("A&B->A"),
            self.classical_parser.parse_expression("A&B->B"),
            self.classical_parser.parse_expression("A->A|B"),
            self.classical_parser.parse_expression("B->A|B"),
            self.classical_parser.parse_expression("(A->C)->(B->C)->(A|B->C)"),
            self.classical_parser.parse_expression("(A->B)->(A->!B)->!A"),
            self.classical_parser.parse_expression("!!A->A")
        )
        self.formal_axioms = (
            self.formal_parser.parse_expression("a=b->a'=b'"),
            self.formal_parser.parse_expression("a=b->a=c->b=c"),
            self.formal_parser.parse_expression("a'=b'->a=b"),
            self.formal_parser.parse_expression("!a'=0"),
            self.formal_parser.parse_expression("a+b'=(a+b)'"),
            self.formal_parser.parse_expression("a+0=a"),
            self.formal_parser.parse_expression("a*0=0"),
            self.formal_parser.parse_expression("a*b'=a*b+a")
        )

    def check_expression(self, header: str, proof: list):
        self.hypothesis = []
        self.proofed = []
        self.proofed_implications = []
        pos = header.find("|-")
        header = header[:pos]
        while len(header) > 0:
            header, token = self.get_token(header)
            self.hypothesis.append(token)
        alpha = None
        free_vars_in_alpha = set()
        if len(self.hypothesis) > 0:
            alpha = self.hypothesis[-1]
            self.hypothesis.pop()
            free_vars_in_alpha = self.get_free_vars(alpha)
        count = 0
        for line in proof:
            count += 1
            # print(count)
            expression = self.formal_parser.parse_expression(line)
            if (alpha is not None) and (expression == alpha):
                self.write_answer(expression, "alpha")
                continue
            elif self.is_hypothesis(expression):
                self.write_answer(expression, "hypothesis")
                continue
            elif self.is_classical_axiom(expression) or self.is_formal_axiom(expression) \
                    or self.is_quantifier_axiom(expression):
                self.write_answer(expression, "axiom")
                continue
            else:
                derivation_rule = self.is_derivation_rule(expression, free_vars_in_alpha)
                if derivation_rule[0]:
                    self.write_answer(expression, derivation_rule[1])
                    continue
                else:
                    return False, count, None
        return True, self.proofed, alpha

    def get_token(self, header: str):
        expression, index = self.formal_parser.parse_part_of_expression(header, 0)
        if index < len(header) and header[index] == ",":
            index += 1
        return header[index:], expression

    def write_answer(self, expression: Expression, type_of_element: str):
        self.proofed.append((expression, type_of_element))
        if isinstance(expression, Implication):
            self.proofed_implications.append(expression)

    def is_hypothesis(self, expression: Expression):
        for hypothesis in self.hypothesis:
            if hypothesis == expression:
                return True
        return False

    def is_classical_axiom(self, expression: Expression):
        for axiom in self.classical_axioms:
            answer, ignored = self.identical_form(axiom, expression)
            if answer:
                return True
        return False

    def is_formal_axiom(self, expression: Expression):
        for axiom in self.formal_axioms:
            answer, ignored = self.identical_form(axiom, expression)
            if answer:
                return True
        return False

    def identical_form(self, axiom: Expression, expression: Expression, variables=None):
        if variables is None:
            variables = {}
        if isinstance(axiom, Quantifier):
            return False, None
        if (isinstance(expression, UnaryOperations) and isinstance(axiom, UnaryOperations)) \
                or (isinstance(expression, BinaryOperations) and isinstance(axiom, BinaryOperations)) \
                or (isinstance(expression, EqPredicate) and isinstance(axiom, EqPredicate)) \
                or (isinstance(expression, Predicate) and isinstance(axiom, Predicate)) \
                or isinstance(expression, Function) and isinstance(axiom, Function):
            if expression.get_operation() != axiom.get_operation():
                return False, variables
            axiom_args = axiom.get_args()
            expr_args = expression.get_args()
            if len(expr_args) != len(axiom_args):
                return False, variables
            for i in range(0, len(axiom_args)):
                answ, variables = self.identical_form(axiom_args[i], expr_args[i], variables)
                if not answ:
                    return False, variables
            return True, variables
        elif isinstance(axiom, Variable):
            var_name = axiom.get_name()
            if var_name in variables.keys():
                if expression == variables[var_name]:
                    return True, variables
                return False, variables
            else:
                variables[var_name] = expression
                return True, variables
        else:
            return False, variables

    def is_quantifier_axiom(self, expression: Expression):
        if not isinstance(expression, Implication):
            return False
        first = expression.get_first_arg()
        second = expression.get_second_arg()
        if isinstance(first, UnQuantifier):
            answer, ignored = self.try_parse_quantifier_axiom(first.get_variable(), first.get_expression(), second)
            return answer
        if isinstance(second, ExQuantifier):
            answer, ignored = self.try_parse_quantifier_axiom(second.get_variable(), second.get_expression(), first)
            return answer
        if isinstance(first, Conjunction):
            if not isinstance(first.get_second_arg(), UnQuantifier):
                return False
            if not isinstance(first.get_second_arg().get_args()[0], Implication):  # a->(a[x:=x'])
                return False
            start = first.get_first_arg()
            middle = first.get_second_arg().get_args()[0].get_first_arg()
            end = first.get_second_arg().get_args()[0].get_second_arg()
            if not middle == second:
                return False
            free_vars = self.get_free_vars(second)
            q_var = first.get_second_arg().get_variable()
            if q_var.get_name() not in free_vars:
                return False
            answer, sub = self.try_parse_quantifier_axiom(q_var, middle, start)
            if (not answer) or (not sub == Variable("0")):
                return False
            answer, sub = self.try_parse_quantifier_axiom(q_var, middle, end)
            if answer and (sub == Increment(q_var)):
                return True
        return False

    def try_parse_quantifier_axiom(self, variable: Variable, first: Expression, second: Expression, con_vars=None):
        if con_vars is None:
            con_vars = set()
        if isinstance(first, Quantifier) and isinstance(second, Quantifier):
            if first.get_variable() != second.get_variable():
                return False, None
            con_vars.add(first.get_variable().get_name())
            return self.try_parse_quantifier_axiom(variable, first.get_expression(), second.get_expression(), con_vars)
        elif (isinstance(first, UnaryOperations) and isinstance(second, UnaryOperations)) \
                or (isinstance(first, BinaryOperations) and isinstance(second, BinaryOperations)) \
                or (isinstance(first, EqPredicate) and isinstance(second, EqPredicate)) \
                or (isinstance(first, Predicate) and isinstance(second, Predicate)) \
                or (isinstance(first, Function) and isinstance(second, Function)):
            if first.get_operation() != second.get_operation():
                return False, None
            first_args = first.get_args()
            second_args = second.get_args()
            if len(first_args) != len(second_args):
                return False, None
            sub = None
            for i in range(0, len(first_args)):
                answ, tmp = self.try_parse_quantifier_axiom(variable, first_args[i], second_args[i], con_vars)
                if not answ:
                    return False, None
                if sub is None:
                    sub = tmp
                elif (tmp is not None) and (sub != tmp):
                    return False, None
            return True, sub
        elif isinstance(first, Variable):
            if (first.get_name() != variable.get_name()) or (first.get_name() in con_vars):
                if not isinstance(second, Variable):
                    return False, None
                return bool(first == second), None
            else:
                free_vars = self.get_free_vars(second)
                if len(set.intersection(free_vars, con_vars)) == 0:
                    return True, second
                return False, None
        else:
            return False, None

    def get_free_vars(self, expression: Expression, con_vars=None):
        if con_vars is None:
            con_vars = set()
        answer = set()
        if isinstance(expression, Quantifier):
            con_vars.add(expression.get_variable().get_name())
            answer = self.get_free_vars(expression.get_expression(), con_vars)
        elif isinstance(expression, UnaryOperations) or isinstance(expression, BinaryOperations) \
                or isinstance(expression, EqPredicate) or isinstance(expression, Predicate) \
                or isinstance(expression, Function):
            expression_args = expression.get_args()
            for arg in expression_args:
                answer = answer.union(self.get_free_vars(arg, con_vars))
        elif isinstance(expression, Variable):
            if expression.get_name() not in con_vars:
                answer.add(expression.get_name())
        return answer

    def is_derivation_rule(self, expression: Expression, free_vars_in_alpha: set()):
        for impl in reversed(self.proofed_implications):      # a, a->b => b
            if impl.get_second_arg() == expression:
                first = impl.get_first_arg()
                for check in reversed(self.proofed):
                    if first == check[0]:
                        return True, "MP"
        if not isinstance(expression, Implication):
            return False, None
        first = expression.get_first_arg()
        second = expression.get_second_arg()
        if isinstance(second, UnQuantifier):    # a->b => a->@x(b)
            free_vars = self.get_free_vars(first)
            q_var = second.get_variable().get_name()
            if q_var in free_vars:
                return False, None
            if q_var in free_vars_in_alpha:
                return False, None
            second_without_quantifier = second.get_expression()
            tmp_impl = Implication(first, second_without_quantifier)
            for impl in self.proofed_implications:
                if impl == tmp_impl:
                    return True, "UnQuantifier_rule"
            return False, None
        elif isinstance(first, ExQuantifier):       # b->a => ?x(b)->a
            free_vars = self.get_free_vars(second)
            q_var = first.get_variable().get_name()
            if q_var in free_vars:
                return False, None
            if q_var in free_vars_in_alpha:
                return False, None
            first_without_quantifier = first.get_expression()
            tmp_impl = Implication(first_without_quantifier, second)
            for impl in self.proofed_implications:
                if impl == tmp_impl:
                    return True, "ExQuantifier_rule"
            return False, None
        else:
            return False, None
