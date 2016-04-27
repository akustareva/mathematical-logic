import parsers
from entities import *


class TransformationByDeduction:
    def __init__(self):
        self.__transformed = []
        self.__parser = parsers.FormalParser()

    def get_proof(self, proof: list, alpha: Expression):
        count = 0
        for expression in proof:
            count += 1
            # print("tr", count)
            if expression[1] == "alpha":
                self.__transform_alpha(expression[0])
            if expression[1] == "axiom" or expression[1] == "hypothesis":
                self.__transform_axiom(expression[0], alpha)
            if expression[1] == "MP":
                self.__transform_mp(expression[0][0], expression[0][1], alpha)
            if expression[1] == "UnQuantifier_rule":
                self.__transform_unq_rule(expression[0], alpha)
            if expression[1] == "ExQuantifier_rule":
                self.__transform_exq_rule(expression[0], alpha)
        return self.__transformed

    def __transform_alpha(self, expression: Expression):
        tmp1 = Implication(expression, Implication(expression, expression))
        tmp2 = Implication(expression, Implication(Implication(expression, expression), expression))
        tmp3 = Implication(expression, expression)
        self.__transformed.append(tmp1)
        self.__transformed.append(Implication(tmp1, Implication(tmp2, tmp3)))
        self.__transformed.append(Implication(tmp2, tmp3))
        self.__transformed.append(tmp2)
        self.__transformed.append(tmp3)

    def __transform_axiom(self, expression: Expression, alpha: Expression):
        self.__transformed.append(expression)
        self.__transformed.append(Implication(expression, Implication(alpha, expression)))
        self.__transformed.append(Implication(alpha, expression))

    def __transform_mp(self, expression: Expression, delta: Expression, alpha: Expression):
        tmp1 = Implication(alpha, delta)
        tmp2 = Implication(alpha, Implication(delta, expression))
        tmp3 = Implication(alpha, expression)
        self.__transformed.append(Implication(tmp1, Implication(tmp2, tmp3)))
        self.__transformed.append(Implication(tmp2, tmp3))
        self.__transformed.append(tmp3)

    def __transform_unq_rule(self, expression: Implication, alpha: Expression):
        unq = open("proofs/un_quantifier.txt", "r")
        for line in unq:
            if line[-1] == "\n":
                line = line[:-1]
            self.__transformed.append(line.replace("#", "(" + str(alpha) + ")").
                                      replace("%", "(" + str(expression.get_first_arg()) + ")").
                                      replace("$", "(" + str(expression.get_second_arg().get_expression()) + ")").
                                      replace("_", str(expression.get_second_arg().get_variable())))
        unq.close()

    def __transform_exq_rule(self, expression: Implication, alpha: Expression):
        exq = open("proofs/ex_quantifier.txt", "r")
        for line in exq:
            if line[-1] == "\n":
                line = line[:-1]
            self.__transformed.append(line.replace("#", "(" + str(alpha) + ")").
                                      replace("%", "(" + str(expression.get_first_arg().get_expression()) + ")").
                                      replace("$", "(" + str(expression.get_second_arg()) + ")").
                                      replace("_", str(expression.get_first_arg().get_variable())))
        exq.close()
