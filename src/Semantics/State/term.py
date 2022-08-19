from Semantics.State.variable import *

class Term:
    terms = None   # Terms or variable
    operator = None
    dbvars = None
    dbvarStrs = None
    literals = None
    literalStrs = None
    name_str = None

    def __init__(self, pTerms, pOperator):
        assert(len(pTerms) == 2 and pOperator in {"+", "-", "*", "/", "%"})
        self.isAtomic = False
        self.operator = pOperator
        self.terms = pTerms
        self.dbvars = set([])
        self.dbvarStrs = set([])
        self.literals = set([])
        self.literalStrs = set([])
        for term in self.terms:
            if isinstance(term, Term):
                self.dbvars = self.dbvars.union(term.dbvars)
                self.dbvarStrs = self.dbvarStrs.union(term.dbvarStrs)
                self.literals = self.literals.union(term.literals)
                self.literalStrs = self.literalStrs.union(term.literalStrs)
            elif isinstance(term, Variable):
                if term.isDBVar:
                    self.dbvars.add(term)
                    self.dbvarStrs.add(term.toString())
                elif term.isLiteral:
                    self.literals.add(term)
                    self.literalStrs.add(term.toString())
        return

    def toString(self):
        if self.name_str is not None:
            return self.name_str
        self.name_str = "(( " + self.operator + " ) "
        self.name_str += self.terms[0].toString()
        self.name_str += " "
        self.name_str += self.terms[1].toString()
        self.name_str += ")"
        return self.name_str

    def printTerm(self):
        print(self.toString())
        return

    def evaluate(self, DBValDic, literalValDic):
        leftTerm = self.terms[0]
        rightTerm = self.terms[1]
        leftTermValue = None
        rightTermValue = None
        if isinstance(leftTerm, Variable):
            if leftTerm.isDBVar:
                leftTermValue = DBValDic[leftTerm.toString()]
            elif leftTerm.isLiteral:
                leftTermValue = literalValDic[leftTerm.toString()]
        elif isinstance(leftTerm, Term):
            leftTermValue = leftTerm.evaluate(DBValDic, literalValDic)

        if isinstance(rightTerm, Variable):
            if rightTerm.isDBVar:
                rightTermValue = DBValDic[rightTerm.toString()]
            elif rightTerm.isLiteral:
                rightTermValue = literalValDic[rightTerm.toString()]
        elif isinstance(rightTerm, Term):
            rightTermValue = leftTerm.evaluate(DBValDic, literalValDic)

        if self.operator == "+":
            return leftTermValue + rightTermValue
        elif self.operator == "-":
            return leftTermValue - rightTermValue
        elif self.operator == "*":
            return leftTermValue * rightTermValue
        elif self.operator == "/":
            if rightTermValue == 0:
                return None
            return leftTermValue / rightTermValue
        elif self.operator == "%":
            if rightTermValue == 0:
                return None
            return leftTermValue % rightTermValue

    def symEvaluate(self, dbStrSymDic, literalStrSymDic):
        leftTerm = self.terms[0]
        rightTerm = self.terms[1]
        leftTermValue = None
        rightTermValue = None
        if isinstance(leftTerm, Variable):
            if leftTerm.isDBVar:
                leftTermValue = dbStrSymDic[leftTerm.toString()]
            elif leftTerm.isLiteral:
                leftTermValue = literalStrSymDic[leftTerm.toString()]
        elif isinstance(leftTerm, Term):
            leftTermValue = leftTerm.evaluate(dbStrSymDic, literalStrSymDic)

        if isinstance(rightTerm, Variable):
            if rightTerm.isDBVar:
                rightTermValue = dbStrSymDic[rightTerm.toString()]
            elif rightTerm.isLiteral:
                rightTermValue = literalStrSymDic[rightTerm.toString()]
        elif isinstance(rightTerm, Term):
            rightTermValue = leftTerm.evaluate(dbStrSymDic, literalStrSymDic)

        if self.operator == "+":
            return leftTermValue + rightTermValue
        elif self.operator == "-":
            return leftTermValue - rightTermValue
        elif self.operator == "*":
            return leftTermValue * rightTermValue
        elif self.operator == "/":
            if rightTermValue == 0:
                return None
            return leftTermValue / rightTermValue
        elif self.operator == "%":
            if rightTermValue == 0:
                return None
            return leftTermValue % rightTermValue
