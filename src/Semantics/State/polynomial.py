from copy import *
from Semantics.State.term import *

class Monomial:
    varOrTerms = None
    dbvars = None
    dbvarStrs = None
    literals = None
    literalStrs = None
    operator = None
    isTrivialTrue = None
    isTrivialFalse  = None
    name_str = None
    varNum = None
    termNum = None

    def __init__(self, p_varTerms, p_operator, p_isTrivialTrue, p_isTrivalFalse):
        assert(p_operator in {"!=", "==", ">", "<", ">=", "<=", "contains", "startsWith", "endsWith", "ncontains", "nstartsWith", "nendsWith", None})
        self.varOrTerms = deepcopy(p_varTerms)
        self.operator = p_operator
        self.isTrivialTrue = p_isTrivialTrue
        self.isTrivialFalse = p_isTrivalFalse
        self.dbvars = set([])
        self.dbvarStrs = set([])
        self.literals = set([])
        self.literalStrs = set([])
        self.varNum = 0
        self.termNum = 0
        for varOrTerm in self.varOrTerms:
            if isinstance(varOrTerm, Variable):
                self.varNum += 1
                if varOrTerm.isDBVar:
                    self.dbvars.add(varOrTerm)
                    self.dbvarStrs.add(varOrTerm.name_str)
                else:
                    self.literals.add(varOrTerm)
                    self.literalStrs.add(varOrTerm.name_str)
            elif isinstance(varOrTerm, Term):
                self.termNum += 1
                self.dbvars = self.dbvars.union(varOrTerm.dbvars)
                self.dbvarStrs = self.dbvarStrs.union(varOrTerm.dbvarStrs)
                self.literals = self.literals.union(varOrTerm.literals)
                self.literalStrs = self.literalStrs.union(varOrTerm.literalStrs)
        return

    def toString(self):
        if self.name_str is None:
            assert(not (self.isTrivialFalse and self.isTrivialTrue))
            if self.isTrivialTrue:
                self.name_str = "1"
            elif self.isTrivialFalse:
                self.name_str = "0"
            else:
                assert(len(self.varOrTerms) == 2)
                self.name_str = "[" + self.varOrTerms[0].toString() + " " + self.operator + " " + self.varOrTerms[1].toString() + "]"
        return self.name_str

    def printMonomial(self):
        print(self.toString())
        return


class Polynomial:
    dbvars = None
    dbvarStrs = None
    literals = None
    opStrs = None
    subpolys = None
    type = None
    name_str = None
    complexity = None
    varNum = None
    termNum = None

    def __init__(self, op, p_subpolys):
        assert(op in {"()", "+", "*"})
        self.subpolys = []

        self.dbvars = set([])
        self.dbvarStrs = set([])
        self.opStrs = set([])
        self.literals = set([])
        self.literalStrs = set([])
        self.varNum = 0
        self.termNum = 0
        if op == "()":
            assert(len(p_subpolys) == 1)
            self.type = "Monomial"
            self.subpolys.append(p_subpolys[0])
            self.dbvars = p_subpolys[0].dbvars
            self.dbvarStrs = p_subpolys[0].dbvarStrs
            self.literals = p_subpolys[0].literals
            self.literalStrs = p_subpolys[0].literalStrs
            self.opStrs.add(p_subpolys[0].operator)
            self.varNum = p_subpolys[0].varNum
            self.termNum = p_subpolys[0].termNum
        elif op == "+":
            self.type = "Sum Polynomial"
            self.subpolys = []
            for p_subpoly in p_subpolys:
                self.varNum += p_subpoly.varNum
                self.termNum += p_subpoly.termNum
                self.dbvars = self.dbvars.union(p_subpoly.dbvars)
                self.dbvarStrs = self.dbvarStrs.union(p_subpoly.dbvarStrs)
                self.opStrs = self.opStrs.union(p_subpoly.opStrs)
                self.literals = self.literals.union(p_subpoly.literals)
                self.literalStrs = self.literalStrs.union(p_subpoly.literalStrs)
                if p_subpoly.type == "Sum Polynomial":
                    self.subpolys.extend(deepcopy(p_subpoly.subpolys))
                else:
                    self.subpolys.append(p_subpoly)
        elif op == "*":
            self.type = "Product Polynomial"
            self.subpolys = []
            for p_subpoly in p_subpolys:
                self.varNum += p_subpoly.varNum
                self.termNum += p_subpoly.termNum
                self.dbvars = self.dbvars.union(p_subpoly.dbvars)
                self.dbvarStrs = self.dbvarStrs.union(p_subpoly.dbvarStrs)
                self.opStrs = self.opStrs.union(p_subpoly.opStrs)
                self.literals = self.literals.union(p_subpoly.literals)
                self.literalStrs = self.literalStrs.union(p_subpoly.literalStrs)
                if p_subpoly.type == "Product Polynomial":
                    self.subpolys.extend(deepcopy(p_subpoly.subpolys))
                else:
                    self.subpolys.append(p_subpoly)
        self.simplify()
        self.complexity = self.computeComplexity()
        return

    def computeComplexity(self):
        if self.type == "Monomial":
            return 1
        maxComplexity = 0
        for subpoly in self.subpolys:
            tmpComplexity = subpoly.computeComplexity()
            maxComplexity = tmpComplexity if tmpComplexity > maxComplexity else tmpComplexity
        return (maxComplexity + 1)

    def notPoly(self):
        assert(self.type in {"Monomial", "Sum Polynomial", "Product Polynomial"})
        if self.type == "Monomial":
            m = self.subpolys[0]
            assert(m.operator in {"!=", "==", ">", "<", ">=", "<=", "contains", "startsWith", "endsWith", "ncontains", "nstartsWith", "nendsWith", None})
            if m.operator is None:
                assert(m.isTrivialTrue or m.isTrivialFalse)
                m.isTrivialTrue = not m.isTrivialTrue
                m.isTrivialFalse = not m.isTrivialFalse
                m.name_str = None
            else:
                cmp_ops = ["endsWith", "startsWith", "contains", "==", ">", "<", ">=", "<=", "!=", "ncontains", "nstartsWith", "nendsWith"]
                for i in range(len(cmp_ops)):
                    if cmp_ops[i] == m.operator:
                        m.operator = cmp_ops[11 - i]
                        m.name_str = None
                        self.name_str = None
                        return
        elif self.type == "Sum Polynomial":
            for subpoly in self.subpolys:
                subpoly.notPoly()
                self.type = "Product Polynomial"
                self.name_str = None
        elif self.type == "Product Polynomial":
            for subpoly in self.subpolys:
                subpoly.notPoly()
                self.type = "Sum Polynomial"
                self.name_str = None
        self.simplify()
        return

    # The function simplify might be costly
    def simplify(self):
        if self.type == "Sum Polynomial":
            subpolys = []
            for subpoly in self.subpolys:
                if subpoly.toString() == "1":
                    self.type = "Monomial"
                    self.subpolys = []
                    self.subpolys.append(Polynomial("()", [Monomial([], None, True, False)]))
                    self.name_str = None
                    return
                elif subpoly.toString() != "0":
                    subpoly.simplify()
                    subpolys.append(subpoly)
                    self.name_str = None
            if len(subpolys) == 1:
                tmp_subpoly = deepcopy(subpolys[0])
                self.subpolys = tmp_subpoly.subpolys
                self.type = tmp_subpoly.type
                self.name_str = None
            else:
                self.subpolys = subpolys
                self.name_str = None
        elif self.type == "Product Polynomial":
            subpolys = []
            for subpoly in self.subpolys:
                if subpoly.toString() == "0":
                    self.type = "Monomial"
                    self.subpolys = []
                    self.subpolys.append(Polynomial("()", [Monomial([], None, False, True)]))
                    self.name_str = None
                    return
                elif subpoly.toString() != "1":
                    subpoly.simplify()
                    subpolys.append(subpoly)
                    self.name_str = None
            if len(subpolys) == 1:
                tmp_subpoly = deepcopy(subpolys[0])
                self.subpolys = tmp_subpoly.subpolys
                self.type = tmp_subpoly.type
                self.name_str = None
            else:
                self.subpolys = subpolys
                self.name_str = None
        return

    def toString(self):
        if self.name_str is None:
            assert(self.type in {"Monomial", "Sum Polynomial", "Product Polynomial"})
            self.name_str = ""
            if self.type == "Monomial":
                assert(len(self.subpolys) == 1)
                self.name_str = self.name_str + self.subpolys[0].toString()
            elif self.type == "Sum Polynomial":
                self.name_str = "("
                for subpoly in self.subpolys:
                    self.name_str = self.name_str + subpoly.toString() + "+"
                self.name_str = self.name_str.rstrip("+")
                self.name_str = self.name_str + ")"
            elif self.type == "Product Polynomial":
                self.name_str = "("
                for subpoly in self.subpolys:
                    self.name_str = self.name_str + subpoly.toString() + "*"
                self.name_str = self.name_str.rstrip("*")
                self.name_str = self.name_str + ")"
        return self.name_str

    def printPolynomial(self):
        print(self.toString())
        for var in self.dbvars:
            print(var.name_str)
        for varStr in self.dbvarStrs:
            print(varStr)
        print(self.complexity)
        return
