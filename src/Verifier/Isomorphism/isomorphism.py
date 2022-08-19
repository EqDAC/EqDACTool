from copy import *
from Semantics.State.term import *

class IsomorphismAnalyzer:
    poly = None
    certVal = None

    def __init__(self, p_poly):
        self.poly = deepcopy(p_poly)
        self.certVal = self.polyPIE(self.poly)

    def polyPIE(self, p_poly):
        assert(p_poly.type in {"Monomial", "Sum Polynomial", "Product Polynomial"})
        if p_poly.type == "Monomial":
            m = p_poly.subpolys[0]
            if isinstance(m.varOrTerms[0], Variable):
                leftPIEValue = hash(m.varOrTerms[0].toString())
            elif isinstance(m.varOrTerms[0], Term):
                leftPIEValue = self.termPIE(m.varOrTerms[0])
            if isinstance(m.varOrTerms[1], Variable):
                rightPIEValue = hash(m.varOrTerms[1].toString())
            elif isinstance(m.varOrTerms[1], Term):
                rightPIEValue = self.termPIE(m.varOrTerms[1])
            PIEs = [leftPIEValue, rightPIEValue]
            op = None
            if m.operator in {"==", "!="}:
                op = m.operator
                if leftPIEValue > rightPIEValue:
                    PIEs.reverse()
            elif m.operator in {">", ">="}:
                PIEs.reverse()
                if m.operator == ">":
                    op = "<"
                elif m.operator == ">=":
                    op = "<="
            else:
                op = m.operator
            return hash(str(PIEs[0]) + "," + str(PIEs[1]) + ":" + op)
        else:
            hashValues = []
            for p_subpoly in p_poly.subpolys:
                hashValues.append(self.polyPIE(p_subpoly))
            hashValues.sort()
            hashValues.append(hash(p_poly.type))
            return hash(str(hashValues))

    def termPIE(self, p_term):
        if isinstance(p_term, Variable):
            return hash(p_term.toString())
        # "+" and "*"
        if p_term.operator not in {"+", "*"}:
            leftPIE = self.termPIE(p_term.terms[0])
            rightPIE = self.termPIE(p_term.terms[1])
            return hash(str(leftPIE) + "," + str(rightPIE) + ":" + p_term.operator)
        else:
            termList = self.flatenTerm(p_term, p_term.operator)
            termPIEList = []
            for t in termList:
                termPIEList.append(hash(t.toString()))
            termPIEList.sort()
            hashStr = ""
            for termPIE in termPIEList:
                hashStr += str(termPIE) + ","
            return hash(hashStr + ":" + p_term.operator)

    def flatenTerm(self, p_term, op):
        if isinstance(p_term, Variable):
            return [p_term]
        if p_term.operator != op:
            return [p_term]
        termList = []
        termList.extend(self.flatenTerm(p_term.terms[0], op))
        termList.extend(self.flatenTerm(p_term.terms[1], op))
        return termList
