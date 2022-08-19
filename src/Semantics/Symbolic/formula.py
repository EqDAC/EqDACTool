from z3 import *
from Semantics.State.term import *

class formula:
    symVarDic = None
    poly = None
    litEncodeDic = None
    s = None

    def __init__(self, p_poly, p_symVarDic, p_symStrVarDic, p_litEncodeDic):
        self.poly = p_poly
        self.symVarDic = p_symVarDic
        self.symStrVarDic = p_symStrVarDic
        self.litEncodeDic = p_litEncodeDic
        self.s = self.constructFormula(self.poly)

    def assignSymbol(self, varOrTerm):
        if isinstance(varOrTerm, Variable):
            varStr = varOrTerm.toString()
            if varStr in self.symVarDic:
                return self.symVarDic[varStr]
            else:
                if varOrTerm.isLiteral:
                    intLabel = self.litEncodeDic.literalToIntMap[varOrTerm.name[0]]
                    assert(intLabel >= 0)
                    self.symVarDic[varStr] = intLabel
                else:
                    varSym = BitVec(varStr, 64)
                    self.symVarDic[varStr] = varSym
                return self.symVarDic[varStr]
        elif isinstance(varOrTerm, Term):
            dbStrSymDic = {}
            literalStrSymDic = {}
            for literal in varOrTerm.literals:
                literalStrSymDic[literal.name_str] = self.assignSymbol(literal)
            for dbvar in varOrTerm.dbvars:
                dbStrSymDic[dbvar.name_str] = self.assignSymbol(dbvar)
            return varOrTerm.symEvaluate(dbStrSymDic, literalStrSymDic)


    def assignStrSymbol(self, var):
        varStr = var.toString()
        if var.isLiteral:
            return varStr
        if varStr in self.symStrVarDic:
            return self.symStrVarDic[varStr]
        else:
            varSym = String(varStr)
            self.symStrVarDic[varStr] = varSym
            return self.symStrVarDic[varStr]

    def assignSymbolByVarStr(self, varStr):
        if varStr in self.symVarDic:
            return self.symVarDic[varStr]
        else:
            if "id" in varStr:
                varSym = BitVec(varStr, 64)
            else:
                varSym = FP(varStr, FPSort(8, 24))
            self.symVarDic[varStr] = varSym
            return self.symVarDic[varStr]

    def constructFormulaForMonomial(self, p_poly):
        assert (len(p_poly.subpolys) == 1)
        if p_poly.subpolys[0].isTrivialTrue:
            subs = Solver()
            subs.add(True)
            return subs
        elif p_poly.subpolys[0].isTrivialFalse:
            subs = Solver()
            subs.add(False)
            return subs
        else:
            subs = Solver()
            assert (len(p_poly.subpolys[0].varOrTerms) == 2)
            op = p_poly.subpolys[0].operator
            if op == "==":
                l = self.assignSymbol(p_poly.subpolys[0].varOrTerms[0])
                r = self.assignSymbol(p_poly.subpolys[0].varOrTerms[1])
                subs.add(l == r)
            elif op == "!=":
                l = self.assignSymbol(p_poly.subpolys[0].varOrTerms[0])
                r = self.assignSymbol(p_poly.subpolys[0].varOrTerms[1])
                subs.add(l != r)
            elif op == ">":
                l = self.assignSymbol(p_poly.subpolys[0].varOrTerms[0])
                r = self.assignSymbol(p_poly.subpolys[0].varOrTerms[1])
                subs.add(l > r)
            elif op == "<":
                l = self.assignSymbol(p_poly.subpolys[0].varOrTerms[0])
                r = self.assignSymbol(p_poly.subpolys[0].varOrTerms[1])
                subs.add(l < r)
            elif op == ">=":
                l = self.assignSymbol(p_poly.subpolys[0].varOrTerms[0])
                r = self.assignSymbol(p_poly.subpolys[0].varOrTerms[1])
                subs.add(l >= r)
            elif op == "<=":
                l = self.assignSymbol(p_poly.subpolys[0].varOrTerms[0])
                r = self.assignSymbol(p_poly.subpolys[0].varOrTerms[1])
                subs.add(l <= r)
            elif op == "contains":
                l = self.assignStrSymbol(p_poly.subpolys[0].varOrTerms[0])
                r = self.assignStrSymbol(p_poly.subpolys[0].varOrTerms[1])
                subs.add(Contains(l, r))
            elif op == "ncontains":
                l = self.assignStrSymbol(p_poly.subpolys[0].varOrTerms[0])
                r = self.assignStrSymbol(p_poly.subpolys[0].varOrTerms[1])
                subs.add(Not(Contains(l, r)))
            elif op == "startsWith":
                l = self.assignStrSymbol(p_poly.subpolys[0].varOrTerms[0])
                r = self.assignStrSymbol(p_poly.subpolys[0].varOrTerms[1])
                subs.add(PrefixOf(l, r))
            elif op == "nstartsWith":
                l = self.assignStrSymbol(p_poly.subpolys[0].varOrTerms[0])
                r = self.assignStrSymbol(p_poly.subpolys[0].varOrTerms[1])
                subs.add(Not(PrefixOf(l, r)))
            elif op == "endsWith":
                l = self.assignStrSymbol(p_poly.subpolys[0].varOrTerms[0])
                r = self.assignStrSymbol(p_poly.subpolys[0].varOrTerms[1])
                subs.add(SuffixOf(l, r))
            elif op == "nendsWith":
                l = self.assignStrSymbol(p_poly.subpolys[0].varOrTerms[0])
                r = self.assignStrSymbol(p_poly.subpolys[0].varOrTerms[1])
                subs.add(Not(SuffixOf(l, r)))
            return subs

    def constructFormulaForMonomials(self, monomials):
        if len(monomials) == 0:
            return None
        valueDic = {}
        subconjs = []
        for monomial in monomials:
            if monomial.varOrTerms[1].isLiteral:
                if monomial.varOrTerms[0].toString() not in valueDic:
                    valueDic[monomial.varOrTerms[0].toString()] = set([])
                    valueDic[monomial.varOrTerms[0].toString()].add(self.assignSymbol(monomial.varOrTerms[1]))
                else:
                    valueDic[monomial.varOrTerms[0].toString()].add(self.assignSymbol(monomial.varOrTerms[1]))
            else:
                if monomial.varOrTerms[1].toString() not in valueDic:
                    valueDic[monomial.varOrTerms[1].toString()] = set([])
                    valueDic[monomial.varOrTerms[1].toString()].add(self.assignSymbol(monomial.varOrTerms[0]))
                else:
                    valueDic[monomial.varOrTerms[1].toString()].add(self.assignSymbol(monomial.varOrTerms[0]))
        for var in valueDic:
            bitMap = {}
            geqLiteral = []
            leqLiteral = []
            eqLiteral = []
            for i in range(self.litEncodeDic.upperInt):
                bitMap[i] = 0
            for literal in valueDic[var]:
                bitMap[literal] = 1
            i = 0
            while(i < self.litEncodeDic.upperInt):
                if bitMap[i] == 0:
                    i += 1
                    continue
                j = i
                while (j < self.litEncodeDic.upperInt):
                    if bitMap[j] == 1:
                        j += 1
                    else:
                        break
                if i == j:
                    eqLiteral.append(i)
                else:
                    geqLiteral.append(i)
                    leqLiteral.append(j)
                i = j + 1
            l = self.assignSymbolByVarStr(var)
            subs = Solver()
            for literal in eqLiteral:
                subs.add(l == literal)
            for literal in geqLiteral:
                subs.add(l >= literal)
            for literal in leqLiteral:
                subs.add(l <= literal)
            subconjs.append(And(subs.assertions()))
        s = Solver()
        s.append(Or(subconjs))
        return s

    def constructFormula(self, p_poly):
        assert (p_poly.type in {"Monomial", "Sum Polynomial", "Product Polynomial"})
        s = Solver()
        if p_poly.type == "Monomial":
            s = self.constructFormulaForMonomial(p_poly)
        elif p_poly.type == "Sum Polynomial":
            subconjs = []
            litmonomial = []
            for p_subpoly in p_poly.subpolys:
                if p_subpoly.type == "Monomial":
                    if p_subpoly.subpolys[0].operator == "==":
                        if (p_subpoly.subpolys[0].varOrTerms[0].isLiteral and (not p_subpoly.subpolys[0].varOrTerms[1].isLiteral)) or (p_subpoly.subpolys[0].varOrTerms[1].isLiteral and (not p_subpoly.subpolys[0].varOrTerms[0].isLiteral)):
                            litmonomial.append(p_subpoly.subpolys[0])
                            continue
                subs = self.constructFormula(p_subpoly)
                subconjs.append(And(subs.assertions()))
            monSolver = self.constructFormulaForMonomials(litmonomial)
            if monSolver is not None:
                subconjs.append(And(monSolver.assertions()))
            s.add(Or(subconjs))
        elif p_poly.type == "Product Polynomial":
            subconjs = []
            for p_subpoly in p_poly.subpolys:
                subs = self.constructFormula(p_subpoly)
                subconjs.append(And(subs.assertions()))
            s.add(And(subconjs))
        return s


