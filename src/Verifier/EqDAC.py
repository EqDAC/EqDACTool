from Util.parser import *
from Semantics.State.constructor import *
from Semantics.Symbolic.litencode import *
from Semantics.Symbolic.formula import *
from Verifier.Isomorphism.isomorphism import *
from Verifier.Divergence.divergence import *


class EqDAC:
    ruleFile = None
    invDBVars = None
    certValue = None
    symformula = None
    symVarDic = None
    ac = None

    def __init__(self, pRuleFile):
        self.ruleFile = pRuleFile
        graph = ruleGraph(self.ruleFile)
        self.ac = AlgebraicConstructor(graph.nodeLabels, graph.topNodeLabels)
        self.ac.extractVarLiteral()
        self.invDBVars = self.ac.invDBVars
        self.ac.transform()

    def getCertificate(self):
        if self.certValue is None:
            self.certValue = IsomorphismAnalyzer(self.ac.poly).certVal
        return self.certValue

    def getSMTFormula(self):
        if self.symformula is not None:
            return self.symformula
        self.symVarDic = {}
        self.symStrVarDic = {}
        self.litEncodeDic = litencode(self.ac.poly, self.ac.poly)
        self.symformula = formula(self.ac.poly, self.symVarDic, self.symStrVarDic, self.litEncodeDic)
        return self.symformula

    def checkDivergence(self, poly:Polynomial):
        thisPoly = self.ac.poly
        t = DivergenceAnalyzer(poly, thisPoly)
        return t.isDivergence

    def checkIsomorphism(self, pCert):
        thisCert = self.getCertificate()
        return thisCert == pCert

    def checkBySMT(self, pSymFormula):
        symFormula = self.getSMTFormula()
        s = Solver()
        s.add(Implies(And(symFormula.s.assertions()), And(pSymFormula.s.assertions())))
        s.add(Implies(And(pSymFormula.s.assertions()), And(symFormula.s.assertions())))
        ts = Solver()
        ts.add(Not(And(s.assertions())))
        checkResult = ts.check()
        return checkResult

