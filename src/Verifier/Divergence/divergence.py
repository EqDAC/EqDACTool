from typing import Set

from Semantics.State.term import *
from Semantics.State.polynomial import *
import random

class DivergenceAnalyzer:
    poly1 = None
    poly2 = None
    varStrToValueDic = None
    literalDic = None

    commonVarStrs = None
    fixedVarStrs = None
    varStrs1 = None
    varStrs2 = None

    literalStrs1 = None
    literalStrs2 = None
    commonLiteralStrs = None
    commonOpStrs = None

    strInt2Literal = None

    isDivergence = None

    def __init__(self, p_poly1: Polynomial, p_poly2: Polynomial):
        self.poly1 = p_poly1
        self.poly2 = p_poly2

        self.poly1Str = p_poly1.toString()
        self.poly2Str = p_poly2.toString()
        if self.poly1Str == self.poly2Str:
            self.isDivergence = False
            return
        if self.poly2Str == "1" and self.poly1Str == "0":
            self.isDivergence = True
            return
        if self.poly1Str == "0" and self.poly2Str == "1":
            self.isDivergence = True
            return

        self.varStrs1 = p_poly1.dbvarStrs
        self.varStrs2 = p_poly2.dbvarStrs

        self.literalStrs1 = p_poly1.literalStrs
        self.literalStrs2 = p_poly2.literalStrs
        self.fixedVarStrs = set([])
        self.varStrToValueDic = {}
        self.literalDic = {}
        self.strInt2Literal = {}
        for varStr in self.varStrs1:
            self.varStrToValueDic[varStr] = None
        for varStr in self.varStrs2:
            self.varStrToValueDic[varStr] = None
        self.commonVarStrs = self.varStrs1.intersection(self.varStrs2)
        self.commonLiteralStrs = self.literalStrs1.intersection(self.literalStrs2)
        self.commonOpStrs = p_poly1.opStrs.intersection(p_poly2.opStrs)

        for literal in self.literalStrs1.union(self.literalStrs2):
            self.literalDic[literal] = len(self.literalDic)
            self.varStrToValueDic[literal] = self.literalDic[literal]

        self.test()
        if self.isDivergence is None:
            self.clearVarStrToValueDic()
            self.test()
        return

    def clearVarStrToValueDic(self):
        self.fixedVarStrs = set([])
        for varStr in self.varStrToValueDic:
            self.varStrToValueDic[varStr] = None
        for varStr in self.literalDic:
            self.varStrToValueDic[varStr] = self.literalDic[varStr]
        return

    def enforce(self, p1: bool, p2: bool):
        if self.isDivergence is not None:
            return
        assert((p1 and (not p2)) or ((not p1) and (p2)))
        truePoly = self.poly1 if p1 else self.poly2
        trueVarStrs = (self.varStrs1 - self.commonVarStrs) if p1 else (self.varStrs2 - self.commonVarStrs)
        falsePoly = self.poly2 if p1 else self.poly1
        falseVarStrs = (self.varStrs2 - self.commonVarStrs) if p1 else (self.varStrs1 - self.commonVarStrs)
        b1 = self.enforceTrue(truePoly, trueVarStrs)
        b2 = self.enforceFalse(falsePoly, falseVarStrs)
        if b1 and b2:
            self.isDivergence = True
        return

    def scoringEnforceHardness(self, p: Polynomial):
        numOfFreeDBVars = len(p.dbvarStrs - self.fixedVarStrs)   # larger is better
        numOfSeperateLiterals = len(p.literalStrs - self.commonLiteralStrs)   # larger is better
        numOfSeperateOps = len(p.opStrs - self.commonOpStrs)
        complexity = p.complexity  # smaller is better
        score = complexity * 1.0 / ((1 + numOfFreeDBVars) * (1 + numOfSeperateLiterals) * (1 + numOfSeperateOps) * 1.0)
        return score

    def enforceTrue(self, poly: Polynomial, varStrs: Set[str]):
        if poly.type == "Monomial":
            m = poly.subpolys[0]
            if m.isTrivialTrue is True:
                return True
            if m.isTrivialFalse is True:
                return False
            leftVar = m.varOrTerms[0]
            rightVar = m.varOrTerms[1]
            op = m.operator
            if self.enforceClauseTrue(leftVar, rightVar, op):
                return True
        elif poly.type == "Sum Polynomial":
            scoredPolys = []
            for p in poly.subpolys:
                scoredPolys.append((p, self.scoringEnforceHardness(p)))
            scoredPolys = sorted(scoredPolys, key = lambda x: x[1])
            return self.enforceTrue(scoredPolys[0][0], varStrs)
        elif poly.type == "Product Polynomial":
            for p in poly.subpolys:
                if not self.enforceTrue(p, varStrs):
                    return False
            return True
        return False

    def enforceFalse(self, poly: Polynomial, varStrs: Set[str]):
        if poly.type == "Monomial":
            m = poly.subpolys[0]
            if m.isTrivialTrue is True:
                return False
            if m.isTrivialFalse is True:
                return True
            leftVar = m.varOrTerms[0]
            rightVar = m.varOrTerms[1]
            op = m.operator
            if self.enforceClauseFalse(leftVar, rightVar, op):
                return True
        elif poly.type == "Product Polynomial":
            scoredPolys = []
            for p in poly.subpolys:
                scoredPolys.append((p, self.scoringEnforceHardness(p)))
            scoredPolys = sorted(scoredPolys, key=lambda x: x[1])
            return self.enforceFalse(scoredPolys[0][0], varStrs)
        elif poly.type == "Sum Polynomial":
            for p in poly.subpolys:
                if not self.enforceFalse(p, varStrs):
                    return False
            return True
        return False

    def enforceClauseTrue(self, leftVar: Variable, rightVar: Variable, op: str):
        leftVarStr = leftVar.name_str
        rightVarStr = rightVar.name_str
        if isinstance(leftVar, Variable) and isinstance(rightVar, Variable):
            if self.varStrToValueDic[leftVarStr] is not None and self.varStrToValueDic[rightVarStr] is not None:
                return self.check(self.varStrToValueDic[leftVarStr], self.varStrToValueDic[rightVarStr], op)
            if self.varStrToValueDic[leftVarStr] is None and self.varStrToValueDic[rightVarStr] is None:
                self.varStrToValueDic[rightVarStr] = random.randint(1, 1000)
                self.fixedVarStrs.add(rightVarStr)
            if self.varStrToValueDic[leftVarStr] is not None:
                self.varStrToValueDic[rightVarStr] = self.assignToRight(leftVarStr, self.varStrToValueDic[leftVarStr], op)
                self.fixedVarStrs.add(rightVarStr)
            if self.varStrToValueDic[rightVarStr] is not None:
                self.varStrToValueDic[leftVarStr] = self.assignToLeft(rightVarStr, self.varStrToValueDic[rightVarStr], op)
                self.fixedVarStrs.add(leftVarStr)
            return True
        elif isinstance(leftVar, Term) and isinstance(rightVar, Variable):
            if self.varStrToValueDic[rightVarStr] is not None:
                return False
            leftTermDBValueDic = {}
            leftTermLiteralValueDic = {}
            for DBVarStr in leftVar.dbvarStrs:
                if self.varStrToValueDic[DBVarStr] is not None:
                    leftTermDBValueDic[DBVarStr] = self.varStrToValueDic[DBVarStr]
                else:
                    self.varStrToValueDic[DBVarStr] = random.randint(1, 1000)
                    self.fixedVarStrs.add(DBVarStr)
                    leftTermDBValueDic[DBVarStr] = self.varStrToValueDic[DBVarStr]
            for literalStr in leftVar.literalStrs:
                leftTermLiteralValueDic[literalStr] = self.varStrToValueDic[literalStr]
            termValue = leftVar.evaluate(leftTermDBValueDic, leftTermLiteralValueDic)
            self.varStrToValueDic[rightVarStr] = self.assignToRight(None, termValue, op)
            return True
        elif isinstance(leftVar, Variable) and isinstance(rightVar, Term):
            if self.varStrToValueDic[leftVarStr] is not None:
                return False
            rightTermDBValueDic = {}
            rightTermLiteralValueDic = {}
            for DBVarStr in rightVar.dbvarStrs:
                if self.varStrToValueDic[DBVarStr] is not None:
                    rightTermDBValueDic[DBVarStr] = self.varStrToValueDic[DBVarStr]
                else:
                    self.varStrToValueDic[DBVarStr] = random.randint(1, 1000)
                    self.fixedVarStrs.add(DBVarStr)
                    rightTermDBValueDic[DBVarStr] = self.varStrToValueDic[DBVarStr]
            for literalStr in rightVar.literalStrs:
                rightTermLiteralValueDic[literalStr] = self.varStrToValueDic[literalStr]
            termValue = rightVar.evaluate(rightTermDBValueDic, rightTermLiteralValueDic)
            self.varStrToValueDic[leftVarStr] = self.assignToLeft(None, termValue, op)
            return True
        else:
            return False

    def enforceClauseFalse(self, leftVar, rightVar, op):
        leftVarStr = leftVar.name_str
        rightVarStr = rightVar.name_str
        oppositeOp = self.getOppositeOp(op)
        if isinstance(leftVar, Variable) and isinstance(rightVar, Variable):
            if self.varStrToValueDic[leftVarStr] is not None and self.varStrToValueDic[rightVarStr] is not None:
                return self.check(self.varStrToValueDic[leftVarStr], self.varStrToValueDic[rightVarStr], oppositeOp)
            if self.varStrToValueDic[leftVarStr] is None and self.varStrToValueDic[rightVarStr] is None:
                self.varStrToValueDic[rightVarStr] = random.randint(1, 1000)
                self.fixedVarStrs.add(rightVarStr)
            if self.varStrToValueDic[leftVarStr] is not None:
                self.varStrToValueDic[rightVarStr] = self.assignToRight(leftVarStr, self.varStrToValueDic[leftVarStr], oppositeOp)
                self.fixedVarStrs.add(rightVarStr)
            if self.varStrToValueDic[rightVarStr] is not None:
                self.varStrToValueDic[leftVarStr] = self.assignToLeft(rightVarStr, self.varStrToValueDic[rightVarStr], oppositeOp)
                self.fixedVarStrs.add(leftVarStr)
            return True
        elif isinstance(leftVar, Term) and isinstance(rightVar, Variable):
            if self.varStrToValueDic[rightVarStr] is not None:
                return False
            leftTermDBValueDic = {}
            leftTermLiteralValueDic = {}
            for DBVarStr in leftVar.dbvarStrs:
                if self.varStrToValueDic[DBVarStr] is not None:
                    leftTermDBValueDic[DBVarStr] = self.varStrToValueDic[DBVarStr]
                else:
                    self.varStrToValueDic[DBVarStr] = random.randint(1, 1000)
                    self.fixedVarStrs.add(DBVarStr)
                    leftTermDBValueDic[DBVarStr] = self.varStrToValueDic[DBVarStr]
            for literalStr in leftVar.literalStrs:
                leftTermLiteralValueDic[literalStr] = self.varStrToValueDic[literalStr]
            termValue = leftVar.evaluate(leftTermDBValueDic, leftTermLiteralValueDic)
            self.varStrToValueDic[rightVarStr] = self.assignToRight(None, termValue, oppositeOp)
            return True
        elif isinstance(leftVar, Variable) and isinstance(rightVar, Term):
            if self.varStrToValueDic[leftVarStr] is not None:
                return False
            rightTermDBValueDic = {}
            rightTermLiteralValueDic = {}
            for DBVarStr in rightVar.dbvarStrs:
                if self.varStrToValueDic[DBVarStr] is not None:
                    rightTermDBValueDic[DBVarStr] = self.varStrToValueDic[DBVarStr]
                else:
                    self.varStrToValueDic[DBVarStr] = random.randint(1, 1000)
                    self.fixedVarStrs.add(DBVarStr)
                    rightTermDBValueDic[DBVarStr] = self.varStrToValueDic[DBVarStr]
            for literalStr in rightVar.literalStrs:
                rightTermLiteralValueDic[literalStr] = self.varStrToValueDic[literalStr]
            termValue = rightVar.evaluate(rightTermDBValueDic, rightTermLiteralValueDic)
            self.varStrToValueDic[leftVarStr] = self.assignToLeft(None, termValue, oppositeOp)
            return True
        else:
            return False

    def check(self, value1, value2, op: str):
        assert (op in {"!=", "==", ">", "<", ">=", "<=", "contains", "startsWith", "endsWith", "ncontains", "nstartsWith", "nendsWith"})
        if op == "==":
            return (value1 == value2)
        if op == "!=":
            return (value1 != value2)
        if op == ">":
            return (value1 > value2)
        if op == "<":
            return (value1 < value2)
        if op == ">=":
            return (value1 >= value2)
        if op == "<=":
            return (value1 <= value2)
        if op == "contains":
            if value1 in self.strInt2Literal and value2 in self.strInt2Literal:
                return (self.strInt2Literal[value2] in self.strInt2Literal[value1])
            if value2 in self.strInt2Literal:
                self.strInt2Literal[value1] = self.assignToLeft(self.strInt2Literal[value2], None, op)
            elif value1 not in self.strInt2Literal:
                self.strInt2Literal[value2] = random.choice('ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789')
                self.strInt2Literal[value1] = self.assignToLeft(self.strInt2Literal[value2], None, op)
            else:
                self.strInt2Literal[value2] = self.assignToRight(self.strInt2Literal[value1], None, op)
        if op == "ncontains":
            if value1 in self.strInt2Literal and value2 in self.strInt2Literal:
                return (self.strInt2Literal[value2] not in self.strInt2Literal[value1])
            if value2 in self.strInt2Literal:
                self.strInt2Literal[value1] = self.assignToLeft(self.strInt2Literal[value2], None, op)
            elif value1 not in self.strInt2Literal:
                self.strInt2Literal[value2] = random.choice('ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789')
                self.strInt2Literal[value1] = self.assignToLeft(self.strInt2Literal[value2], None, op)
            else:
                self.strInt2Literal[value2] = self.assignToRight(self.strInt2Literal[value1], None, op)
        if op == "endsWith":
            if value1 in self.strInt2Literal and value2 in self.strInt2Literal:
                return self.strInt2Literal[value1].endswith(self.strInt2Literal[value2])
            if value2 in self.strInt2Literal:
                self.strInt2Literal[value1] = self.assignToLeft(self.strInt2Literal[value2], None, op)
            elif value1 not in self.strInt2Literal:
                self.strInt2Literal[value2] = random.choice('ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789')
                self.strInt2Literal[value1] = self.assignToLeft(self.strInt2Literal[value2], None, op)
            else:
                self.strInt2Literal[value2] = self.assignToRight(self.strInt2Literal[value1], None, op)
        if op == "nendsWith":
            if value1 in self.strInt2Literal and value2 in self.strInt2Literal:
                return (not self.strInt2Literal[value1].endswith(self.strInt2Literal[value2]))
            if value2 in self.strInt2Literal:
                self.strInt2Literal[value1] = self.assignToLeft(self.strInt2Literal[value2], None, op)
            elif value1 not in self.strInt2Literal:
                self.strInt2Literal[value2] = random.choice('ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789')
                self.strInt2Literal[value1] = self.assignToLeft(self.strInt2Literal[value2], None, op)
            else:
                self.strInt2Literal[value2] = self.assignToRight(self.strInt2Literal[value1], None, op)
        if op == "startsWith":
            if value1 in self.strInt2Literal and value2 in self.strInt2Literal:
                return self.strInt2Literal[value1].startswith(self.strInt2Literal[value2])
            if value2 in self.strInt2Literal:
                self.strInt2Literal[value1] = self.assignToLeft(self.strInt2Literal[value2], None, op)
            elif value1 not in self.strInt2Literal:
                self.strInt2Literal[value2] = random.choice('ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789')
                self.strInt2Literal[value1] = self.assignToLeft(self.strInt2Literal[value2], None, op)
            else:
                self.strInt2Literal[value2] = self.assignToRight(self.strInt2Literal[value1], None, op)
        if op == "nstartsWith":
            if value1 in self.strInt2Literal and value2 in self.strInt2Literal:
                return (not self.strInt2Literal[value1].startswith(self.strInt2Literal[value2]))
            if value2 in self.strInt2Literal:
                self.strInt2Literal[value1] = self.assignToLeft(self.strInt2Literal[value2], None, op)
            elif value1 not in self.strInt2Literal:
                self.strInt2Literal[value2] = random.choice('ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789')
                self.strInt2Literal[value1] = self.assignToLeft(self.strInt2Literal[value2], None, op)
            else:
                self.strInt2Literal[value2] = self.assignToRight(self.strInt2Literal[value1], None, op)
        return False

    def getOppositeOp(self, op):
        if op == None:
            return None
        if op == "==":
            return "!="
        if op == "!=":
            return "=="
        if op == ">":
            return "<="
        if op == "<":
            return ">="
        if op == ">=":
            return "<"
        if op == "<=":
            return ">"
        if op.startswith("n"):
            return op.lstrip("n")
        else:
            return "n" + op

    def assignToLeft(self, rightVarStr, rightValue, op):
        if op == "==":
            return rightValue
        if op == "!=":
            if random.randint(0, 1):
                return rightValue + random.randint(1, 1000)
            else:
                return rightValue - random.randint(1, 1000)
        if op == ">":
            return rightValue + random.randint(1, 1000)
        if op == "<":
            return rightValue - random.randint(1, 1000)
        if op == ">=":
            return rightValue + random.randint(0, 1000)
        if op == "<=":
            return rightValue - random.randint(0, 1000)
        if op == "contains":
            return rightVarStr + random.choice('ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789')
            pass
        if op == "ncontains":
            if len(rightVarStr) == 0:
                return None
            if len(rightVarStr) == 1:
                if rightVarStr == "a":
                    return str(random.choice('ABCDEFGHIJKLMNOPQRSTUVWXYZbcdefghijklmnopqrstuvwxyz0123456789'))
                else:
                    return "a"
            else:
                return rightVarStr[0: random.randint(0, len(rightVarStr) - 1)]
        if op == "startsWith":
            return rightVarStr + str(random.choice('ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789'))
        if op == "nstartsWith":
            if len(rightVarStr) == 0:
                return None
            if len(rightVarStr) == 1:
                if rightVarStr == "a":
                    return str(random.choice('ABCDEFGHIJKLMNOPQRSTUVWXYZbcdefghijklmnopqrstuvwxyz0123456789'))
                else:
                    return "a"
            else:
                return rightVarStr[0: random.randint(0, len(rightVarStr) - 1)]
        if op == "endsWith":
            return str(random.choice('ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789')) + rightVarStr
        if op == "nendsWith":
            if len(rightVarStr) == 0:
                return None
            if len(rightVarStr) == 1:
                if rightVarStr == "a":
                    return str(random.choice('ABCDEFGHIJKLMNOPQRSTUVWXYZbcdefghijklmnopqrstuvwxyz0123456789'))
                else:
                    return "a"
            else:
                return rightVarStr[0: random.randint(0, len(rightVarStr) - 1)]
        return None

    def assignToRight(self, leftVarStr, leftValue, op):
        if op == "==":
            return leftValue
        if op == "!=":
            if random.randint(0, 1):
                return leftValue + random.randint(1, 1000)
            else:
                return leftValue - random.randint(1, 1000)
        if op == "<":
            return leftValue + random.randint(1, 1000)
        if op == ">":
            return leftValue - random.randint(1, 1000)
        if op == "<=":
            return leftValue + random.randint(0, 1000)
        if op == ">=":
            return leftValue - random.randint(0, 1000)

        if op == "contains":
            return leftVarStr
        if op == "ncontains":
            return leftVarStr + random.choice('ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789')
        if op == "startsWith":
            if leftVarStr == "":
                return leftVarStr
            else:
                return leftVarStr[0: random.randint(0, len(leftVarStr) - 1)]
        if op == "nstartsWith":
            if leftVarStr == "":
                return None
            else:
                if leftVarStr[0] == "a":
                    return "b" + leftVarStr
                else:
                    return "a" + leftVarStr
        if op == "endsWith":
            if leftVarStr == "":
                return leftVarStr
            else:
                return leftVarStr[random.randint(0, len(leftVarStr - 1)), len(leftVarStr)]
        if op == "nendsWith":
            if leftVarStr == "":
                return None
            else:
                if leftVarStr[-1] == "a":
                    return leftVarStr + "b"
                else:
                    return leftVarStr + "a"
        return None

    def test(self):
        if len(self.varStrs1) < len(self.varStrs2):
            if self.poly1Str == "0":
                trueVarStrs = self.varStrs2 - self.commonVarStrs
                b = self.enforceTrue(self.poly2, trueVarStrs)
                if b:
                    self.isDivergence = True
                return
            elif self.poly1Str == "1":
                falseVarStrs = self.varStrs2 - self.commonVarStrs
                b = self.enforceFalse(self.poly2, falseVarStrs)
                if b:
                    self.isDivergence = True
                return
            else:
                truePoly = self.poly1
                trueVarStrs = (self.varStrs1 - self.commonVarStrs)
                falsePoly = self.poly2
                falseVarStrs = (self.varStrs2 - self.commonVarStrs)
                if self.enforceTrue(truePoly, trueVarStrs):
                    if self.enforceFalse(falsePoly, falseVarStrs):
                        self.isDivergence = True
                        return
                self.clearVarStrToValueDic()
                if self.enforceFalse(truePoly, trueVarStrs):
                    if self.enforceTrue(falsePoly, falseVarStrs):
                        self.isDivergence = True
                        return
        else:
            if self.poly2Str == "0":
                trueVarStrs = self.varStrs1 - self.commonVarStrs
                b = self.enforceTrue(self.poly1, trueVarStrs)
                if b:
                    self.isDivergence = True
                return
            elif self.poly2Str == "1":
                falseVarStrs = self.varStrs1 - self.commonVarStrs
                b = self.enforceFalse(self.poly1, falseVarStrs)
                if b:
                    self.isDivergence = True
                return
            else:
                truePoly = self.poly1
                trueVarStrs = (self.varStrs1 - self.commonVarStrs)
                falsePoly = self.poly2
                falseVarStrs = (self.varStrs2 - self.commonVarStrs)
                if self.enforceFalse(truePoly, trueVarStrs):
                    if self.enforceTrue(falsePoly, falseVarStrs):
                        self.isDivergence = True
                        return
                self.clearVarStrToValueDic()
                if self.enforceTrue(truePoly, trueVarStrs):
                    if self.enforceFalse(falsePoly, falseVarStrs):
                        self.isDivergence = True
                        return
        return
