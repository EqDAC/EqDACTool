from Semantics.State.environment import *
from Semantics.State.polynomial import *
from Semantics.State.variable import *

def uniqueVarAppend(varList, var):
    for item in varList:
        if var.toString() == item.toString():
            return
    varList.append(var)
    return


def getVarIndex(varList, var):
    index = 0
    for item in varList:
        if var.toString() == item.toString():
            return index
        index = index + 1
    return -1


class AlgebraicConstructor:
    # ingredient
    nodeLabels = None
    topNodeLabels = None
    skipset = None

    # core algebraic constructs
    m_VarEnv = None
    m_PredicateEnv = None
    m_IteEnv = None
    m_DBVars = None
    m_NonDBVars = None
    m_Literals = None

    # algebraic representation
    poly = None
    invDBVars = []

    def __init__(self, p_nodeLabels, p_topNodeLabels):
        self.nodeLabels = p_nodeLabels
        self.topNodeLabels = p_topNodeLabels
        self.skipset = set([])
        self.m_VarEnv = VarEnv()
        self.m_PredicateEnv = PredicateEnv()
        self.m_IteEnv = IteEnv()
        self.m_Terms = {}
        self.m_DBVars = []
        self.m_NonDBVars = []
        self.m_Literals = []
        self.poly = Polynomial("()", [Monomial([], None, True, False)])
        return

    def extractVarLiteral(self):
        for i in self.nodeLabels:
            if i in self.skipset:
                continue
            if self.nodeLabels[i]["type"] == "MemberExpression":
                self.updateSkipSetByMemberExpression(self.nodeLabels[i])
                self.createDBVariable(self.nodeLabels[i])
            elif self.nodeLabels[i]["type"] == "AssignmentExpression":
                uniqueVarAppend(self.m_NonDBVars, Variable(self.nodeLabels[i]["left"]))
                self.skipset.add(self.nodeLabels[i]["left"]["astlabel"])
            elif self.nodeLabels[i]["type"] == "Identifier":
                self.createLiteral(self.nodeLabels[i])
            elif self.nodeLabels[i]["type"] == "Literal":
                self.createLiteral(self.nodeLabels[i])

        self.computeInvDBVars()
        id = 0
        for var in self.m_DBVars:
            self.m_VarEnv.putVarID(id, var)
            poly_one = Polynomial("()", [Monomial([], None, True, False)])
            self.m_VarEnv.putNonBoolValueByDBVar(id, id, poly_one)
            id = id + 1
        for var in self.m_NonDBVars:
            self.m_VarEnv.putVarID(id, var)
            id = id + 1
        for var in self.m_Literals:
            self.m_VarEnv.putVarID(id, var)
            poly_one = Polynomial("()", [Monomial([], None, True, False)])
            self.m_VarEnv.putNonBoolValueByDBVar(id, id, poly_one)
            id = id + 1
        return

    def transform(self):
        for i in self.topNodeLabels:
            if self.nodeLabels[i]["type"] == "ExpressionStatement":
                expr = self.nodeLabels[i]["expression"]
                if expr["type"] == "BinaryExpression":
                    self.handleBinaryExpression(expr)
                    subpoly = self.m_PredicateEnv.getValue(expr["astlabel"])
                    self.poly = Polynomial("*", [self.poly, subpoly])
                elif expr["type"] == "LogicalExpression":
                    self.handleLogicalExpression(expr)
                    subpoly = self.m_PredicateEnv.getValue(expr["astlabel"])
                    self.poly = Polynomial("*", [self.poly, subpoly])
                elif expr["type"] == "AssignmentExpression":
                    self.handleAssignmentExpression(expr)
                elif expr["type"] == "CallExpression":
                    if expr["callee"]["type"] == "MemberExpression":
                        if expr["callee"]["property"]["name"] == "startsWith" and expr["callee"]["object"]["name"] == "string":
                            self.handleStringCallExpression(expr)
                            subpoly = self.m_PredicateEnv.getValue(expr["astlabel"])
                            self.poly = Polynomial("*", [self.poly, subpoly])
            elif self.nodeLabels[i]["type"] == "IfStatement":
                self.handleIfStatement(self.nodeLabels[i])
                ite_poly = self.m_IteEnv.getValue(self.nodeLabels[i]["astlabel"])
                if ite_poly != None:
                    self.poly = Polynomial("*", [self.poly, ite_poly])
        self.poly.simplify()
        return

    def updateSkipSetByMemberExpression(self, astNode):
        self.skipset.add(astNode["astlabel"])
        self.skipset.add(astNode["property"]["astlabel"])
        if astNode["object"]["type"] == "Identifier":
            self.skipset.add(astNode["object"]["astlabel"])
        elif astNode["object"]["type"] == "MemberExpression":
            self.updateSkipSetByMemberExpression(astNode["object"])
        return

    def createDBVariable(self, memberExpression):
        uniqueVarAppend(self.m_DBVars, Variable(memberExpression))
        return

    def createLiteral(self, astNode):
        var = Variable(astNode)
        isNonDBVar = False
        for NonDBVar in self.m_NonDBVars:
            if NonDBVar.toString() == var.toString():
                isNonDBVar = True
                break
        if not isNonDBVar:
            uniqueVarAppend(self.m_Literals, Variable(astNode))
        return

    def getVariableByNode(self, astNode):
        if astNode["type"] == "MemberExpression":
            tmpVar = Variable(astNode)
            index = getVarIndex(self.m_DBVars, tmpVar)
            return self.m_DBVars[index]
        elif astNode["type"] == "Literal":
            tmpLiteral = Variable(astNode)
            index = getVarIndex(self.m_Literals, tmpLiteral)
            return self.m_Literals[index]
        else:
            tmpVar = Variable(astNode)
            index = getVarIndex(self.m_NonDBVars, tmpVar)
            if index == -1:
                index = getVarIndex(self.m_Literals, tmpVar)
                return self.m_Literals[index]
            else:
                return self.m_NonDBVars[index]

    def handleBinaryExpression(self, astNode, condpoly = Polynomial("()", [Monomial([], None, True, False)])):
        leftNode = astNode["left"]
        rightNode = astNode["right"]
        op = astNode["operator"]
        assert(leftNode["type"] in {"MemberExpression", "Identifier", "Literal", "BinaryExpression"})
        assert(rightNode["type"] in {"MemberExpression", "Identifier", "Literal", "ArrayExpression", "BinaryExpression"})
        assert(op in {"!=", "==", ">", "<", ">=", "<=", "in", "+", "-", "*", "/", "%"})

        if op in {"+", "-", "*", "/", "%"}:
            leftTerm = None
            rightTerm = None
            if leftNode["type"] == "MemberExpression":
                tmpVar = Variable(leftNode)
                index = getVarIndex(self.m_DBVars, tmpVar)
                leftTerm = self.m_DBVars[index]
            elif leftNode["type"] == "Literal":
                tmpLiteral = Variable(leftNode)
                index = getVarIndex(self.m_Literals, tmpLiteral)
                leftTerm = self.m_Literals[index]
            elif leftNode["type"] == "BinaryExpression":
                self.handleBinaryExpression(leftNode, condpoly)
                leftTerm = self.m_Terms[leftNode["astlabel"]]
            if rightNode["type"] == "MemberExpression":
                tmpVar = Variable(rightNode)
                index = getVarIndex(self.m_DBVars, tmpVar)
                rightTerm = self.m_DBVars[index]
            elif rightNode["type"] == "Literal":
                tmpLiteral = Variable(rightNode)
                index = getVarIndex(self.m_Literals, tmpLiteral)
                rightTerm = self.m_Literals[index]
            elif rightNode["type"] == "BinaryExpression":
                self.handleBinaryExpression(rightNode, condpoly)
                rightTerm = self.m_Terms[rightNode["astlabel"]]
            t = Term([leftTerm, rightTerm], op)
            self.m_Terms[astNode["astlabel"]] = t
            return

        if op not in {"in"}:
            if leftNode["type"] == "BinaryExpression" and rightNode["type"] == "BinaryExpression":
                self.handleBinaryExpression(leftNode, condpoly)
                self.handleBinaryExpression(rightNode, condpoly)
                leftTerm = self.m_Terms[leftNode["astlabel"]]
                rightTerm = self.m_Terms[rightNode["astlabel"]]
                self.m_PredicateEnv.putValue(astNode["astlabel"],
                                             Polynomial("()", [Monomial([leftTerm, rightTerm], op, False, False)]))
                return
            if leftNode["type"] == "BinaryExpression" and rightNode["type"] != "BinaryExpression":
                self.handleBinaryExpression(leftNode, condpoly)
                leftTerm = self.m_Terms[leftNode["astlabel"]]
                varID2 = self.m_VarEnv.getVarID(self.getVariableByNode(rightNode))
                val2_polys = self.m_VarEnv.getNonBoolValue(varID2)
                m = Monomial([], None, False, True)
                sum_poly = Polynomial("()", [m])
                for DBVarID2 in val2_polys:
                    subpoly2 = deepcopy(val2_polys[DBVarID2])
                    var2 = self.m_VarEnv.getVarByID(DBVarID2)
                    vars = [leftTerm, var2]
                    subpoly3 = Polynomial("()", [Monomial(vars, op, False, False)])
                    poly = Polynomial("*", [subpoly2, subpoly3])
                    sum_poly = Polynomial("+", [poly, sum_poly])
                self.m_PredicateEnv.putValue(astNode["astlabel"], Polynomial("*", [condpoly, sum_poly]))
                return
            if leftNode["type"] != "BinaryExpression" and rightNode["type"] == "BinaryExpression":
                self.handleBinaryExpression(rightNode, condpoly)
                rightTerm = self.m_Terms[rightNode["astlabel"]]
                varID1 = self.m_VarEnv.getVarID(self.getVariableByNode(leftNode))
                val1_polys = self.m_VarEnv.getNonBoolValue(varID1)
                m = Monomial([], None, False, True)
                sum_poly = Polynomial("()", [m])
                for DBVarID1 in val1_polys:
                    subpoly1 = deepcopy(val1_polys[DBVarID1])
                    var1 = self.m_VarEnv.getVarByID(DBVarID1)
                    vars = [var1, rightTerm]
                    subpoly2 = Polynomial("()", [Monomial(vars, op, False, False)])
                    poly = Polynomial("*", [subpoly1, subpoly2])
                    sum_poly = Polynomial("+", [poly, sum_poly])
                self.m_PredicateEnv.putValue(astNode["astlabel"], Polynomial("*", [condpoly, sum_poly]))
                return
            varID1 = self.m_VarEnv.getVarID(self.getVariableByNode(leftNode))
            varID2 = self.m_VarEnv.getVarID(self.getVariableByNode(rightNode))
            val1_polys = self.m_VarEnv.getNonBoolValue(varID1)
            val2_polys = self.m_VarEnv.getNonBoolValue(varID2)
            m = Monomial([], None, False, True)
            sum_poly = Polynomial("()", [m])
            for DBVarID1 in val1_polys:
                for DBVarID2 in val2_polys:
                    subpoly1 = deepcopy(val1_polys[DBVarID1])
                    subpoly2 = deepcopy(val2_polys[DBVarID2])
                    var1 = self.m_VarEnv.getVarByID(DBVarID1)
                    var2 = self.m_VarEnv.getVarByID(DBVarID2)
                    vars = [var1, var2]
                    subpoly3 = Polynomial("()", [Monomial(vars, op, False, False)])
                    poly = Polynomial("*", [subpoly1, subpoly2, subpoly3])
                    sum_poly = Polynomial("+", [poly, sum_poly])
            self.m_PredicateEnv.putValue(astNode["astlabel"], Polynomial("*", [condpoly, sum_poly]))
        else:
            # Assume that in operator only check string variables
            varID1 = self.m_VarEnv.getVarID(self.getVariableByNode(leftNode))
            assert(rightNode["type"] in {"ArrayExpression"})
            val1_polys = self.m_VarEnv.getNonBoolValue(varID1)
            LSumPolys = []
            for literalElem in rightNode["elements"]:
                varID2 = self.m_VarEnv.getVarID(self.getVariableByNode(literalElem))
                val2_polys = self.m_VarEnv.getNonBoolValue(varID2)
                m = Monomial([], None, False, True)
                sum_poly = Polynomial("()", [m])
                for DBVarID1 in val1_polys:
                    for DBVarID2 in val2_polys:
                        subpoly1 = deepcopy(val1_polys[DBVarID1])
                        subpoly2 = deepcopy(val2_polys[DBVarID2])
                        var1 = self.m_VarEnv.getVarByID(DBVarID1)
                        var2 = self.m_VarEnv.getVarByID(DBVarID2)
                        vars = [var1, var2]
                        subpoly3 = Polynomial("()", [Monomial(vars, "==", False, False)])
                        poly = Polynomial("*", [subpoly1, subpoly2, subpoly3])
                        sum_poly = Polynomial("+", [poly, sum_poly])
                LSumPolys.append(sum_poly)
            LSumPoly = Polynomial("+", LSumPolys)
            self.m_PredicateEnv.putValue(astNode["astlabel"], Polynomial("*", [condpoly, LSumPoly]))
            return
        return

    def handleStringCallExpression(self, astNode, condpoly = Polynomial("()", [Monomial([], None, True, False)])):
        assert(len(astNode["arguments"]) == 2)
        leftNode = astNode["arguments"][0]
        rightNode = astNode["arguments"][1]
        op = astNode["callee"]["property"]["name"]
        assert(leftNode["type"] in {"MemberExpression", "Identifier", "Literal"})
        assert(rightNode["type"] in {"MemberExpression", "Identifier", "Literal", "ArrayExpression"})
        assert(op in {"contains", "startsWith", "endsWith"})
        varID1 = self.m_VarEnv.getVarID(self.getVariableByNode(leftNode))
        varID2 = self.m_VarEnv.getVarID(self.getVariableByNode(rightNode))
        val1_polys = self.m_VarEnv.getNonBoolValue(varID1)
        val2_polys = self.m_VarEnv.getNonBoolValue(varID2)
        m = Monomial([], None, False, True)
        sum_poly = Polynomial("()", [m])
        for DBVarID1 in val1_polys:
            for DBVarID2 in val2_polys:
                subpoly1 = deepcopy(val1_polys[DBVarID1])
                subpoly2 = deepcopy(val2_polys[DBVarID2])
                var1 = self.m_VarEnv.getVarByID(DBVarID1)
                var2 = self.m_VarEnv.getVarByID(DBVarID2)
                vars = [var1, var2]
                subpoly3 = Polynomial("()", [Monomial(vars, op, False, False)])
                poly = Polynomial("*", [subpoly1, subpoly2, subpoly3])
                sum_poly = Polynomial("+", [poly, sum_poly])
        self.m_PredicateEnv.putValue(astNode["astlabel"], Polynomial("*", [condpoly, sum_poly]))
        return

    def handleLogicalExpression(self, astNode, condpoly = Polynomial("()", [Monomial([], None, True, False)])):
        assert(astNode["operator"] in {"&&", "||"})
        assert(astNode["left"]["type"] in {"BinaryExpression", "LogicalExpression", "Identifier", "CallExpression"})
        assert (astNode["right"]["type"] in {"BinaryExpression", "LogicalExpression", "Identifier", "CallExpression"})
        if astNode["left"]["type"] == "BinaryExpression":
            self.handleBinaryExpression(astNode["left"])
        elif astNode["left"]["type"] == "CallExpression":
            self.handleStringCallExpression(astNode["left"])
        elif astNode["left"]["type"] == "LogicalExpression":
            self.handleLogicalExpression(astNode["left"])
        else:
            pass

        if astNode["right"]["type"] == "BinaryExpression":
            self.handleBinaryExpression(astNode["right"])
        elif astNode["right"]["type"] == "CallExpression":
            self.handleStringCallExpression(astNode["right"])
        elif astNode["right"]["type"] == "LogicalExpression":
            self.handleLogicalExpression(astNode["right"])
        else:
            pass

        if astNode["left"]["type"] == "Identifier":
            varID = self.m_VarEnv.getVarID(Variable(astNode["left"]))
            left_poly = self.m_VarEnv.getBoolValue(varID)
        else:
            left_poly = self.m_PredicateEnv.getValue(astNode["left"]["astlabel"])
        if astNode["right"]["type"] == "Identifier":
            varID = self.m_VarEnv.getVarID(Variable(astNode["right"]))
            right_poly = self.m_VarEnv.getBoolValue(varID)
        else:
            right_poly = self.m_PredicateEnv.getValue(astNode["right"]["astlabel"])

        if astNode["operator"] == "&&":
            poly = Polynomial("*", [left_poly, right_poly])
            self.m_PredicateEnv.putValue(astNode["astlabel"], Polynomial("*", [poly, condpoly]))
        else:
            poly = Polynomial("+", [left_poly, right_poly])
            self.m_PredicateEnv.putValue(astNode["astlabel"], Polynomial("*", [poly, condpoly]))
        return

    def handleAssignmentExpression(self, astNode, condpoly = Polynomial("()", [Monomial([], None, True, False)])):
        assert(astNode["right"]["type"] in {"BinaryExpression", "LogicalExpression", "MemberExpression", "Identifier"})
        varID = self.m_VarEnv.getVarID(Variable(astNode["left"]))
        if astNode["right"]["type"] == "BinaryExpression":
            self.handleBinaryExpression(astNode["right"])
            poly = Polynomial("*", [self.m_PredicateEnv.getValue(astNode["right"]["astlabel"]), condpoly])
            self.m_VarEnv.putBoolValue(varID, poly)
        elif astNode["right"]["type"] == "LogicalExpression":
            self.handleLogicalExpression(astNode["right"])
            poly = Polynomial("*", [self.m_PredicateEnv.getValue(astNode["right"]["astlabel"]), condpoly])
            self.m_VarEnv.putBoolValue(varID, poly)
        elif astNode["right"]["type"] == "MemberExpression":
            DBVarID = self.m_VarEnv.getVarID(Variable(astNode["right"]))
            self.m_VarEnv.putNonBoolValueByDBVar(varID, DBVarID, condpoly)
        elif astNode["right"]["type"] == "Identifier":
            NonDBVarID = self.m_VarEnv.getVarID(Variable(astNode["right"]))
            self.m_VarEnv.putNonBoolValueByNonDBVar(varID, NonDBVarID, condpoly)
        return

    def handleIfStatement(self, node, condpoly = Polynomial("()", [Monomial([], None, True, False)])):
        self.handleTestInIfStatement(node["test"], condpoly)
        poly = self.m_PredicateEnv.getValue(node["test"]["astlabel"])
        tbr_entry_poly = deepcopy(poly)
        fbr_entry_poly = deepcopy(poly)
        fbr_entry_poly.notPoly()
        if node["consequent"] is not None:
            self.handleBranchInIfStatement(node["consequent"], Polynomial("*", [tbr_entry_poly, condpoly]))
        if node["alternate"] is not None:
            self.handleBranchInIfStatement(node["alternate"], Polynomial("*", [fbr_entry_poly, condpoly]))
        if node["consequent"] is not None:
            tbr_poly = self.m_IteEnv.getValue(node["consequent"]["astlabel"])
        else:
            tbr_poly = None
        if node["alternate"] is not None:
            fbr_poly = self.m_IteEnv.getValue(node["alternate"]["astlabel"])
        else:
            fbr_poly = None
        if tbr_poly != None and fbr_poly == None:
            self.m_IteEnv.putValue(node["astlabel"], tbr_poly)
        elif tbr_poly == None and fbr_poly != None:
            self.m_IteEnv.putValue(node["astlabel"], fbr_poly)
        elif tbr_poly != None and fbr_poly != None:
            self.m_IteEnv.putValue(node["astlabel"], Polynomial("+", [tbr_poly, fbr_poly]))
        return

    def handleTestInIfStatement(self, testExpr, condpoly = Polynomial("()", [Monomial([], None, True, False)])):
        if testExpr["type"] == "BinaryExpression":
            self.handleBinaryExpression(testExpr, condpoly)
        elif testExpr["type"] == "LogicalExpression":
            self.handleLogicalExpression(testExpr, condpoly)
        elif testExpr["type"] == "CallExpression":
            self.handleStringCallExpression(testExpr, condpoly)
        return

    def handleBranchInIfStatement(self, branch, condpoly):
        assert(branch["type"] == "BlockStatement")
        for astNode in branch["body"]:
            if astNode["type"] == "ExpressionStatement":
                expr = astNode["expression"]
                if expr["type"] == "BinaryExpression":
                    self.handleBinaryExpression(expr, condpoly)
                    subpoly = self.m_PredicateEnv.getValue(expr["astlabel"])
                    self.m_IteEnv.putValue(branch["astlabel"], subpoly)
                elif expr["type"] == "LogicalExpression":
                    self.handleLogicalExpression(expr, condpoly)
                    subpoly = self.m_PredicateEnv.getValue(expr["astlabel"])
                    self.m_IteEnv.putValue(branch["astlabel"], subpoly)
                elif expr["type"] == "AssignmentExpression":
                    self.handleAssignmentExpression(expr, condpoly)
                elif expr["type"] == "CallExpression":
                    if expr["callee"]["type"] == "MemberExpression":
                        if expr["callee"]["property"]["name"] == "startsWith" and expr["callee"]["object"]["name"] == "string":
                            self.handleStringCallExpression(expr, condpoly)
                            subpoly = self.m_PredicateEnv.getValue(expr["astlabel"])
                            self.m_IteEnv.putValue(branch["astlabel"], subpoly)
            elif astNode["type"] == "IfStatement":
                self.handleIfStatement(astNode, condpoly)
                br_poly = self.m_IteEnv.getValue(branch["astlabel"])
                if br_poly != None:
                    self.m_IteEnv.iteVal[branch["astlabel"]] = Polynomial(br_poly, self.m_IteEnv.getValue(astNode["astlabel"]))
        return

    def computeInvDBVars(self):
        self.invDBVars = []
        for DBVar in self.m_DBVars:
            self.invDBVars.append(DBVar.toString())
        return
