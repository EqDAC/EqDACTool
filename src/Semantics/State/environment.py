from Semantics.State.polynomial import *

class VarEnv:
    # map an integer(ID) to a variable
    varIDs = None

    # map the ID of an boolean artificial/DBVariable variable to its value {(dbval/literal/polynomial, polynomial)}
    # the value can be a database variable, a literal, or a boolean value
    BoolVarVal = None
    NonBoolVarVal = None

    def __init__(self):
        self.varIDs = {}
        self.BoolVarVal = {}
        self.NonBoolVarVal = {}
        return

    def putVarID(self, id, varTerm):
        self.varIDs[id] = varTerm
        return

    def getVarID(self, varTerm):
        for id in self.varIDs:
            if varTerm.isEqual(self.varIDs[id]):
                return id
        return None

    def getVarByID(self, varID):
        if varID in self.varIDs:
            return self.varIDs[varID]
        return None

    def putBoolValue(self, varID, p_poly):
        if varID not in self.BoolVarVal:
            self.BoolVarVal[varID] = p_poly
        else:
            self.BoolVarVal[varID] = Polynomial("+", [self.BoolVarVal[varID], p_poly])

    def getBoolValue(self, varID):
        if varID in self.BoolVarVal:
            return self.BoolVarVal[varID]
        return None

    def putNonBoolValueByDBVar(self, varID, DBVarID, p_poly):
        if varID not in self.NonBoolVarVal:
            self.NonBoolVarVal[varID] = {}
            self.NonBoolVarVal[varID][DBVarID] = p_poly
        else:
            if DBVarID not in self.NonBoolVarVal[varID]:
                self.NonBoolVarVal[varID][DBVarID] = p_poly
            else:
                self.NonBoolVarVal[varID][DBVarID] = Polynomial("+", [self.NonBoolVarVal[varID][DBVarID], p_poly])
        return

    def putNonBoolValueByNonDBVar(self, varID, NonDBVarID, p_poly):
        if varID in self.BoolVarVal:
            not_p_poly = deepcopy(p_poly)
            not_p_poly.notPoly()
            for DBVarID in self.BoolVarVal[varID]:
                self.BoolVarVal[varID][DBVarID] = Polynomial("*", [self.BoolVarVal[varID][DBVarID], not_p_poly])
        val_polys = deepcopy(self.NonBoolVarVal[NonDBVarID])
        for DBVarID in val_polys:
            val_polys[DBVarID] = Polynomial("*", [val_polys[DBVarID], p_poly])
            self.putNonBoolValueByDBVar(varID, DBVarID, val_polys[DBVarID])
        return

    def getNonBoolValue(self, varID):
        if varID in self.NonBoolVarVal:
            return self.NonBoolVarVal[varID]
        return None


class PredicateEnv:
    # map the ID of a predicate to its value (polynomial)
    # where the ID is the ID of the predicate node in the AST
    predVal = None

    def __init__(self):
        self.predVal = {}
        return

    def putValue(self, predID, p_poly):
        assert(predID not in self.predVal)
        self.predVal[predID] = p_poly
        return

    def getValue(self, predID):
        if predID in self.predVal:
            return self.predVal[predID]
        else:
            return None


class IteEnv:
    # map the ID of a branch and a ite expr/statement to its value (polynomial)
    # where the ID is the ID of the predicate node in the AST
    iteVal = None

    def __init__(self):
        self.iteVal = {}
        return

    def putValue(self, iteID, p_poly):
        if iteID not in self.iteVal:
            self.iteVal[iteID] = p_poly
        else:
            self.iteVal[iteID] = Polynomial("*", [self.iteVal[iteID], p_poly])
        return

    def getValue(self, iteID):
        if iteID in self.iteVal:
            return self.iteVal[iteID]
        else:
            return None
