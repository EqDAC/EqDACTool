import os
import json
import copy
from Util.config import *

# Acyclic graph
class ruleGraph:
    ruleFile = None
    original_AST = None
    label = None

    # label each node by a unique integer
    labeled_AST = None

    # map an integer(ID) to the node
    nodeLabels = None

    # map the integer(ID) to the top-level node
    topNodeLabels = None

    def __init__(self, p_ruleFile):
        self.ruleFile = p_ruleFile
        self.label = 1
        self.nodeLabels = {}
        self.topNodeLabels = {}
        self.generateAST()
        self.labelAST()
        return

    def importRule(self):
        assert (self.ruleFile is not None)
        self.file = open(rule_path + self.ruleFile, 'r')
        lines = self.file.readlines()
        ruleStr = ""
        for line in lines:
            if line.find("//") == -1:
                ruleStr = ruleStr + line.strip("\n")
        return ruleStr

    def generateAST(self):
        assert(self.ruleFile is not None)
        # ruleStr = self.importRule()
        # jsonFileName = self.ruleFile + '.json'
        # os.system("node " + esprima_path + 'ast_generator.js ' + ast_path + jsonFileName + ' ' + '\'' + ruleStr + '\' > /dev/null')
        self.loadAST()
        return

    def loadAST(self):
        assert(self.ruleFile is not None)
        self.original_AST = json.load(open(ast_path + self.ruleFile))
        return

    def labelAST(self):
        assert(self.ruleFile is not None)
        assert(self.original_AST is not None)
        self.labeled_AST = copy.deepcopy(self.original_AST)
        self.recLabelAST(self.labeled_AST)
        # labeled_AST_data = json.dumps(self.labeled_AST, sort_keys=False, indent=4, separators=(',', ': '))
        # with open(labeled_ast_path + "labeled_" + self.ruleFile + ".json", "w") as outfile:
        #     outfile.write(labeled_AST_data)
        return
    
    def recLabelAST(self, singleAST):
        self.label = self.label + 1
        if singleAST is None:
            return
        singleAST["astlabel"] = self.label
        assert(self.label not in self.nodeLabels)
        self.nodeLabels[self.label] = singleAST
        if singleAST["type"] == "MemberExpression":
            self.recLabelAST(singleAST["object"])
            self.recLabelAST(singleAST["property"])
        elif singleAST["type"] == "Program":
            for subSingleAST in singleAST["body"]:
                self.topNodeLabels[self.label + 1] = subSingleAST
                self.recLabelAST(subSingleAST)
        elif singleAST["type"] == "ExpressionStatement":
            self.recLabelAST(singleAST["expression"])
        elif singleAST["type"] in {"BinaryExpression", "LogicalExpression", "AssignmentExpression"}:
            self.recLabelAST(singleAST["left"])
            self.recLabelAST(singleAST["right"])
        elif singleAST["type"] == "IfStatement":
            self.recLabelAST(singleAST["test"])
            self.recLabelAST(singleAST["consequent"])
            self.recLabelAST(singleAST["alternate"])
        elif singleAST["type"] == "Identifier":
            return
        elif singleAST["type"] == "UnaryExpression":
            self.recLabelAST(singleAST["argument"])
        elif singleAST["type"] == "BlockStatement":
            for subSingleAST in singleAST["body"]:
                self.recLabelAST(subSingleAST)
        elif singleAST["type"] == "ArrayExpression":
            for subSingleAST in singleAST["elements"]:
                self.recLabelAST(subSingleAST)
        elif singleAST["type"] == "CallExpression":
            if singleAST["callee"]["type"] == "MemberExpression":
                if singleAST["callee"]["property"]["name"] in {"startsWith", "endsWith", "contains"} and singleAST["callee"]["object"]["name"] == "string":
                    for subSingleAST in singleAST["arguments"]:
                        self.recLabelAST(subSingleAST)
        return
