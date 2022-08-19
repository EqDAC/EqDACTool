class Variable:
    name = None
    name_str = None
    isDBVar = None
    isLiteral = None

    def __init__(self, expr):
        self.name = []
        self.isDBVar = False
        self.isLiteral = False
        self.constructName(expr)
        self.type = True if len(self.name) > 1 else False
        return

    def constructName(self, expr):
        if expr["type"] == "MemberExpression":
            if "name" in expr["property"]:
                self.isDBVar = True
                self.name.insert(0, expr["property"]["name"])
                self.constructName(expr["object"])
        elif expr["type"] == "Identifier":
            if "name" in expr:
                self.name.insert(0, expr["name"])
        elif expr["type"] == "Literal":
            if "raw" in expr:
                self.isLiteral = True
                self.name.insert(0, expr["raw"])
        return

    def toString(self):
        if self.name_str is None:
            self.name_str = ""
            for token in self.name:
                self.name_str = self.name_str + token + "."
            self.name_str = self.name_str.rstrip('.')
        return self.name_str

    def printVariable(self):
        print(self.toString())
        return

    def isEqual(self, p_varTerm):
        return self.toString() == p_varTerm.toString()
