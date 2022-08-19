class litencode:
    poly1 = None
    poly2 = None
    literalCluster = None
    literalToIntMap = None
    upperInt = None

    def __init__(self, p_poly1, p_poly2):
        self.poly1 = p_poly1
        self.poly2 = p_poly2
        self.literalCluster = []
        self.literalToIntMap = {}
        self.upperInt = 0
        self.compute()

    def compute(self):
        self.scanPolynomial(self.poly1)
        self.scanPolynomial(self.poly2)
        self.computeLiteralToIntMap()
        return

    def scanPolynomial(self, poly):
        if poly.type == "Monomial":
            cluster = set([])
            for p_subpoly in poly.subpolys:
                literalVars = p_subpoly.literalStrs
                cluster = cluster.union(literalVars)
            self.literalCluster.append(cluster)
        elif poly.type == "Sum Polynomial":
            cluster = set([])
            for p_subpoly in poly.subpolys:
                if p_subpoly.type == "Monomial":
                    literalVars = p_subpoly.subpolys[0].literalStrs
                    cluster = cluster.union(literalVars)
                else:
                    self.scanPolynomial(p_subpoly)
            self.literalCluster.append(cluster)
        elif poly.type == "Product Polynomial":
            for p_subpoly in poly.subpolys:
                self.scanPolynomial(p_subpoly)
        return

    def computeLiteralToIntMap(self):
        self.literalCluster = sorted(self.literalCluster, key=lambda cluster: len(cluster), reverse=True)
        for cluster in self.literalCluster:
            literalInCluster = []
            for literal in cluster:
                if literal not in self.literalToIntMap:
                    literalInCluster.append(literal)
            for literal in literalInCluster:
                self.literalToIntMap[literal] = self.upperInt
                self.upperInt += 1
        return




