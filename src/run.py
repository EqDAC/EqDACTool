from Verifier.EqDAC import *


def batchInEqRun():
    print("Eq pairs:")
    for i in range(10):
        file1 = str(i + 1) + "_1.av.json"
        file2 = str(i + 1) + "_2.av.json"
        if pairEqRun(file1, file2) == "EQ":
            print(file1.rstrip(".av.json") + " " + file2.rstrip(".av.json"))
    return


def pairEqRun(file1, file2):
    sa1 = EqDAC(file1)
    sa2 = EqDAC(file2)
    isDivergence = sa1.checkDivergence(sa2.ac.poly)
    if isDivergence is not None:
        if isDivergence is True:
            return "NEQ"
    if sa1.checkIsomorphism(sa2.getCertificate()):
        return "EQ"
    checkResult = sa1.checkBySMT(sa2.getSMTFormula())
    if checkResult == unsat:
        return "EQ"
    else:
        return "NEQ"


def allPairEqRun():
    files = []
    print("Eq pairs:")
    for i in range(10):
        file1 = str(i + 1) + "_1.av.json"
        file2 = str(i + 1) + "_2.av.json"
        files.append(file1)
        files.append(file2)
    for i in range(len(files)):
        for j in range(i + 1, len(files)):
            if pairEqRun(files[i], files[j]) == "EQ":
                print(files[i].rstrip(".av.json") + " " + files[j].rstrip(".av.json"))
    return


if __name__ == "__main__":
    print("Input the pair number of data constraints")
    print("-1: Pairwise batch run. Reason all 45 pairs")
    print("0: Batch run. Reason all 10 pairs (_-1 vs _-2)")
    print("1~10: Decide equivalence of each pair (_-1 vs _-2)")
    while(True):
        idstr = input("Enter a number: ")
        id = int(idstr)
        if id < -1 or id > 10:
            print("The number should >= -1 and <= 10")
            continue
        else:
            if id == 0:
                batchInEqRun()
            elif id == -1:
                allPairEqRun()
            else:
                file1 = str(id) + "_1.av.json"
                file2 = str(id) + "_2.av.json"
                print(pairEqRun(file1, file2))
            break
