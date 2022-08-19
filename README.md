# EqDAC

## Overview

*EqDAC* (Equivalent Verification of Data Constraints) is a decision procedure supporting the equivalence verification of data constraints in FinTech systems. Currently, it supports data constraint maintenance in a global financial technology company. 

## Basic Modules
The source code of *EqDAC* consists of five modules as follows.

- Utility: Invoke the parser to generate the AST of a data constraint.
-  Semantics: The semantic representation of a data constraint
   - State: Construct the symbolic state where the property abstracts the data constraint semantics.
   - Symbolic: Construct the symbolic representation, i.e., a FOL formula.
-  Verifier: The component of the decision procedure
   - Divergence: The divergence analyzer generates concrete values to refute the equivalence.
   - Isomorphism: Isomorphism analyzer leverages the tree isomorphism algorithm to prove the equivalence.

## Examples of Data Constraints

We evaluate *EqDAC* upon the data constraints in company A. Due to the commercial use, we do not release the original set of data constraints and provide 20 typical data constraints as examples. In addition, all the data constraints have been desensitized and encrypted to avoid the leakage of any Personal Identifiable Information. 

We simplify original data constraints and extract typical statements to make the pattern clear and intuitive. A data constraint used in the production can contain more statements composed of different examples.

Overall, we provide nine pairs of equivalent data constraints and a pair of non-equivalent ones. They cover the commonly-existed program constructs of data constraints and show the typical patterns of equivalent and non-equivalent pairs.
Specifically, the data constraints in the file `n_1.av` and `n_2.av` are equivalents, where n is not equal to 8. Except for (7_1, 7_2), the other eight equivalent pairs can be proved by the isomorphism analysis. We have discussed the pair (7_1, 7_2) in the case study of our paper.

Lastly, the numbers of different patterns in the set of examples do not reflect the proportion in the original data constraint set of the company. Therefore, we just present them to demonstrate the capability of each stage in *EqDAC*.

## How to Run

Before you run *EqDAC*, REMEMBER to configure the `root_path` in the file `src/Util/config.py,` which should be specified as the absolute path of the root directory of *EqDAC*.
If you want to analyze your data constraints, make sure you download the library [*esprima*](https://github.com/jquery/esprima) in the third party's directory, parses a data constraint, and generate the ASTs. 
Currently, we have generated all the ASTs of sample data constraints.
You can load the ASTs directly to have a quick start.

The file `run.py` provides three modes of running the prototype. You can verify all the ten pairs of data constraints in a single run by specifying the integer 0. Also, you can test each case by setting the ID, which ranges from 1 to 10. Finally, if you want to try the data constraint indexing, you can enter -1 to start the indexing.

**Running Example 1**
```
➜ python run.py
Input the pair number of data constraints
-1: Pairwise batch run. Reason all 45 pairs
0: Batch run. Reason all ten pairs (_-1 vs _-2)
1~10: Decide the equivalence of each pair (_-1 vs _-2)
Enter a number: 1
EQ
```

**Running Example 2**
```
➜ python run.py
Input the pair number of data constraints
-1: Pairwise batch run. Reason all 45 pairs
0: Batch run. Reason all 10 pairs (_-1 vs _-2)
1~10: Decide the equivalence of each pair (_-1 vs _-2)
Enter a number: 0
Eq pairs:
1_1 1_2
2_1 2_2
3_1 3_2
4_1 4_2
5_1 5_2
6_1 6_2
7_1 7_2
9_1 9_2
10_1 10_2
```

**Running Example 3**
```
➜ python run.py
Input the pair number of data constraints
-1: Pairwise batch run. Reason all 45 pairs
0: Batch run. Reason all 10 pairs (_-1 vs _-2)
1~10: Decide the equivalence of each pair (_-1 vs _-2)
Enter a number: -1
Eq pairs:
1_1 1_2
2_1 2_2
3_1 3_2
4_1 4_2
5_1 5_2
6_1 6_2
7_1 7_2
9_1 9_2
10_1 10_2
```

## Feedback

Please file an issue for bugs/issues/questions/feature requests. We are always happy to receive your feedback or help you adapt *EqDAC* to support equivalence checking of your programs in a different language.


