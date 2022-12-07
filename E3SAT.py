#3-satisfiability

import random
import numpy
from termcolor import colored

numpy.random.seed(seed = 2); mixPRNG = numpy.random.default_rng(seed = 1) #for testing purposes
globSecParam = 10
testCNF = [['x1', 'x2', 'x1'], ['x1', 'x3', 'x2'], ['~x0', 'x3', 'x1'], ['x2', 'x1', 'x0']]
testAssignment = {'x0': 0, 'x1': 0, 'x2': 1, 'x3': 0}

###bit commitment
def bitstringXOR(a, b):
    if len(a) != len(b) or not isinstance(a, str) or not isinstance(b, str):
        raise Exception("Lengths of strings must be equal")
    else:
        ans = ""
        for i in range(len(a)):
            if a[i] == b[i]:
                ans += "0"
            else:
                ans += "1"
        return ans

def binToNN(a):
    if not isinstance(a, str) or len(a) == 0:
        raise Exception("Input must be a binary string")
    else:
        power = 0
        ans = 0
        for i in range(len(a)):
            if a[-i - 1] == "0":
                pass
            elif a[-i - 1] == "1":
                ans += 2 ** power
            else:
                raise Exception("Input must be a binary string")
            power += 1
        return ans

def genGoodString(securityParam = globSecParam):
    goodString_ = numpy.random.randint(2, size = (3 * securityParam,))
    goodString = ''.join(str(_) for _ in goodString_) #hopefully this should be a good string (happens with prob ≥ 1 - 1 / (2 ^ n))
    return goodString

def bitCommit(goodString, committedBit, securityParam = globSecParam, PRNGSeed = None):
    if committedBit < 0 or committedBit > 1:
        raise Exception("Invalid bit")

    if PRNGSeed == None:
        PRNGSeed_ = numpy.random.randint(2, size = (securityParam,))
        PRNGSeed = ''.join(str(_) for _ in PRNGSeed_)

    random.seed(a = PRNGSeed) #set the seed for the PRNG based on random string of length of security parameter
    PRN_ = random.getrandbits(3 * securityParam)
    PRN = bin(PRN_)[2:] #this is the PRN the sender uses (G(s) in textbook)
    while len(PRN) < 3 * securityParam:
        PRN = '0' + PRN

    if committedBit == 0: #if the committed bit is 0, send only the PRN, if the bit is 1, XOR with good string first
        verifMsg = PRN
    else:
        verifMsg = bitstringXOR(PRN, goodString)
    return [PRNGSeed, verifMsg]

def revealPhase(PRNGSeed, verifMsg, goodString, securityParam = globSecParam):
    random.seed(a = PRNGSeed)
    PRN_ = random.getrandbits(3 * securityParam)
    PRN = bin(PRN_)[2:]
    while len(PRN) < 3 * securityParam: #padding
        PRN = '0' + PRN

    if PRN == verifMsg:
        committedBit = 0
    elif bitstringXOR(PRN, goodString) == verifMsg:
        committedBit = 1
    else:
        raise Exception("Reveal failed")
    return committedBit
###

def checkAssignment(CNF, testAssignment): #test an assignment of variables (not used)
    for clause in CNF:
        atLeastOne = 0; allTried = 0
        for variable in clause:
            if variable[0] == '~':
                inv = True
                variable = variable[1:]
            else:
                inv = False
            if inv:
                if testAssignment[variable] == 0:
                    atLeastOne += 1
                else:
                    pass
            else:
                if testAssignment[variable] == 1:
                    atLeastOne += 1
                else:
                    pass
            allTried += 1

            if atLeastOne == 0 and allTried == 3:
                return False
    
    return True

print(colored(testCNF, 'yellow'))
print(colored(testAssignment, 'yellow'))

def relabelVars(CNF, permuteDict): #relabel all variables based on some mapping
    permutedCNF = []

    for clause in CNF:
        permutedClause = []
        for literal in clause:
            if literal[0] == '~':
                inv = True
                literal = literal[1:]
            else:
                inv = False

            literal = permuteDict[literal]
            if inv:
                literal = '~' + literal
            else:
                pass

            permutedClause.append(literal)

        permutedCNF.append(permutedClause)

    return permutedCNF

def shuffleVars(CNF, validAssignment, permuteDict0 = {}, permuteDict1 = {}): #permute trues' and falses' labels (and store the mapping) first
    numVars = len(validAssignment)
    if permuteDict0 == {} and permuteDict1 == {}: #create a permutation map (2 actually: the trues and falses)
        trueVars = []; falseVars = []; permutationDict = {}
        for i in range(numVars):
            literal = 'x' + str(i)
            if validAssignment[literal]:
                trueVars.append(literal)
            else:
                falseVars.append(literal)

        ptrueVars = trueVars.copy(); pfalseVars = falseVars.copy()
        mixPRNG.shuffle(ptrueVars); mixPRNG.shuffle(pfalseVars) #mixPRNG
        for i in [trueVars, falseVars]:
            for j in range(len(i)):
                if i == trueVars:
                    permutationDict[i[j]] = ptrueVars[j]
                elif i == falseVars:
                    permutationDict[i[j]] = pfalseVars[j]
    else:
        permutationDict = {**permuteDict0, **permuteDict1}
    
    permutationDict = list(permutationDict.items()); mixPRNG.shuffle(permutationDict); permutationDict = dict(permutationDict) #mixPRNG
    permutedCNF = relabelVars(CNF, permutationDict)

    return permutationDict, permutedCNF

def shuffleClauses(CNF, permuteListClauses = []): #reorder the clauses in the CNF second
    if permuteListClauses == []:
        return mixPRNG.permutation(CNF) #mixPRNG
    else:
        numClauses = len(permuteListClauses); reorderedClauses = []
        for i in range(numClauses):
            reorderedClauses.append(CNF[permuteListClauses[i]])
        return reorderedClauses

def permuteVarOrder(CNF): #reorder the variables in each clause third
    reorderedCNF = []
    for clause in CNF:
        reorderedClause = clause.copy()
        mixPRNG.shuffle(reorderedClause) #mixPRNG
        reorderedCNF.append(reorderedClause)
    return reorderedCNF

def coinflipInvert(CNF, validAssignment): #invert literals w prob 1/2 fourth
    inversions = set()
    for literal in validAssignment.keys():
        coinflip = mixPRNG.choice([0, 1]) #mixPRNG
        if coinflip == 1:
            for clause in CNF:
                for i in range(3):
                    if clause[i] == '~' + literal:
                        clause[i] = literal
                    elif clause[i] == literal:
                        clause[i] = '~' + literal
                    else:
                        pass
            inversions.add(literal)

            validAssignment[literal] = validAssignment[literal] ^ 1
        else:
            pass

    return CNF, validAssignment, inversions

def mixCNF(CNF, validAssignment, permuteDict0 = {}, permuteDict1 = {}, permuteListClauses = []):
    permutationDict, CNF = shuffleVars(CNF, validAssignment, permuteDict0, permuteDict1)
    CNF = shuffleClauses(CNF, permuteListClauses)
    CNF = permuteVarOrder(CNF)
    CNF, validAssignment, inversions = coinflipInvert(CNF, validAssignment)

    return CNF, validAssignment, permutationDict, inversions

#ex1, ex2, ex3, ex4 = mixCNF(testCNF, testAssignment)
#print('out:', ex1); print('inversions:', ex4); print('perms:', ex3)#; print('assignment:', ex2)

def toBits(_):
    ba = []
    for i in bytearray(_, 'ascii'):
        ba.append(bin(i))
    return ba

def fromBits(_):
    for i in range(len(_)):
        _[i] = int(_[i], 2)
    return bytearray(_).decode('ascii')

def CNFToBits(CNF):
    CNFAsBits = []
    for clause in CNF:
        clauseAsBits = []
        for literal in clause:
            if literal[0] == '~':
                inv = True
                subscript = literal[2:]; subscript = int(subscript); subscript = bin(subscript)[2:]
            else:
                inv = False
                subscript = literal[1:]; subscript = int(subscript); subscript = bin(subscript)[2:]

            if inv:
                subscript = '1' + subscript
            else:
                subscript = '0' + subscript

            clauseAsBits.append(subscript)

        CNFAsBits.append(clauseAsBits)

    return CNFAsBits

def bitsToCNF(bitstring):
    CNF = []
    for clause in bitstring:
        _ = []
        for var in clause:
            literal = fromBits(var)
            _.append(literal)
        CNF.append(_)
    return CNF

def commitCNF(CNF, securityParam = globSecParam):
    CNFAsBits = CNFToBits(CNF)
    allCommitments = []; seeds = []
    goodString = genGoodString(securityParam)

    for clause in CNFAsBits:
        clauseC = []
        for literal in clause:
            literalC = []
            for bit in literal:
                bit = int(bit)
                com = bitCommit(goodString, bit, securityParam)
                seeds.append(com[0]); literalC.append(com[1])
            
            clauseC.append(literalC)

        allCommitments.append(clauseC)

    return allCommitments, seeds, goodString

def commitAssign(validAssignment, securityParam = globSecParam):
    commitDict = {}; seeds = []; goodString = genGoodString(securityParam)
    for literal in validAssignment.keys():
        assignment = validAssignment[literal]
        committedAssign = bitCommit(goodString, assignment, securityParam)
        commitDict[literal] = committedAssign[1]
        seeds.append(committedAssign[0])

    return commitDict, seeds, goodString

def revealCNFCommit(allCommitments, seeds, goodString, securityParam = globSecParam):
    CNF = []; seedIndex = 0
    for clause in allCommitments:
        revealedClause = []
        for literal in clause:
            invCheckBit = revealPhase(seeds[seedIndex], literal[0], goodString, securityParam); seedIndex += 1
            varString = ''
            for varBits in literal[1:]:
                digit = revealPhase(seeds[seedIndex], varBits, goodString, securityParam); digit = str(digit)
                varString = varString + digit
                seedIndex += 1
            
            varString = str(binToNN(varString))

            if invCheckBit:
                varString = '~x' + varString
            else:
                varString = 'x' + varString

            revealedClause.append(varString)

        CNF.append(revealedClause)

    return CNF

def revealAssignCommit(commitDict, seeds, goodString, clause, securityParam = globSecParam):
    revealedDict = {}
    for literal in clause:
        if literal[0] == '~':
            literal = literal[1:]
        else:
            pass

        seedIndex = int(literal[1:])
        revealedAssign = revealPhase(seeds[seedIndex], commitDict[literal], goodString, securityParam)

        revealedDict[literal] = revealedAssign
    
    return revealedDict

#now either the verifier can ask for the CNF and permutation mappings, or ask for a clause and its assignments
def verifyCNFs(trueCNF, givenCNF, permutationDict, inversions):
    clauseCompareTrue = []; clauseCompareGiven = []
    for clause in givenCNF:
        for i in range(3):
            if clause[i][0] == '~':
                literal = clause[i][1:]
                if literal in inversions:
                    clause[i] = literal
                else:
                    pass
            else:
                literal = clause[i]
                if literal in inversions:
                    clause[i] = '~' + literal
                else:
                    pass

    invPermDict = dict((v, k) for k, v in permutationDict.items())
    CNF = relabelVars(givenCNF, invPermDict)
    for clause in CNF:
        clauseCompareGiven.append(set(clause))

    for clause in trueCNF:
        clauseCompareTrue.append(set(clause))

    for clause in clauseCompareGiven:
        if (clause in clauseCompareTrue):
            pass
        else:
            print('this one here', clause)
            return False
        
    return True

def verifyClause(clause, givenAssignment):
    for i in range(3):
        if clause[i][0] == '~':
            literal = clause[i][1:]
            if givenAssignment[literal] == 0:
                return True
            else:
                pass
        else:
            if givenAssignment[clause[i]]:
                return True
            else:
                pass

    return False

#all that's left to put all the fns together
def prover1(CNF, validAssignment, permuteDict0 = {}, permuteDict1 = {}, permuteListClauses = [], securityParam = globSecParam):
    mixedCNF, _permutedAssign, permutationDict, inversions = mixCNF(CNF, validAssignment, permuteDict0, permuteDict1, permuteListClauses)
    print(mixedCNF)
    allCommitments, seedsCNF, goodStringCNF = commitCNF(mixedCNF, securityParam)
    commitDict, seedsAssign, goodStringAssign = commitAssign(validAssignment, securityParam)
    return allCommitments, seedsCNF, goodStringCNF, commitDict, seedsAssign, goodStringAssign, permutationDict, inversions, mixedCNF, securityParam

a1, b1, c1, d1, e1, f1, g1, h1, i1, l1 = prover1(testCNF, testAssignment)
#print(a); print(d); print(g); print(h)

def verifier1(allCommitments): #pick whether to ask for whole CNF or just a clause and its assignments
    flip = numpy.random.randint(0, 2)
    if flip:
        wantCNF = True
    else:
        wantCNF = False
    
    if wantCNF:
        return 'CNF'
    else:
        return numpy.random.randint(0, len(allCommitments))

def prover2(permutedCNF, allCommitments, seedsCNF, goodStringCNF, commitDict, seedsAssign, goodStringAssign, permutationDict, inversions, wantCNFOrClause, securityParam = globSecParam):
    if wantCNFOrClause == 'CNF':
        return allCommitments, seedsCNF, goodStringCNF, permutationDict, inversions, securityParam
    else:
        committedClause = allCommitments[wantCNFOrClause]; numSeeds = 0
        for varInBits in committedClause:
            numSeeds += len(varInBits)
        seedsForClause = seedsCNF[wantCNFOrClause:(wantCNFOrClause + numSeeds)]
        clause = permutedCNF[wantCNFOrClause]
        committedAssignments = {}
        for literal in clause:
            if literal[0] == '~':
                literal = literal[1:]
            else:
                pass
            committedAssignments[literal] = commitDict[literal]
        seedsForAssign = seedsAssign[wantCNFOrClause:(wantCNFOrClause + 3)]

        return committedClause, seedsForClause, committedAssignments, seedsForAssign, goodStringCNF, goodStringAssign, securityParam
        
a2, b2, c2, d2, e2, f2 = prover2(i1, a1, b1, c1, d1, e1, f1, g1, h1, 'CNF')
A2, B2, C2, D2, E2, F2, G2 = prover2(i1, a1, b1, c1, d1, e1, f1, g1, h1, 1)

def verifier2CNF(trueCNF, allCommitments, seedsCNF, goodStringCNF, permutationDict, inversions, securityParam = globSecParam):
    revealed = revealCNFCommit(allCommitments, seedsCNF, goodStringCNF, securityParam)
    return verifyCNFs(trueCNF, revealed, permutationDict, inversions)

print(verifier2CNF(testCNF, a2, b2, c2, d2, e2, f2))

def verifier2Clause(committedClause, seedsForClause, committedAssignments, seedsForAssign, goodStringCNF, goodStringAssign, securityParam):
    revealedClause = revealCNFCommit([committedClause], seedsForClause, goodStringCNF, securityParam); revealedClause = revealedClause[0]
    revealedAssign = revealAssignCommit(committedAssignments, seedsForAssign, goodStringAssign, revealedClause, securityParam)
    return verifyClause(revealedClause, revealedAssign)

print(verifier2Clause(A2, B2, C2, D2, E2, F2, G2))