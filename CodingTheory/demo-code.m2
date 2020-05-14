restart

--Change your FileName to wherever your copy of the package lives:
installPackage("CodingTheory", FileName => "/Users/gwynethwhieldon/M2develop/Workshop-2020-Cleveland/CodingTheory/CodingTheory.m2")

F = GF(2,4)
codeLen = 7
codeDim = 3
L = apply(toList(1..codeDim),j-> apply(toList(1..codeLen),i-> random(F)))


-- Constructor via GF(p,q) (p=2,q=4):
C1 = linearCode(2,4,codeLen,L)

C1p = linearCode((GF(2,4))^codeLen,L)

-- Sample Code
F = GF(2)
codeLen = 10
codeDim = 4
L = apply(toList(1..codeDim),j-> apply(toList(1..codeLen),i-> random(F)))

-- Constructor via basefield, dimension of ambient space, list of codewords:
C2 = linearCode(F,codeLen,L)
peek C2

-- Constructor via submodule:
C3 = linearCode(C2.Code)


-- Sample method usages:
dualCode(C1)
dualCode(C2)
dualCode(C3)

alphabet(C1)
alphabet(C2)
alphabet(C3)

-- Canonical form for parity check matrix production:

M = matrix(L)
G = transpose groebnerBasis transpose M

