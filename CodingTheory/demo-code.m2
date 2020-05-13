--Change your FileName to wherever your copy of the package lives:
loadPackage("CodingTheory", FileName => "/Users/gwynethwhieldon/M2develop/Workshop-2020-Cleveland/CodingTheory/CodingTheory.m2")


-- Sample Code
F = GF(2^4)
codeLen = 10
codeDim = 4
L = apply(toList(1..codeDim),j-> apply(toList(1..codeLen),i-> random(F)))

-- Constructor via basefield, dimension of ambient space, list of codewords:
C = linearCode(F,codeLen,L)
peek C

codeLen = 7
codeDim = 3
L = apply(toList(1..codeDim),j-> apply(toList(1..codeLen),i-> random(F)))

-- Constructor via GF(p,q) (p=2,q=4):
C = linearCode(2,4,codeLen,L)

-- Constructor via ambient module and submodule:
C2 = linearCode(C.AmbientModule,C.Code)




