restart

--Change your FileName to wherever your copy of the package lives:
installPackage("CodingTheory", FileName => "/Users/gwynethwhieldon/M2develop/Workshop-2020-Cleveland/CodingTheory/CodingTheory.m2")

-----------------------------------------------------
-- Codes from Generator Matrices (as lists):
-----------------------------------------------------
F = GF(3,4)
codeLen = 7
codeDim = 3
L = apply(toList(1..codeDim),j-> apply(toList(1..codeLen),i-> random(F)))
C = linearCode(F,L)
peek C
-- check that dimension and length are correct:
dim C
length C
-- check that G*H^t = 0:
C.GeneratorMatrix * (transpose C.ParityCheckMatrix)
-----------------------------------------------------
-- Codes from Parity Check Matrices (as a matrix):
-----------------------------------------------------
F = GF(2)
L = {{1,0,1,0,0,0,1,1,0,0},{0,1,0,0,0,0,0,1,1,0},{0,0,1,0,1,0,0,0,1,1},{1,0,0,1,0,1,0,0,0,1},{0,1,0,0,1,1,1,0,0,0}}
C = linearCode(F,L,ParityCheck => true)
peek C


