

restart
uninstallPackage "InvariantRings"
installPackage "InvariantRings"
check InvariantRings

B = QQ[a,b,c,d]
A = ideal(a*d - b*c - 1)
SL2std = matrix{{a,b},{c,d}}
R1 = QQ[x_1..x_2]

time V1 = linearlyReductiveAction(A,SL2std,R1)
time hilbertIdeal V1


restart
loadPackage "InvariantRings"
R1 = QQ[a_1..a_3]
W = matrix{{1,0,1},{0,1,1}}
L = {3,3}
T = finiteAbelianAction(L,W,R1)
R1^T
invariantRing T

-- S_2 as a linearly reductive action
S = QQ[z]
A = ideal(z^2 - 1)
M = matrix{{(1+z)/2, (1-z)/2},{(1-z)/2,(1+z)/2}}
R = QQ[a,b]
X = linearlyReductiveAction(A,M,R)
isInvariant(a,X)

-- invariants of binary forms
restart
needsPackage "InvariantRings"
S = QQ[a,b,c,d]
I = ideal(a*d - b*c - 1)
A = S[u,v]
M = transpose (map(S,A)) last coefficients sub(basis(2,A),{u=>a*u+b*v,v=>c*u+d*v})
R = QQ[x_1..x_3]
L = linearlyReductiveAction(I,M,R)
hilbertIdeal L
invariants L
invariants(L,4)
invariants(L,5)

-- invariant of 2x2 matrices of binary linear forms with SL_2 action
restart
needsPackage "InvariantRings"
S = QQ[a_(1,1)..a_(2,2),b_(1,1)..b_(2,2),c_(1,1)..c_(2,2)]
I = ideal((det genericMatrix(S,a_(1,1),2,2))-1,
    (det genericMatrix(S,b_(1,1),2,2))-1,
    (det genericMatrix(S,c_(1,1),2,2))-1)
G1 = transpose genericMatrix(S,2,2)
G2 = transpose genericMatrix(S,b_(1,1),2,2)
G3 = transpose genericMatrix(S,c_(1,1),2,2)
R = QQ[x_(1,1,1)..x_(2,2,2)]
L=linearlyReductiveAction(I,G1**G2**G3,R)
elapsedTime inv=invariants L

-- invariants of S_4 using King's algorithm
-- and with the linear algebra method
restart
needsPackage "InvariantRings"
R = QQ[x_1..x_4]
L = apply({"2134","2341"},permutationMatrix);
S4 = finiteAction(L,R)
elapsedTime invariants S4
elapsedTime invariants(S4,UseLinearAlgebra=>true)
