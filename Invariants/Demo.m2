installPackage "InvariantRings" -- runs all checks
viewHelp "InvariantRings" -- opens documentation in browser

--no invariants example
--SL2 acting on C^2
restart
needsPackage "InvariantRings"
B = QQ[a,b,c,d]
A = ideal(a*d - b*c - 1)
SL2std = matrix{{a,b},{c,d}}
R = QQ[x_1..x_2]
V = linearlyReductiveAction(A,SL2std,R) 
invariants V
elapsedTime hilbertIdeal V

-- abelian group example C3xC3 acting on polynomial ring in two vars
restart
needsPackage "InvariantRings"
R = QQ[x_1..x_3]
W = matrix{{1,0,1},{0,1,1}}
L = {3,3}
T = diagonalAction(W,L,R)
S = R^T
invariantRing T
-- resolution of Hilbert ideal
I = definingIdeal S 
Q = ring I
F = res I
-- Hilbert series of ring of invariants
hilbertSeries S
-- equivariant Hilbert series of polynomial ring
equivariantHilbertSeries T


-- S_2 as a linearly reductive action
restart
needsPackage "InvariantRings"
S = QQ[z]
A = ideal(z^2 - 1)
M = matrix{{(1+z)/2, (1-z)/2},{(1-z)/2,(1+z)/2}}
R = QQ[a,b]
X = linearlyReductiveAction(A,M,R)
isInvariant(a,X)
invariants X

-- invariants of binary quadrics
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


-- invariants of binary quartics
restart
needsPackage "InvariantRings"
S = QQ[a,b,c,d]
I = ideal(a*d - b*c - 1)
A = S[u,v]
M4 = M = transpose (map(S,A)) last coefficients sub(basis(4,A),{u=>a*u+b*v,v=>c*u+d*v})
R4 = QQ[x_1..x_5]
L4 = linearlyReductiveAction(I,M4,R4)
elapsedTime hilbertIdeal L4
elapsedTime X = invariants L4 
-- Other invariants can be obtained from the generators above
g2 = X_0/12
g3 = -X_1/216
256*(g2^3 - 27*g3^2) -- discriminant of the quartic can be expressed in terms of invariants
1728*(g2^3)/(g2^3 - 27*g3^2) -- j-invariant (symmetrized cross-ratio) of quartic also in terms of invariants

-- invariant of 2x2 matrices of binary linear forms with SL_2 action
restart
needsPackage "InvariantRings"
S = QQ[a_(1,1)..a_(2,2),b_(1,1)..b_(2,2),c_(1,1)..c_(2,2)]
I = ideal((det genericMatrix(S,a_(1,1),2,2))-1,
    (det genericMatrix(S,b_(1,1),2,2))-1,
    (det genericMatrix(S,c_(1,1),2,2))-1);
G1 = transpose genericMatrix(S,2,2);
G2 = transpose genericMatrix(S,b_(1,1),2,2);
G3 = transpose genericMatrix(S,c_(1,1),2,2);
R = QQ[x_(1,1,1)..x_(2,2,2)]
L=linearlyReductiveAction(I,G1**G2**G3,R)
elapsedTime inv=invariants L
elapsedTime invariants(L,2)
-- elapsedTime invariants(L,4) takes too long, linear algebra
-- method is very slow with this many variables
-- however hilbertIdeal is fast!
elapsedTime hilbertIdeal(L)
J = hilbertIdeal(L)
isInvariant((J.gens)_(0,0),L)

-- invariants of S_4 using King's algorithm
-- and with the linear algebra method
restart
needsPackage "InvariantRings"
R = QQ[x_1..x_4]
L = apply({"2134","2341"},permutationMatrix);
S4 = finiteAction(L,R)
elapsedTime invariants S4
elapsedTime invariants(S4,UseLinearAlgebra=>true)
elapsedTime p=primaryInvariants S4
elapsedTime secondaryInvariants(p,S4)
elapsedTime hironakaDecomposition(S4)
