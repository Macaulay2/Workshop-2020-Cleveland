

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

S = QQ[z]
A = ideal(z^2 - 1)
M = matrix{{(1+z)/2, (1-z)/2},{(1-z)/2,(1+z)/2}}
R = QQ[a,b]
X = linearlyReductiveAction(A,M,R)
isInvariant(a,X)

