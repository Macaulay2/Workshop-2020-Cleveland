-------------------------------------------
--- FiniteGroupAction TESTS ---------------
-------------------------------------------

-- Test 0
TEST ///
R = QQ[x_1]
G = finiteAction({matrix{{-1}}}, R)
assert(set group G === set {matrix{{1_QQ}}, matrix{{-1_QQ}}})
assert(isAbelian G)
assert(reynoldsOperator(x_1 + x_1^2, G) === x_1^2)
assert(isInvariant(1 + x_1^4 + x_1^6, G))
assert(not isInvariant(1 + x_1^5 + x_1^4, G))
///

-- Test 1
TEST ///
R = QQ[x_1..x_3]
L = apply(2, i -> permutationMatrix(3, [i + 1, i + 2] ) )
S3 = finiteAction(L,R)
assert(#(group S3) === 6)
assert(not isAbelian S3)
assert(reynoldsOperator(x_1 + x_1*x_2*x_3, S3) === (1/3)*(x_1 + x_2 + x_3) + x_1*x_2*x_3)
assert(isInvariant(1 + x_1 + x_2 + x_3, S3))
assert(not isInvariant(1 + x_1, S3))
///


-------------------------------------------
--- DiagonalAction TESTS -------------
-------------------------------------------

-- The first two tests are of trivial actions, and seem to run into problems. The analogous torusAction test seems to be fine though

-- Test 2
TEST ///
R = QQ[x_1]
T = diagonalAction(matrix{{0}}, {3}, R)
invariants0 = set {R_0}
assert(set invariants T === invariants0)
assert(isInvariant(R_0 + R_0^2, T))
///

-- Test 3
TEST ///
R = QQ[x_1]
T = diagonalAction(matrix{{3}}, {1}, R)
invariants0 = set {R_0}
assert(set invariants T === invariants0)
assert(isInvariant(R_0 + R_0^2, T))
///

-- Test 4
TEST ///
R = QQ[x_1]
T = diagonalAction(matrix{{1}}, {2}, R)
invariants0 = set {R_0^2}
assert(set invariants T === invariants0)
assert(isInvariant(R_0^2, T))
///

-- Test 5
TEST ///
R = QQ[x_1..x_3]
T = diagonalAction(matrix{{1,0,1},{0,1,1}}, {3,3}, R)
invariants1 = set {x_3^3, x_2^3, x_1^3, x_1*x_2*x_3^2, x_1^2*x_2^2*x_3}
assert(set invariants T === invariants1)
///

-- Test 6
TEST ///
R = QQ[x_1]
T = diagonalAction(matrix{{0}}, R)
invariants0 = set {x_1}
assert(first weights T === matrix{{0}})
assert(set invariants T === invariants0)
///

-- Test 7
TEST ///
R0 = QQ[x_1..x_2]
T0 = diagonalAction(matrix{{1,1}}, R0)
invariants0 = set {}
assert(first weights T0 === matrix{{1,1}})
assert(set invariants T0 === invariants0)
///

-- Test 8
TEST ///
R1 = QQ[x_1..x_4]
T1 = diagonalAction(matrix {{-3, -1, 1, 2}}, R1)
invariants1 =  set {x_2*x_3, x_2^2*x_4, x_1*x_3*x_4, x_1*x_2*x_4^2, x_1^2*x_4^3, x_1*x_3^3}
assert(first weights T1 === matrix{{-3, -1, 1, 2}})
assert(set invariants T1 === invariants1)
///

-- Test 9
TEST ///
R2 = QQ[x_1..x_4]
T2 = diagonalAction(matrix{{0,1,-1,1},{1,0,-1,-1}}, R2)
invariants2 = set {x_1*x_2*x_3,x_1^2*x_3*x_4}
assert(set invariants T2 === invariants2)
///
     
     
-------------------------------------------
--- LinearlyReductiveAction TESTS ---------
-------------------------------------------

-- Test 10
TEST ///
A = QQ[z]
I = ideal(z^2 - 1)
M = matrix{{(z+1)/2, (1-z)/2},{(1-z)/2, (1+z)/2}}
R = QQ[x_1,x_2]
V = linearlyReductiveAction(I,M,R)
assert(hilbertIdeal V == ideal(x_1 + x_2, x_2^2))
///

-- Test 11
TEST ///
R = QQ[a,b,c,d]
idealSL2 = ideal(a*d - b*c - 1)
SL2std = matrix{{a,b},{c,d}}
R1 = QQ[x_1..x_2]
V1 = linearlyReductiveAction(idealSL2,SL2std,R1)
assert(hilbertIdeal V1 == 0)
assert(set invariants V1 === set {})
SL2Sym2 = matrix{{a^2, a*b, b^2}, {2*a*c, b*c + a*d, 2*b*d}, {c^2, c*d, d^2}}
R2 = QQ[x_1..x_3]
V2 = linearlyReductiveAction(idealSL2,SL2Sym2,R2)
assert(set invariants V2 === set {x_2^2-x_1*x_3})
///

-- Test 12
-- This tests invariants for an action on a quotient ring
TEST ///
S = QQ[z]
I = ideal(z^2 - 1)
M = matrix{{(z+1)/2, (1-z)/2},{(1-z)/2, (z+1)/2}}
Q = QQ[x,y] / ideal(x*y)
L = linearlyReductiveAction(I, M, Q)
assert(invariants L === {x+y})
assert(hilbertIdeal L === ideal(x+y))
assert(invariants(L,2) === {x^2+y^2})
assert(isInvariant(x^3+y^3,L))
///

-------------------------------------------
--- equivariantHilbertSeries TESTS --------
-------------------------------------------

-- Test 13
-- mixed torus + abelian action
TEST ///
R = QQ[x_1..x_3]
W1 = matrix{{1,0,-1},{0,1,-1}}
W2 = matrix{{0,1,1},{1,0,1}}
d = {3,3}
D = diagonalAction(W1,W2,d,R)
degRing = degreesRing D
e = equivariantHilbertSeries D
assert(value denominator e === 
    1+(-z_0*z_3-z_1*z_2-z_0^(-1)*z_1^(-1)*z_2*z_3)*T+(z_0*z_1*z_
      2*z_3+z_1^(-1)*z_2*z_3^2+z_0^(-1)*z_2^2*z_3)*T^2-z_2^2*z_3^2
      *T^3)
assert(equivariantHilbertSeries(D,Order=>6) ===
    1+(z_0*z_3+z_1*z_2+z_0^(-1)*z_1^(-1)*z_2*z_3)*T+(z_0^2*z_3^2
      +z_0*z_1*z_2*z_3+z_1^2*z_2^2+z_1^(-1)*z_2*z_3^2+z_0^(-1)*z_2
      ^2*z_3+z_0^(-2)*z_1^(-2)*z_2^2*z_3^2)*T^2+(z_0^3+z_0^2*z_1*z
      _2*z_3^2+z_0*z_1^2*z_2^2*z_3+z_0*z_1^(-1)*z_2+z_1^3+z_2^2*z_
      3^2+z_0^(-1)*z_1*z_3+z_0^(-1)*z_1^(-2)*z_2^2+z_0^(-2)*z_1^(-
      1)*z_3^2+z_0^(-3)*z_1^(-3))*T^3+(z_0^4*z_3+z_0^3*z_1*z_2+z_0
      ^2*z_1^2*z_2^2*z_3^2+z_0^2*z_1^(-1)*z_2*z_3+z_0*z_1^3*z_3+z_
      0*z_2^2+z_1^4*z_2+z_1*z_3^2+z_1^(-2)*z_2^2*z_3+z_0^(-1)*z_1^
      2*z_2*z_3+z_0^(-1)*z_1^(-1)+z_0^(-2)*z_2*z_3^2+z_0^(-2)*z_1
      ^(-3)*z_3+z_0^(-3)*z_1^(-2)*z_2+z_0^(-4)*z_1^(-4)*z_2*z_3)*T
      ^4+(z_0^5*z_3^2+z_0^4*z_1*z_2*z_3+z_0^3*z_1^2*z_2^2+z_0^3*z_
      1^(-1)*z_2*z_3^2+z_0^2*z_1^3*z_3^2+z_0^2*z_2^2*z_3+z_0*z_1^4
      *z_2*z_3+z_0*z_1+z_0*z_1^(-2)*z_2^2*z_3^2+z_1^5*z_2^2+z_1^2*
      z_2*z_3^2+z_1^(-1)*z_3+z_0^(-1)*z_1^3*z_2^2*z_3+z_0^(-1)*z_2
      +z_0^(-1)*z_1^(-3)*z_3^2+z_0^(-2)*z_1*z_2^2*z_3^2+z_0^(-2)*z
      _1^(-2)*z_2*z_3+z_0^(-3)*z_1^(-1)*z_2^2+z_0^(-3)*z_1^(-4)*z_
      2*z_3^2+z_0^(-4)*z_1^(-3)*z_2^2*z_3+z_0^(-5)*z_1^(-5)*z_2^2*
      z_3^2)*T^5)
///

-- Test 14
-- torus action
TEST ///
R = QQ[x_1..x_4]
W = matrix{{0,1,-1,1},{1,0,-1,-1}}
D = diagonalAction(W, R)
degRing = degreesRing D
e = equivariantHilbertSeries D
assert(value denominator e ===
    1+(-z_0-z_0*z_1^(-1)-z_1-z_0^(-1)*z_1^(-1))*T+(z_0^2*z_1^(-1
      )+z_0*z_1+z_0+z_1^(-1)+z_1^(-2)+z_0^(-1))*T^2+(-z_0^2-z_0*z_
      1^(-2)-1-z_1^(-1))*T^3+z_0*z_1^(-1)*T^4)
assert(equivariantHilbertSeries(D,Order=>6) ===
    1+(z_0+z_0*z_1^(-1)+z_1+z_0^(-1)*z_1^(-1))*T+(z_0^2+z_0^2*z_
      1^(-1)+z_0^2*z_1^(-2)+z_0*z_1+z_0+z_1^2+z_1^(-1)+z_1^(-2)+z_
      0^(-1)+z_0^(-2)*z_1^(-2))*T^2+(z_0^3+z_0^3*z_1^(-1)+z_0^3*z_
      1^(-2)+z_0^3*z_1^(-3)+z_0^2*z_1+z_0^2+z_0^2*z_1^(-1)+z_0*z_1
      ^2+z_0*z_1+z_0*z_1^(-1)+z_0*z_1^(-2)+z_0*z_1^(-3)+z_1^3+1+z_
      1^(-1)+z_0^(-1)*z_1+z_0^(-1)*z_1^(-2)+z_0^(-1)*z_1^(-3)+z_0
      ^(-2)*z_1^(-1)+z_0^(-3)*z_1^(-3))*T^3+(z_0^4+z_0^4*z_1^(-1)+
      z_0^4*z_1^(-2)+z_0^4*z_1^(-3)+z_0^4*z_1^(-4)+z_0^3*z_1+z_0^3
      +z_0^3*z_1^(-1)+z_0^3*z_1^(-2)+z_0^2*z_1^2+z_0^2*z_1+z_0^2+z
      _0^2*z_1^(-1)+z_0^2*z_1^(-2)+z_0^2*z_1^(-3)+z_0^2*z_1^(-4)+z
      _0*z_1^3+z_0*z_1^2+z_0+z_0*z_1^(-1)+z_0*z_1^(-2)+z_1^4+z_1+1
      +z_1^(-2)+z_1^(-3)+z_1^(-4)+z_0^(-1)*z_1^2+z_0^(-1)*z_1^(-1
      )+z_0^(-1)*z_1^(-2)+z_0^(-2)+z_0^(-2)*z_1^(-3)+z_0^(-2)*z_1
      ^(-4)+z_0^(-3)*z_1^(-2)+z_0^(-4)*z_1^(-4))*T^4+(z_0^5+z_0^5*
      z_1^(-1)+z_0^5*z_1^(-2)+z_0^5*z_1^(-3)+z_0^5*z_1^(-4)+z_0^5*
      z_1^(-5)+z_0^4*z_1+z_0^4+z_0^4*z_1^(-1)+z_0^4*z_1^(-2)+z_0^4
      *z_1^(-3)+z_0^3*z_1^2+z_0^3*z_1+z_0^3+2*z_0^3*z_1^(-1)+z_0^3
      *z_1^(-2)+z_0^3*z_1^(-3)+z_0^3*z_1^(-4)+z_0^3*z_1^(-5)+z_0^2
      *z_1^3+z_0^2*z_1^2+z_0^2*z_1+z_0^2+z_0^2*z_1^(-1)+z_0^2*z_1
      ^(-2)+z_0^2*z_1^(-3)+z_0*z_1^4+z_0*z_1^3+z_0*z_1+z_0+z_0*z_1
      ^(-1)+z_0*z_1^(-2)+z_0*z_1^(-3)+z_0*z_1^(-4)+z_0*z_1^(-5)+z_
      1^5+z_1^2+z_1+z_1^(-1)+z_1^(-2)+z_1^(-3)+z_0^(-1)*z_1^3+z_0
      ^(-1)+z_0^(-1)*z_1^(-1)+z_0^(-1)*z_1^(-3)+z_0^(-1)*z_1^(-4)+
      z_0^(-1)*z_1^(-5)+z_0^(-2)*z_1+z_0^(-2)*z_1^(-2)+z_0^(-2)*z_
      1^(-3)+z_0^(-3)*z_1^(-1)+z_0^(-3)*z_1^(-4)+z_0^(-3)*z_1^(-5
      )+z_0^(-4)*z_1^(-3)+z_0^(-5)*z_1^(-5))*T^5)
///

-- Test 15
-- abelian action
TEST ///
R = QQ[x_1..x_3]
d = {3,3}
W = matrix{{1,0,1},{0,1,1}}
D = diagonalAction(W, d, R)
degRing = degreesRing D
e = equivariantHilbertSeries D
assert(value denominator e ===
    1+(-z_0*z_1-z_0-z_1)*T+(z_0^2*z_1+z_0*z_1^2+z_0*z_1)*T^2-z_0
      ^2*z_1^2*T^3)
assert(equivariantHilbertSeries(D,Order=>6) ===
    1+(z_0*z_1+z_0+z_1)*T+(z_0^2*z_1^2+z_0^2*z_1+z_0^2+z_0*z_1^2
      +z_0*z_1+z_1^2)*T^2+(z_0^2*z_1^2+z_0^2*z_1+z_0^2+z_0*z_1^2+z
      _0+z_1^2+z_1+3)*T^3+(z_0^2*z_1^2+z_0^2*z_1+z_0^2+z_0*z_1^2+3
      *z_0*z_1+3*z_0+z_1^2+3*z_1+1)*T^4+(3*z_0^2*z_1^2+3*z_0^2*z_1
      +3*z_0^2+3*z_0*z_1^2+3*z_0*z_1+z_0+3*z_1^2+z_1+1)*T^5)
///
