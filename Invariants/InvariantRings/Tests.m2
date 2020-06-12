-------------------------------------------
--- FiniteGroupAction TESTS ---------------
-------------------------------------------

TEST ///
R = QQ[x_1]
G = finiteAction({matrix{{-1}}}, R)
assert(set group G === set {matrix{{1_QQ}}, matrix{{-1_QQ}}})
assert(isAbelian G)
assert(reynoldsOperator(x_1 + x_1^2, G) === x_1^2)
assert(isInvariant(1 + x_1^4 + x_1^6, G))
assert(not isInvariant(1 + x_1^5 + x_1^4, G))
///

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
--- FiniteAbelianAction TESTS -------------
-------------------------------------------

-- The first two tests are of trivial actions, and seem to run into problems. The analogous torusAction test seems to be fine though

TEST ///
R0 = QQ[x_1]
T0 = finiteAbelianAction({3},matrix{{0}},R0)
invariants0 = set {x_1}
assert(set invariants T0 === invariants0)
assert(isInvariant(x_1 + x_1^2, T0))
///

TEST ///
R0 = QQ[x_1]
T0 = finiteAbelianAction({1},matrix{{3}},R0)
invariants0 = set {x_1}
assert(set invariants T0 === invariants0)
assert(isInvariant(x_1 + x_1^2, T0))
///

TEST ///
R0 = QQ[x_1]
T0 = finiteAbelianAction({2},matrix{{1}},R0)
invariants0 = set {x_1^2}
assert(set invariants T0 === invariants0)
assert(isInvariant(x_1^2, T0))
///

TEST ///
R1 = QQ[x_1..x_3]
T1 = finiteAbelianAction({3,3},matrix{{1,0,1},{0,1,1}},R1)
invariants1 = set {x_3^3, x_2^3, x_1^3, x_1*x_2*x_3^2, x_1^2*x_2^2*x_3}
assert(set invariants T1 === invariants1)
///


-------------------------------------------
--- TorusAction TESTS ---------------------
-------------------------------------------

TEST ///
R = QQ[x_1]
T = torusAction(matrix{{0}}, R)
invariants0 = set {x_1}
assert(weights T === matrix{{0}})
assert(set invariants T === invariants0)
///

TEST ///
R0 = QQ[x_1..x_2]
T0 = torusAction(matrix{{1,1}}, R0)
invariants0 = set {}
assert(weights T0 === matrix{{1,1}})
assert(set invariants T0 === invariants0)
///

TEST ///
R1 = QQ[x_1..x_4]
T1 = torusAction(matrix {{-3, -1, 1, 2}}, R1)
invariants1 =  set {x_2*x_3, x_2^2*x_4, x_1*x_3*x_4, x_1*x_2*x_4^2, x_1^2*x_4^3, x_1*x_3^3}
assert(weights T1 === matrix{{-3, -1, 1, 2}})
assert(set invariants T1 === invariants1)
///

TEST ///
R2 = QQ[x_1..x_4]
T2 = torusAction(matrix{{0,1,-1,1},{1,0,-1,-1}}, R2)
invariants2 = set {x_1*x_2*x_3,x_1^2*x_3*x_4}
assert(set invariants T2 === invariants2)
///
     
     
-------------------------------------------
--- LinearlyReductiveAction TESTS ---------
-------------------------------------------

TEST ///
A = QQ[z]
I = ideal(z^2 - 1)
M = matrix{{(z+1)/2, (1-z)/2},{(1-z)/2, (1+z)/2}}
R = QQ[x_1,x_2]
V = linearlyReductiveAction(I,M,R)
assert(hilbertIdeal V == ideal(x_1 + x_2, x_2^2))
///

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
  
       





