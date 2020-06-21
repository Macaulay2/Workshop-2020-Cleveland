restart
needsPackage("MonomialIntegerPrograms")
viewHelp("MonomialIntegerPrograms")

loadBuiltinCodimAndDegree();

-- quick function for generating a random monomial ideal
rmi := (R, j, k, l) -> monomialIdeal(apply(j, i -> product apply(take(random gens R, 1 + random k), x -> x^(1 + random l))))

-- dimension of mon ideal
R = QQ[x_1..x_100];
I = rmi(R, 30, 20, 3);
print I
numgens I
elapsedTime(codim I)
elapsedTime(codimensionIP I)

-- solving info is saved in temporary directory
ScipPrintLevel = 0 -- no info
ScipPrintLevel = 1 -- location of temporary directory
ScipPrintLevel = 2 -- + error log if it exists
ScipPrintLevel = 3 -- + IP formulation
ScipPrintLevel = 4 -- + complete solving output from SCIP

-- degree of mon ideal
R = QQ[x_1..x_50];
I = rmi(R, 25, 15, 3);
print I
numgens I
elapsedTime(degree I)
elapsedTime(degreeIP I)

-- enumerating monomial ideals with a given Hilbert function
R = QQ[x,y,z]
M = monomialIdealsWithHilbertFunction({1,3,4,2,1,0}, R);
#M
M_0
take(M, 5)

-- specify first total betti number
Ma = monomialIdealsWithHilbertFunction({1,3,4,2,1,0}, R, FirstBetti => 6); 
#Ma
member(M_0, Ma)

-- specify first graded betti numbers
b = {0,0,2,3,0,1};
Mb = monomialIdealsWithHilbertFunction({1,3,4,2,1,0}, R, GradedBettis => b); 
#Mb
member(M_0, Mb)

-- enumerating Betti tables of mon. ideals with a given Hilbert function
B = bettiTablesWithHilbertFunction({1,3,4,2,1,0}, R)
tB = bettiTablesWithHilbertFunction({1,3,4,2,1,0}, R, Count => true)
