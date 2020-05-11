restart
needsPackage("MonomialIntegerPrograms")

-- quick function for generating a random monomial ideal
rmi := (R, j, k, l) -> monomialIdeal(apply(j, i -> product apply(take(random gens R, 1 + random k), x -> x^(1 + random l))))


-- dimension of mon ideal
R = QQ[x_1..x_100];
I = rmi(R, 30, 20, 3);
print I
time(dim I)
time(dimensionIP I)

-- solving info is saved in temporary directory
ScipPrintLevel = 0 -- no info
ScipPrintLevel = 1 -- location of temporary directory
ScipPrintLevel = 2 -- + error log if it exists
ScipPrintLevel = 3 -- + IP formulation
ScipPrintLevel = 4 -- + complete solving output from SCIP

-- degree of mon ideal
R = QQ[x_1..x_50];
I = rmi(R, 25, 15, 3);
time(degree I)
time(degreeIP I)

-- "top" minimal primes
R = QQ[a..j];
I = rmi(R, 10, 5, 1);
print I
minimalPrimes I
select(oo, a -> # first entries gens a == codim I)
topMinimalPrimesIP I

-- GOAL #1: make "top" minimal primes work for non squarefree
R = QQ[a..j];
I = rmi(R, 10, 5, 2);
print I
minimalPrimes I
select(oo, a -> # first entries gens a == codim I)
topMinimalPrimesIP I

-- GOAL #2: function for all minimal primes 

-- OTHER GOALS relate to functions for enumerating monomial ideals 
-- satisfying certain constraints on Hilbert function values and 
-- Betti numbers, see doc page

viewHelp("sample session in Monomial Integer Programs")
