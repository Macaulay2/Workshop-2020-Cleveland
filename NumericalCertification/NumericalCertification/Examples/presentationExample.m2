restart
needsPackage("NumericalCertification", FileName => "NumericalCertification.m2")
-- cbms2 system : 7 roots (6 regular roots, 1 multiple root)
R = CC[x,y,z]
F = polySystem {(x-y)^3 - z^2, (z-x)^3 - y^2, (y-z)^3 - x^2} 
listOfSols = solveSystem F 
length listOfSols -- 14 solutions.

-- certify using alpha-theory
certifySolutions(F, listOfSols)
certifyCount(F,listOfSols)


-- certify using alphaCertified
loadPackage("NumericalCertification", FileName=> "NumericalCertification.m2", 
     Reload => true, Configuration => {"ALPHACERTIFIEDexec"=>"~/alphaCertifiedLinux64/"})
alphaCertified(F, listOfSols)
toACertifiedPoly F -- input file


-- certify multiple roots.
P = last listOfSols; -- one of numerical roots of the multiple root
V = computeOrthoBasis(F,P);
A = Aoperator(F,P,V)
numericalRank A -- we can certify if A is full-rank

listOfMultipleRoots = drop(listOfSols, {0,5}) -- list of numerical roots of the multiple root.
apply(listOfMultipleRoots, i -> certifyRootMultiplicityBound(F, i))
