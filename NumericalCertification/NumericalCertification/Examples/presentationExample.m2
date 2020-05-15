restart
needsPackage("NumericalCertification", FileName => "~/M2Cleveland/Workshop-2020-Cleveland/NumericalCertification/NumericalCertification.m2",Reload=>true)
-- cbms2 system : 7 roots (6 regular roots, 1 multiple root at the origin)
R = CC[x,y,z]
F = polySystem {(x-y)^3 - z^2, (z-x)^3 - y^2, (y-z)^3 - x^2} 
listOfSols = solveSystem F 
length listOfSols -- 14 solutions.

-- certify using alpha-theory
certifyRegularSolution(F, listOfSols)
alphaTheoryCertification(F,listOfSols)


-- certify using alphaCertified
loadPackage("NumericalCertification", FileName=> "~/M2Cleveland/Workshop-2020-Cleveland/NumericalCertification/NumericalCertification.m2", 
     Reload => true, Configuration => {"ALPHACERTIFIEDexec"=>"~/alphaCertifiedLinux64"})
alphaCertified(F, listOfSols)
alphaCertified(F, listOfSols, PRECISION => 4096)
toACertifiedPoly F -- input file


-- certify multiple roots.
P = last listOfSols; -- one of numerical roots of the multiple root
A = Aoperator(F,P)
numericalRank A -- we can certify if A is full-rank

listOfMultipleRoots = drop(listOfSols, {0,5}) -- list of numerical roots of the multiple root.
certifyCluster(F, first listOfMultipleRoots)
apply(listOfMultipleRoots, i -> certifyCluster(F, i))



certifySolutions(F, listOfSols)

