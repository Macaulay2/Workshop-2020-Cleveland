uninstallPackage "RandomRationalPoints";
loadPackage "RandomRationalPoints";
installPackage "RandomRationalPoints";
check RandomRationalPoints

allowableThreads = 8;
loadPackage "RandomRationalPoints";
loadPackage "FastLinAlg";

T = ZZ/101[x1,x2,x3,x4,x5,x6,x7];
 I =  ideal(x5*x6-x4*x7,x1*x6-x2*x7,x5^2-x1*x7,x4*x5-x2*x7,x4^2-x2*x6,x1*x4-x2*x5,
x2*x3^3*x5+3*x2*x3^2*x7+8*x2^2*x5+3*x3*x4*x7-8*x4*x7+x6*x7,x1*x3^3*x5+3*x1*x3^2*x7
+8*x1*x2*x5+3*x3*x5*x7-8*x5*x7+x7^2,x2*x3^3*x4+3*x2*x3^2*x6+8*x2^2*x4+3*x3*x4*x6
-8*x4*x6+x6^2,x2^2*x3^3+3*x2*x3^2*x4+8*x2^3+3*x2*x3*x6-8*x2*x6+x4*x6,x1*x2*x3^3
+3*x2*x3^2*x5+8*x1*x2^2+3*x2*x3*x7-8*x2*x7+x4*x7,x1^2*x3^3+3*x1*x3^2*x5+8*x1^2*x2
+3*x1*x3*x7-8*x1*x7+x5*x7);
M = jacobian I;
J = I + chooseGoodMinors(5, 4, M);

extendingIdealByNonVanishingMinor(I, M, 4, Strategy=>GenericProjection)

 new OptionTable from {
    Strategy=>BruteForce, 
    Homogeneous => true, 
    MaxChange => 0, 
    Codimension => null,
    IntersectionAttempts => 20,
    ProjectionAttempts => 20,
    ExtendField => false,
    PointCheckAttempts => 100
}

R = ZZ/5[x,y]
R = ZZ/11[x,y,z]
I2 = intersect(ideal(x,y),ideal(x,z), ideal(y,z))
