--This is Example 3.5 from Kisun's paper
restart
loadPackage("NumericalCertification",FileName=>"../../NumericalCertification.m2",Reload=>true)

R = QQ[x,y,z];
F = polySystem {x^3-y*z,y^3-x*z,z^3-x*y};
p = point matrix{{0/1,0/1,0/1}};

M = random(QQ^3, QQ^3)
M = rationalUnitaryMatrix 3
randomTransform = flatten entries(M * transpose vars R)
F' = polySystem sub(transpose matrix{{x^3-y*z,y^3-x*z,z^3-x*y}}
   , {x=>randomTransform#0, y=>randomTransform#1, z=>randomTransform#2})
V = computeOrthoBasis(F',p)
A = Aoper2(F',p,V)


A = Aoperator(F,p,V)
det A


--This is Example 2 from Dayton/Zeng
restart
loadPackage("NumericalCertification",FileName=>"../../NumericalCertification.m2",Reload=>true)

S = QQ[i]/(i^2+1);
R = S[x,y];
F = polySystem {x-y+x^2,x-y+y^2};
p = point matrix{{i/10^12,(1+i)/10^12}};

V = computeOrthoBasis(F,p)
A = Aoperator(F,p,V)
det A

--non-deterministic, but it seems we're unable to verify this is a multiple root.
certifyRootMultiplicityBound(F,p)


--This is Example 3.6 from Kisun's paper (modified to be polynomials)
restart
loadPackage("NumericalCertification",FileName=>"../../NumericalCertification.m2",Reload=>true)

S = QQ[i]/(i^2+1)
R = S[x,y,z];
F = polySystem {(y-z)^3-(x+y+z)*((x-z)-(x-z)^3/6),(x-z)^3-(y-z)*((x+y+z)-(x+y+z)^3/6),-(x+y+z)^3+(x-z)*((y-z)-(y-z)^3/6)};
p = point matrix{{1/10^15,(1+i)/10^15,(2+3*i)/10^15}};

V = computeOrthoBasis(F,p)
A = Aoperator(F,p,V)
det A

--We are able to verify that this is a multiple root of multiplicity 8 or more. 
certifyRootMultiplicityBound(F,p)





--- More examples



-- mth191, kappa : 2, multiplicity : 4
restart
loadPackage("NumericalCertification",FileName=>"../../NumericalCertification.m2",Reload=>true)

R = CC[x,y,z]
F = polySystem {x^3+(y+1)^2+z^2-1, x^2+(y+1)^3+z^2-1, x^2+(y+1)^2+z^3-1}
P = last solveSystem F;

V = computeOrthoBasis(F,P)
A = Aoper2(F,P,V)

certifyRootMultiplicityBound(F,P) -- false




-- Ojika 2, kappa : 1, multiplicity : 2 
R = QQ[x,y,z]
F = polySystem {(x+1)^2+y+z-1, (x+1)+y^2+z-1, (x+1)+y+z^2-1}
P = (solveSystem F)#-3

V = computeOrthoBasis(F,P)
A = Aoper2(F,P,V)

certifyRootMultiplicityBound(F,P) -- false


-- KSS, kappa : 4, multiplicity : 16
R = QQ[x1,x2,x3,x4,x5]
F = polySystem ideal((x1+1)^2-2*(x1+1)+1+x1+x2+x3+x4+x5, (x2+1)^2-2*(x2+1)+1+x1+x2+x3+x4+x5, (x3+1)^2-2*(x3+1)+1+x1+x2+x3+x4+x5, (x4+1)^2-2*(x4+1)+1+x1+x2+x3+x4+x5, (x5+1)^2-2*(x5+1)+1+x1+x2+x3+x4+x5)
P = last solveSystem F
-- P = point {{0/1,0/1,0/1,0/1,0/1}}

V = computeOrthoBasis(F,P)
A = Aoper2(F,P,V)

certifyRootMultiplicityBound(F,P) -- false
