--This is Example 3.5 from Kisun's paper
restart
loadPackage("NumericalCertification",FileName=>"../../NumericalCertification.m2",Reload=>true)

R = QQ[x,y,z];
F = polySystem {x^3-y*z,y^3-x*z,z^3-x*y};
p = point matrix{{0/1,0/1,0/1}};

V = computeOrthoBasis(F,p)
A = Aoperator(F,p,V)
det A


--This is Example 2 from Dayton/Zeng
restart
loadPackage("NumericalCertification",FileName=>"../../NumericalCertification.m2",Reload=>true)

R = QQ[x,y];
F = polySystem {x-y+x^2,x-y+y^2};
p = point matrix{{0/1,0/1}};

V = computeOrthoBasis(F,p)
A = Aoperator(F,p,V)
det A

--non-deterministic, but it seems we're unable to verify this is a multiple root.
certifyRootMultiplicityBound(F,p)


--This is Example 3.6 from Kisun's paper (modified to be polynomials)
restart
loadPackage("NumericalCertification",FileName=>"../../NumericalCertification.m2",Reload=>true)

R = QQ[x,y,z];
F = polySystem {(y-z)^3-(x+y+z)*((x-z)-(x-z)^3/6),(x-z)^3-(y-z)*((x+y+z)-(x+y+z)^3/6),-(x+y+z)^3+(x-z)*((y-z)-(y-z)^3/6)};
p = point matrix{{0/1,0/1,0/1}};

V = computeOrthoBasis(F,p)
A = Aoperator(F,p,V)
det A

--We are able to verify that this is a multiple root of multiplicity 8 or more. 
certifyRootMultiplicityBound(F,p)

