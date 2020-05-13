needsPackage "IntegralClosure"
integralClosure(Ideal, RingElement, ZZ) := opts -> (I,a,D) -> (
    S := ring I;
    if a % I != 0 then error "The ring element should be an element of the ideal.";
    if ((ideal 0_S):a) != 0 then error "The given ring element must be a nonzerodivisor of the ring.";
    z := local z;
    w := local w;
    Reesi := (flattenRing reesAlgebra(I,a,Variable => z))_0;
    Rbar := integralClosure(Reesi, opts, Variable => w);
    zIdeal := ideal(map(Rbar,Reesi))((vars Reesi)_{0..numgens I -1});
    zIdealD := module zIdeal^D;
    L := prepend(D,toList(degreeLength S:null));
    RbarPlusD := image basisOfDegreeD(L,Rbar); --all gens of first-degree D.
    gD := matrix inducedMap(RbarPlusD, zIdealD);
    mapback := map(S,Rbar, matrix{{numgens Rbar-numgens S:0_S}}|(vars S), DegreeMap => d -> drop(d, 1));
    M := coker mapback presentation RbarPlusD;
--    ID := I^D;
    ID = (trim I)^D;
    phi := map(M, module ID, mapback gD);
    assert(isHomogeneous phi);
    assert(isWellDefined phi);
    error "debug me";
--    extendIdeal(ID,a^D,phi)
    extendIdeal phi
    )

findGrade2Ideal = method()
findGrade2Ideal Module := Ideal => M -> (
    --finds the unique grade 2 ideal isomorphic to M, if there is one.
    psi := syz transpose presentation M;
    trim ideal psi
    )

extendIdeal = method()
extendIdeal(Ideal, RingElement, Matrix) := Ideal => (I,a,phi) -> (
    --input: f: (module I) --> M, an inclusion from an ideal to a module that is isomorphic
    --to an ideal J containing I.
    --a is an element of I that is a nzd in R.
    --output: generators of J, so that f becomes the inclusion I subset J.
    --note f^{-1}(aM) = aJ
    --answer is aJ:a
    M := target phi;
    aJ := trim ideal ker(inducedMap(M/(a*M), M)*phi);
    J := trim(aJ:a);
    J
    )

extendIdeal(Ideal, Matrix) := Ideal => (I, phi) -> (
    --input: f: (module I) --> M, an inclusion from an ideal 
    --           to a module that is isomorphic to an ideal J containing I.
    --output: generators of J, so that f becomes the inclusion I subset J.
    inc := transpose gens I;
    phi0 := transpose matrix phi;
    assert(target inc == target phi0);
    sz := syz transpose presentation target phi;
    assert(source phi0 == target sz);
    preimageInc := inc // (phi0 * sz);
    ideal (sz * preimageInc)
    )

extendIdeal(Matrix) := Ideal => phi -> (
    --input: f: (module I) --> M, an inclusion from an ideal 
    --to a module that is isomorphic to the inclusion of I into an ideal J containing I.
    --output: the ideal J, so that f becomes the inclusion I subset J.
    inc := transpose gens source phi;
    phi0 := transpose matrix phi;
    (q,r) = quotientRemainder(inc,phi0);
    if r !=0 then error "phi is not isomorphic to an inclusion of ideals";
    trim ideal q -- is the "trim" doing anything?
    )
--    sz := syz transpose presentation target phi;
--    assert(source phi0 == target sz);
--    preimageInc := inc // (phi0 * sz);
--    ideal (sz * preimageInc)
--  )
-*
--bits of old code:      
	  return J;
          iota = matrix phi;
	  phi1 = map(M,cover(a*M), inducedMap(M,a*M));
	  psi = phi1//phi;
          trim ideal psi)
*-

integralClosure(Ideal,ZZ) := Ideal => o -> (I,D) -> integralClosure(I, I_0, D, o)
integralClosure(Ideal,RingElement) := Ideal => o -> (I,a) -> integralClosure(I, a, 1, o)
integralClosure(Ideal) := Ideal => o -> I -> integralClosure(I, I_0, 1, o)

    
--basisOfDegreeD (List,Module)
--basisOfDegreeD (List,Ideal)


basisOfDegreeD = method()
basisOfDegreeD (List,Ring) := Matrix => (L,R) ->(
    --assumes degrees of R are non-negative
    --change to a heft value sometime.
    PL := positions(L, d-> d=!=null);    
    PV := positions(degrees R, D->any(PL,i->D#i > 0));
    PVars := (gens R)_PV;
    PDegs := PVars/degree/(D->D_PL);
      kk := ultimate(coefficientRing, R);
    R1 := kk(monoid[PVars,Degrees =>PDegs]);
    back := map(R,R1,PVars);
    g := back basis(L_PL, R1);
    map(target g,,g)
    )

///
R = ZZ/101[a,b,c,Degrees=>{{1,1,0},{1,0,0},{0,0,2}}]
L = {2,2,null}
basisOfDegreeD({2,null,2}, S)

S = ZZ/101[vars(0..10), Degrees => {{2, 6}, {1, 3}, {1, 3}, {1, 3}, {1, 3}, {0, 1}, {0, 1}, {0, 1}, {0, 1}, {0, 1}, {0, 1}}]
basisOfDegreeD({2,null}, S)
///

end--

restart
needs "bug-integralClosure.m2"
TEST///
    S = ZZ/101[a,b,c,d]
    K =ideal(a,b)
    I = c*d*K
    M = module (c*K)
    M' = module(d*K)
    phi = map(M,module I,d*id_M)
    phi' = map(M',module I,c*id_M')
    assert(isWellDefined phi)
    assert(extendIdeal phi == c*K)
    assert(extendIdeal phi'== d*K)    
///

TEST///
    S = ZZ/101[a,b,c]/ideal(a^3-b*(b-c)*(b+c))
    K =ideal(a,b)
    I = c*(b+c)*K
    M = module (c*K)
    M' = module((b+c)*K)
    phi = map(M,module I,(b+c)*id_M)
    phi' = map(M',module I,c*id_M')
    assert(isWellDefined phi)
    assert(isWellDefined phi')    
    assert(extendIdeal phi == c*K)
    assert(extendIdeal phi'== (b+c)*K)    
    integralClosure I == I
///

TEST///
-*
  restart
  needs "bug-integralClosure.m2"
*-
    S = ZZ/101[a,b,c]/ideal(a^3-b^2*c)
    K =ideal(a,b)
    I = c*(b+c)*K
    M = module (c*K)
    M' = module((b+c)*K)
    phi = map(M,module I,(b+c)*id_M)
    phi' = map(M',module I,c*id_M')
    assert(isWellDefined phi)
    assert(isWellDefined phi')    
    assert(extendIdeal(I,phi)== c*K)
    assert(extendIdeal(I,phi')== (b+c)*K)    
    integralClosure I -- wrong!!

    -- inside the debugger, during `integralClosure I`
    isWellDefined phi -- true.
    
    S = ZZ/101[a,b,c]/ideal(a^3-b^2*c)
    ID = ideal(b^2*c+b*c^2,a*b*c+a*c^2)
    M = (cokernel matrix {{-a, 0, 0, -c}, {b, -a, 0, 0}})
    phi = map(M, module ID, matrix {{1_S, 0}, {0, 1}})
    isWellDefined phi
    extendIdeal(ID, phi) -- should not be 0, must contain I?
      -- unless the hypothesis that M is isomorphic to an ideal
      -- containing ID is incorrect...?
///




S=ZZ/32003[a,b,c,d,e,f]
I=ideal(a*b*d,a*c*e,b*c*f,d*e*f);
trim(J=I^2)
K=integralClosure(I,I_0,2) -- integral closure of J = I^2
assert(K == J+ideal"abcdef") --doesn't work yet on this example!

Ibar = extendIdeal(ID,I_0^2,phi)
F=ideal(a*b*c*d*e*f);
gens(F^2)%J^2 -- so F satisfies X^2-m, with m\in J^2.
assert(isSubset(F, K)) -- F should be contained in the integral closure.
assert(K != J)

R = Rbar
L = {2,null}

-- stopped at extendIdeal.
-- Let's figure out the lift.
isWellDefined phi -- false!! This is the first order of business.
extendIdeal(ID, phi)
sz = syz transpose presentation M -- this is the answer in this example.
ff = ((transpose matrix phi) * sz)

inc = transpose gens source phi
transpose matrix phi
(inc // ff)
source phi
target phi

-- One possible bug:
L = reesIdeal(I,I_0,Variable => z)
g = map(ring I, ring L, (gens I))
g L -- nonzero!!
last (flattenRing ring L)
oo L

reesAlgebra(I, I_0, Variable => getSymbol "z")
