newPackage(
  "AlgebraicOptimization",
  Version => "0.1", 
  Date => "May 12, 2020",
  Authors => {
    {Name => "Marc Harkonen", 
    Email => "harkonen@gatech.edu", 
    HomePage => "https://people.math.gatech.edu/~mharkonen3/"},
    {Name => "Jose Israel Rodriguez", 
    Email => "jose@math.wisc.edu", 
    HomePage => "https://www.math.wisc.edu/~jose/"},
    {Name => "Your name here",
    Email => "Your email here",
    HomePage => "Your page here"}
  },
  Headline => "A package for algebraic optimization",
  DebuggingMode => true,
  PackageImports => {"Elimination"}
)

export {
  -- Methods
  "projectiveDual",
  "conormalRing",
  "conormalVariety",
  "multiDegreeEDDegree",
  --More Methods
  "makeLagrangeRing","witnessLagrangeVariety","witnessCriticalIdeal",
  -- Options
  "DualVariable",
  --Types and keys
  "ConormalRing","CNRing","PrimalRing","DualRing","PrimalCoordinates","DualCoordinates",
  --More Types
  "LagrangeVarietyWitness","LagrangeRing",
  --More Keys
  "LagrangeVariable","PrimalIdeal","JacobianConstraint","AmbientRing","LagrangeCoordinates","PrimalWitnessSystem"
}

ConormalRing = new Type of HashTable;

conormalRing = method(Options => {DualVariable => null});
-- Creates a ConormalRing from a primal ring R
conormalRing Ring := ConormalRing => opts -> R -> (
  if not degreeLength R == 1 then error "expected degree length 1";
  u := if opts.DualVariable === null then symbol u else opts.DualVariable;
  dualR := (coefficientRing R)[u_0..u_(#gens R - 1)];
  new ConormalRing from {
    CNRing => R ** dualR,
    PrimalRing => R,
    DualRing => dualR,
    PrimalCoordinates => gens R,
    DualCoordinates => gens dualR
  }
)


conormalVariety = method(Options => options conormalRing);
-- Computes the conormal variety
conormalVariety (Ideal, ConormalRing) := Ideal => opts -> (I,C) -> (
  if not ring I === C.PrimalRing then error "expected ideal in primal ring";
  
  c := codim I;
  jacI := sub(diff(matrix{C.PrimalCoordinates}, transpose gens I), C.CNRing);
  jacBar := sub(matrix{C.DualCoordinates}, C.CNRing) || jacI;
  J' := sub(I,C.CNRing) + minors(c+1, jacBar);
  J := saturate(J', minors(c, jacI));
  J
)
TEST ///

///


projectiveDual = method(Options => options conormalRing);
-- (Alg. 5.1 in SIAM book)
-- Takes homogeneous ideal as input, returns ideal of dual of the projective variety
projectiveDual Ideal := Ideal => opts -> I -> (
  if not isHomogeneous I then error("Ideal has to be homogeneous");
  R := ring I;
  S := conormalRing(R, opts);

  primalCoordinates := S.PrimalCoordinates / (i->sub(i,S.CNRing));
  dualCoordinates := S.DualCoordinates / (i->sub(i,S.CNRing));

  J := conormalVariety(I, S);

  sub(eliminate(primalCoordinates, J), S.DualRing)
)

TEST ///
S = QQ[x_0..x_2]
I = ideal(x_2^2-x_0^2+x_1^2)
dualI = projectiveDual(I)
S = ring dualI
assert( dualI == ideal(S_0^2 - S_1^2 - S_2^2)) 
///


multiDegreeEDDegree = method();
multiDegreeEDDegree Ideal := ZZ => I -> (
  S := conormalRing ring I;
  N := conormalVariety(I,S);
  (mon,coef) := coefficients multidegree N;
  sub(sum flatten entries coef, ZZ)
)

TEST ///
R = QQ[x_0..x_3]
J = ideal det(matrix{{x_0, x_1, x_2}, {x_1, x_0, x_3}, {x_2, x_3, x_0}})
assert(multiDegreeEDDegree(J) == 13)
///



--Code for Lagrange multipliers


LagrangeRing = new Type of HashTable;
LagrangeVarietyWitness = new Type of MutableHashTable;

newRingFromSymbol = (n,s,kk)->(
    kk[s_0..s_(n - 1)]
    )

--TODO: decide if we want to create or make. 

makeLagrangeRing = method(Options => {DualVariable => null,LagrangeVariable => null});
-- Creates a LagrangeRing from a primal ring R
makeLagrangeRing (ZZ,Ring) := LagrangeRing => opts -> (c,R) -> (
  if not member(degreeLength R, {1,2}) then error "expected degree length 1 or 2";
  u := if opts.DualVariable === null then symbol u else opts.DualVariable;
  dualR := newRingFromSymbol(#gens R,u, (coefficientRing R));
  lambda := if opts.LagrangeVariable === null then symbol lambda else opts.LagrangeVariable;
  lagrangeR := newRingFromSymbol(c,lambda, (coefficientRing R));
  new LagrangeRing from {
    AmbientRing => R ** dualR**lagrangeR,
    LagrangeRing => lagrangeR,
    PrimalRing => R,
    DualRing => dualR,
    PrimalCoordinates => gens R,
    DualCoordinates => gens dualR,
    LagrangeCoordinates => gens lagrangeR
  }
)
makeLagrangeRing Ideal := LagrangeRing => opts -> I -> makeLagrangeRing(codim I,ring I)

TEST ///
R=QQ[x,y]
I=ideal(x^2+y^2-1)
LR = makeLagrangeRing(1,ring I)
--TODO: make a better test.
--Check keys
assert( sort\\toString\keys LR == sort\\toString\{AmbientRing, LagrangeRing, PrimalCoordinates, DualRing, DualCoordinates, LagrangeCoordinates, PrimalRing})
--Check values LR
assert (sort\\toString\values LR==sort\\toString\{QQ[x, y, u_0, u_1, lambda_0], QQ[lambda_0], {x, y}, QQ[u_0, u_1], {u_0, u_1}, {lambda_0}, R})
///



isCofficientRingInexact = R -> (
 -- This checks if kk is a ComplexField or RealField 
    kk:=ultimate(coefficientRing,R);
    member(kk,{ComplexField,RealField}) 
    )

findRegularSequence = I -> (
    c:=codim I;
    WI := sub(ideal(),ring I);
    b:=0;
    scan(numgens I, i -> (
	J :=  WI + ideal I_i;
	if codim J == b + 1 then (WI=J; b=b+1)
	)
    );
    WI)

witnessLagrangeVariety = method(Options => options makeLagrangeRing);
-- Computes a witness system for a lagrange variety 
witnessLagrangeVariety (Ideal,Ideal, LagrangeRing) := LagrangeVarietyWitness => opts -> (WI,I,AR) -> (
  if not ring I === AR.PrimalRing then error "expected ideal in primal ring";  
  c := #AR.LagrangeCoordinates;
  if numgens WI =!= c then error "expected numgens WI to equal the number of lagrange coordinates";  
  jacWI := sub(diff(matrix{AR.PrimalCoordinates}, transpose gens WI), AR.AmbientRing);
  jacBar := sub(matrix{AR.DualCoordinates}, AR.AmbientRing) || sub(jacWI,AR.AmbientRing);
  J0 := sub(WI,AR.AmbientRing);
  J1 := sub(I,AR.AmbientRing);
  J2 := ideal (sub(matrix{{1}|AR.LagrangeCoordinates},AR.AmbientRing)*jacBar);
  new LagrangeVarietyWitness from {
      LagrangeRing =>AR,
      PrimalWitnessSystem =>J0,
      PrimalIdeal=>J1,
      JacobianConstraint=>J2}
)
witnessLagrangeVariety (Ideal,Ideal) := LagrangeVarietyWitness => opts -> (WI,I) -> (
    AR:=makeLagrangeRing(numgens WI,ring I,opts);
    witnessLagrangeVariety(WI,I,AR,opts)
    )
witnessLagrangeVariety (Ideal) := LagrangeVarietyWitness => opts -> I -> (
  R:= ring I; 
  if isCofficientRingInexact(R) then error"Not implemented for RR or CC coefficient ring. Try makeLagrangeRing(ZZ,Ring).";
  WI := findRegularSequence I;--This may not be generically reduced.
  AR:=makeLagrangeRing(numgens WI,R,opts);
  witnessLagrangeVariety(WI,I,AR,opts)
  )

TEST ///
R=QQ[x,y]
I=ideal(x^2+y^2-1)
LVW = witnessLagrangeVariety(I,I)
--TODO better test
--Check keys 
assert( sort\\toString\keys LVW == sort\\toString\{JacobianConstraint, LagrangeRing, PrimalIdeal, PrimalWitnessSystem})
--Check values TODO
--Check degree
assert(4 == degree (LVW))

LVW =witnessLagrangeVariety (I,I, makeLagrangeRing I)
--Check keys 
assert( sort\\toString\keys LVW == sort\\toString\{JacobianConstraint, LagrangeRing, PrimalIdeal, PrimalWitnessSystem})
--Check values TODO
--Check degree
assert(4 == degree (LVW))

LVW =witnessLagrangeVariety I
--Check keys 
assert( sort\\toString\keys LVW == sort\\toString\{JacobianConstraint, LagrangeRing, PrimalIdeal, PrimalWitnessSystem})
--Check values TODO
--Check degree
assert(4 == degree (LVW))

///

coefficientRing(LagrangeVarietyWitness) := LVW ->coefficientRing LVW#LagrangeRing#AmbientRing
ring (LagrangeVarietyWitness) := LVW -> ring LVW#JacobianConstraint 

-- Degree of LagrangeVarietyWitness
--TODO: How to document this?
degree (List,LagrangeVarietyWitness) := (v,LVW) -> (    
    if degreeLength  LVW.LagrangeRing#PrimalRing==2 then(
	u:=gens coefficientRing LVW;
	if #v=!=#u then error "data does not agree with number of parameters. ";
    	subData :=apply(u,v,(i,j)->i=>j);
	return degree sub(LVW#PrimalIdeal+LVW#JacobianConstraint,subData)
	)
    else error"degreeLength is not 2."
    )
degree (Nothing,LagrangeVarietyWitness) := (a,LVW) -> (
	u:=gens coefficientRing ring (LVW#PrimalIdeal);
	kk:=ultimate(coefficientRing,LVW);
    	v :=apply(u,i->random kk);
	degree(v,LVW)
	)
degree (LagrangeVarietyWitness) := LVW -> degree(LVW#PrimalIdeal+LVW#JacobianConstraint)




TEST///
    R=QQ[x,y,z,w]
    WI = ideal(x*z-y^2,y*w-z^2)
    I = ideal(x*w-z*y)+WI 
    codim I
    LVW1 = witnessLagrangeVariety(WI,I)
    LVW2 = witnessLagrangeVariety I
    assert(LVW1#PrimalWitnessSystem =!=    LVW2#PrimalWitnessSystem )
    assert(16 == degree LVW1)
    assert(16 == degree LVW2)
    
    R=QQ[u][x,y,z,w]

    WI = ideal(u*x*z-y^2,y*w-z^2)
    I = ideal(u*x*w-z*y)+WI 
    LVW1 = witnessLagrangeVariety(WI,I)
    assert(16 == degree({1},LVW1)	)
    assert(16 == degree(,LVW1)	)
    assert(6 == degree({0},LVW1)	)
    assert(33==degree LVW1)

    LVW2 = witnessLagrangeVariety I
    assert(16 == degree({1},LVW2)	)
    assert(16 == degree(,LVW2)	)
    assert(3 == degree({0},LVW2)	)
    assert(36==degree LVW2)

///


--witnessCriticalVariety and Optimization degree
witnessCriticalIdeal = method(Options => options makeLagrangeRing);
witnessCriticalIdeal (List,List,LagrangeVarietyWitness) := (Ideal,Ideal,Ideal) => opts  -> (v,g,LVW) ->(
--Output: substitution of (WI,I,LVW) 
    if degreeLength  LVW#LagrangeRing#PrimalRing==2 then(
	u:=gens coefficientRing (LVW);
	if #v=!=#u then error "data does not agree with number of parameters. ";
    	LR:=LVW#LagrangeRing;
	y := drop(drop(gens ring LVW,#gens LR#PrimalRing),-# gens LR#LagrangeRing);
	subDualVars := apply(y,g,(i,j)->i=>sub(j,ring LVW));
	subVars:=subDualVars;
	scan(gens ring LVW,X->if not member(X,y) then subVars=append(subVars,X=>X) );
	gradSub := map(ring LVW,ring LVW,subVars);	
	subData :=apply(u,v,(i,j)->i=>j);
	--TODO: Issue with denominators.
	return (sub(gradSub(LVW#PrimalWitnessSystem),subData),sub(gradSub(LVW#PrimalIdeal),subData),sub(gradSub(LVW#JacobianConstraint),subData))
	)
    else error"degreeLength is not 2."
    )


witnessCriticalIdeal (List,RingElement,LagrangeVarietyWitness) := (Ideal,Ideal,Ideal) =>opts -> (v,psi,LVW) -> (
    g := apply(gens ring psi,x->diff(x,psi));
    witnessCriticalIdeal(v,g,LVW);
    )
--TODO : Establish naming conventions.
TEST///
R=QQ[a,b][x,y]
I=ideal(x^2+y^2-1)
WI=I
LVW = witnessLagrangeVariety(WI,I)
ring LVW
WCI = witnessCriticalIdeal({7,99},{x-a,y-b},LVW)
assert (2 ==degree (WCI_1+WCI_2))--ED degree of circle

R=QQ[a,b][x,y]
I=ideal(x^2+3*y^2-1)
WI=I
LVW = witnessLagrangeVariety(WI,I)
ring LVW
WCI = witnessCriticalIdeal({7,99},{x-a,y-b},LVW)
assert (4 ==degree (WCI_1+WCI_2))--ED degree of ellipse
///




TEST///
R=QQ[a,b][x,y]
I=ideal(x^2+y^2-1)
WI=I
LVW = witnessLagrangeVariety(WI,I)
ring LVW
assert (2 ==degree witnessCriticalIdeal({7,99},{x-a,y-b},LVW))--ED degree of circle

R=QQ[a,b][x,y]
I=ideal(x^2+3*y^2-1)
WI=I
LVW = witnessLagrangeVariety(WI,I)
ring LVW
assert (4 ==degree witnessCriticalIdeal({7,99},{x-a,y-b},LVW))--ED degree of ellipse
///

--TODO : bertiniSolve
--TODO : monodromySolve

TEST///
R=QQ[a,b][x,y]
I=ideal(x^2+y^2-1)
WI=I
LVW = witnessLagrangeVariety(WI,I)
ring LVW
needsPackage"Bertini"

bertiniZeroDimSolve (WCI_0+WCI_2)_*)

makeB'InputFile(storeBM2Files,
    ring LVW
    AffVariableGroup=>{basis({1,0},R),basis({0,2},R)}
    )




-*
optimizationDegree = method(Options => options makeLagrangeRing);
optimizationDegree (List,List,LagrangeVarietyWitness) := ZZ => opts  -> (v,g,LVW) ->(
    CI:=witnessCriticalIdeal(v,g,LVW);
    CI = CI+LVW#PrimalIdeal;
    scan(g,i->if ring g ==frac ring CI then CI:=saturate(CI,denominator g))
    )
*-

-- Documentation below

beginDocumentation()

-- template for package documentation
doc ///
Key
  AlgebraicOptimization
Headline
  Package for algebraic optimization
Description
  Text
    Todo
  Example
    todo
Caveat
SeeAlso
///

doc ///
Key
  ConormalRing
///


-- template for function documentation
doc ///
Key
  projectiveDual
  (projectiveDual, Ideal)
  [projectiveDual, DualVariable]
Headline
  Compute projective dual
Usage
  projectiveDual(I)
Inputs
  I:
    a homogeneous @TO2{Ideal, "ideal"}@
Outputs
  :Ideal
    the projective dual of {\tt I}
--Consequences
--  asd
Description
  Text
    Compute the projective dual of a homogeneous ideal.
    For example, the snippet below shows that the dual of a circle is a circle.

  Example
    S = QQ[x_0..x_2]
    I = ideal(x_2^2-x_0^2+x_1^2)
    projectiveDual(I)

  Text
    The option {\tt DualVariable} specifies the basename for the dual variables
  Example
    projectiveDual(I,DualVariable => y)
--  Code
--    todo
--  Pre
--    todo
--Caveat
--  todo
--SeeAlso
--  todo
///

doc ///
Key
  conormalRing
  [conormalRing, DualVariable]
Headline
  Creates a ring with primal and dual variables
Usage
  conormalRing(R)
Inputs
  R:Ring
Outputs
  :ConormalRing
Description
  Text
    Creates an element of type ConormalRing
  Example
    R = QQ[x_0..x_2]
    conormalRing(R)
    conormalRing(R, DualVariable => l)
Caveat
  The ring $R$ must have degree length 1
SeeAlso
  conormalVariety
///

doc ///
Key
  conormalVariety
  (conormalVariety, Ideal, ConormalRing)
--Headline
--  todo
Inputs
  I:Ideal
    defined in the primal variables only
  S:ConormalRing
Usage
  conormalVariety(I,S)

Caveat
  The ring containing $I$ and $p$ must have primal variables in degree $\{1,0\}$ and dual variables in degree $\{0,1\}$.
  Such a ring can be obtained using @TO{conormalRing}@.
///

doc ///
Key
  multiDegreeEDDegree
  (multiDegreeEDDegree, Ideal)
Inputs
  I:Ideal
Outputs
  :ZZ
    the ED-degree of $I$
Usage
  multiDegreeEDDegree(I)
Description
  Text
    Computes the ED degree symbolically by taking the sum of multidegrees of the conormal ideal. 
    See theorem 5.4 in Draisma et. al. The Euclidean Distance Degree of an Algebraic Variety https://arxiv.org/abs/1309.0049 

    As an example, we see that the ED-degree of Caylay's cubic surface is 13
  Example
    R = QQ[x_0..x_3]
    J = ideal det(matrix{{x_0, x_1, x_2}, {x_1, x_0, x_3}, {x_2, x_3, x_0}})
    multiDegreeEDDegree(J)

Caveat
  The conormal variety cannot intersect the diagonal $\Delta(\mathbb{P}^{n-1}) \subset \mathbb{P}^{n-1} \times \mathbb{P}^{n-1}$.
  At the moment this is not checked.
///

TEST ///
  -- test code and assertions here
  -- may have as many TEST sections as needed
///


doc ///
Key
  makeLagrangeRing
  (makeLagrangeRing, ZZ,Ring)
  (makeLagrangeRing, Ideal)
Headline
  Make a ring for using Lagrange multipliers
Usage
  makeLagrangeRing(I)
  makeLagrangeRing(c,I)  
Inputs
  I:
    an  @TO2{Ideal, "ideal"}@    
  c:
    the number of Lagrange multipliers
    
Outputs
  :LagrangeRing
    a desciption of the output is needed TODO
--Consequences
--  asd
Description
  Text
    TODO.

  Example
    R=QQ[x,y]
    I=ideal(x^2+y^2-1)
    LR = makeLagrangeRing(1,ring I)

--  Code
--    todo
--  Pre
--    todo
--Caveat
--  todo
--SeeAlso
--  todo
///
  
doc ///
Key
  witnessLagrangeVariety
  (witnessLagrangeVariety, Ideal,Ideal, LagrangeRing)
  (witnessLagrangeVariety, Ideal, Ideal)
  (witnessLagrangeVariety, Ideal)
Headline
  witness a Lagrange variety
Usage
  witnessLagrangeVariety(WI,I,LR)  
  witnessLagrangeVariety(WI,I)  
  witnessLagrangeVariety(I)
Inputs
  I:
    an  @TO2{Ideal, "ideal"}@    
  WI:
    a complete intersection with I as an irreducible component
  LR:
    a LagrangeRing    
Outputs
  :LagrangeVarietyWitness
    a desciption of the output is needed TODO
--Consequences
--  asd
Description
  Text
    TODO.

  Example
    R=QQ[x,y,z,w]
    WI = ideal(x*z-y^2,y*w-z^2)
    I = ideal(x*w-z*y)+WI 
    codim I
    LVW1 = witnessLagrangeVariety(WI,I)
    LVW2 = witnessLagrangeVariety I
    LVW1#PrimalWitnessSystem =!=    LVW2#PrimalWitnessSystem 

--  Code
--    todo
--  Pre
--    todo
--Caveat
--  todo
--SeeAlso
--  todo
///

  
  
end


--Example
restart
path={"/Users/jo/Documents/GoodGit/M2020/Workshop-2020-Cleveland/alg-stat/AlgebraicOptimization"}|path  
loadPackage("AlgebraicOptimization",Reload=>true)
check"AlgebraicOptimization"
installPackage"AlgebraicOptimization"

M= QQ[x_1..x_2]
I = ideal(4*(x_1^4+x_2^4),4*x_1^3,4*x_2^3)
dualI = projectiveDual(I)
radical I==I
S = ring dualI
