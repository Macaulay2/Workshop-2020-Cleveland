newPackage(
  "AlgebraicOptimization",
  Version => "0.1", 
  Date => "May 12, 2020",
  Authors => {
    {Name => "Marc Harkonen", 
    Email => "harkonen@gatech.edu", 
    HomePage => "https://people.math.gatech.edu/~mharkonen3/"},
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
  -- Options
  "DualVariable",
  --Types and keys
  "ConormalRing","CNRing","PrimalRing","DualRing","PrimalCoordinates","DualCoordinates",
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
	J := ideal  WI + ideal I_i;
	if codim J == b + 1 then (WI=J; b=b+1)
	)
    );
    WI)

witnessLagrangeVariety = method(Options => options makeLagrangeRing);
-- Computes a witness system for a lagrange variety 
witnessLagrangeVariety (Ideal,Ideal, LagrangeRing) := LagrangeVarietyWitness => opts -> (WI,I,AR) -> (
  if not ring I === AR.PrimalRing then error "expected ideal in primal ring";  
  c := #AR.LagrangeCoordinates;
  if numgens I =!= c then error "expected numgens WI to equal the number of lagrange coordinates";  
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
  makeLagrangeRing(numgens WI,R,opts)
  )
-*
-- Degree of LagrangeVarietyWitness
degree (List,LagrangeVarietyWitness) := (v,LVW) -> (
    if degreeLength LVW#PrimalRing==2 then(
	u:=gens coefficientRing (LVW#PrimalRing);
	if #v=!=#u then error "data does not agree with number of parameters. ";
    	subData :=apply(u,v,(i,j)->i=>j);
	return degree sub(LVW#PrimalIdeal+LVW#JacobianConstraint,subData)
	)
    else error"degreeLength is not 2."
    )
degree (Nothing,LagrangeVarietyWitness) := LVW -> (
    if degreeLength LVW#PrimalRing==2 then(
	u:=gens coefficientRing (LVW#PrimalRing);
	kk:=coefficientRing first u;
    	v :=apply(u,i->i=>random kk);
	return degree(v,LVW)
	)
    else error"degreeLength is not 2."
    )
degree (LagrangeVarietyWitness) := LVW -> degree(LVW#PrimalIdeal+LVW#JacobianConstraint)


--witnessCriticalVariety and Optimization degree
witnessCriticalIdeal := (List,List,LagrangeVarietyWitness) := (v,g,LVW) -> (
    if degreeLength LVW#PrimalRing==2 then(
	u:=gens coefficientRing (LVW#PrimalRing);
	if #v=!=#u then error "data does not agree with number of parameters. ";
    	AR:=LVW.LagrangeRing;
	y := drop(drop(gens AR,#gens AR.PrimalRing),# gens AR.LagrangeRing);
	subDualVars := apply(y,g,(i,j)->i=>j);
	gradSub := map(AR,ring LVW#PrimalRing,subDualVars);--back in primalRing.	
	subData :=apply(u,v,(i,j)->i=>j);
	--Issue with denominators.
	return sub(gradSub(LVW#PrimalIdeal+LVW#JacobianConstraint),subData)
	)
    else error"degreeLength is not 2."
    )

witnessCriticalIdeal := (List,RingElement,LagrangeVarietyWitness) := (v,psi,LVW) -> (
    g := apply(gens ring psi,x->diff(x,psi));
    witnessCriticalIdeal(v,g,LVW);
    )

optimizationDegree(v,g,LVW)-> (
    CI:=witnessCriticalIdeal(v,g,LVW);
    CI = CI+LVW#PrimalIdeal;
    scan(g,i->if ring g ==frac ring CI then CI:=saturate(CI,denominator g))
    )


TEST ///
--lagrangeRing(2,QQ[x1,x2])

R=QQ[x,y]
I=ideal(x^2+y^2-1)
LR = makeLagrangeRing(1,ring I)
LVW = witnessLagrangeVariety(I,I,LR)
peek LVW

R=QQ[x,y]
I=ideal(x^2+y^2-1)
LVW = witnessLagrangeVariety(I,I)
peek LVW
degree (LVW)

///
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

  
end


--Example
restart
path={"/Users/jo/Documents/GoodGit/M2020/Workshop-2020-Cleveland/alg-stat/AlgebraicOptimization"}|path  
loadPackage("AlgebraicOptimization",Reload=>true)
M= QQ[x_1..x_2]
I = ideal(4*(x_1^4+x_2^4),4*x_1^3,4*x_2^3)
dualI = projectiveDual(I)
radical I==I
S = ring dualI
