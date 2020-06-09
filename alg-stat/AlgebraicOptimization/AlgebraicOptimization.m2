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
    {Name => "Fatemeh Tarashi Kashani",
    Email => "tarashikashanifatemeh@gmail.com",
    HomePage => "https://www.linkedin.com/in/fatemehtarashi/"},
    {Name => "Benjamin Hollering",
    Email => "bkholler@ncsu.edu",
    HomePage => "https://benhollering.wordpress.ncsu.edu/"}
  },
  Headline => "A package for algebraic optimization",
  DebuggingMode => true,
  PackageImports => {"Elimination","NumericalAlgebraicGeometry","Bertini","PrimaryDecomposition", "ToricInvariants"}
)

--------------------
--Exports
--------------------

export {
  -- Methods
  "projectiveDual",
  "conormalRing",
  "conormalIdeal",
  "probabilisticEDDegree",
  "symbolicEDDegree",
  "checkGeneralCoordinates",
  "projectionEDDegree",
  "sectionEDDegree",
  "symbolicMultidegreeEDDegree",
  "probabilisticMultidegreeEDDegree",
  "probabilisticFritzJohnEDDegree",
  "MLequationsIdeal",
  "MLequationsDegree",
  "parametricMLIdeal",
  "parametricMLDegree",
  "probabilisticLagrangeMultiplierEDDegree",
  "toricMLIdeal",
  "toricMLDegree",
  "probabilisticConormalVarietyOptimizationDegree",
  -- Options
  "DualVariable", "CoeffRing",
  --Types and keys
  "ConormalRing","PrimalRing","DualRing","PrimalCoordinates","DualCoordinates",
  --More Types
  "LagrangeVarietyWitness","LagrangeIdeal",
  --"IsolatedCriticalPointSet",
  --Methods
  --"isolatedRegularCriticalPointSet","criticalIdeal","lagrangeIdeal",
  --"gradient",
  "probabilisticLagrangeMultiplierOptimizationDegree",
  --More Keys
  "LagrangeVariable","PrimalIdeal","JacobianConstraint","AmbientRing","LagrangeCoordinates","WitnessPrimalIdeal",
  "Data",
  --"Gradient",
  --"WitnessSuperSet", "SaveFileDirectory",
  -- Tolerances
  --"MultiplicityTolerance","EvaluationTolerance", "ConditionNumberTolerance",
  --"updateMultiplicityTolerance","updateEvaluationTolerance","updateConditionNumberTolerance",
  "Coordinates", "Factors",
  --"Numerators","Denominators",
  -- Strategies
  "Probabilistic", "Symbolic"
}



--------------------
--ConormalRing
--------------------

ConormalRing = new Type of MutableHashTable;
--a ConormalRing always has the following keys:
-- AmbientRing, Factors, Coordinates
conormalRing = method(Options => {DualVariable => null});
-- Creates a ConormalRing from a primal ring R
conormalRing Ring := ConormalRing => opts -> R -> (
  --if not degreeLength R == 1 then error "expected degree length 1";
  u := if opts.DualVariable === null then symbol u else opts.DualVariable;
  dualR := (coefficientRing R)[u_0..u_(#gens R - 1)];
  new ConormalRing from {
    AmbientRing => R ** dualR,
    Factors => {R, dualR},
    Coordinates => {gens R, gens dualR}
  }
)
conormalRing Ideal := ConormalRing => opts -> I -> conormalRing(ring I, opts)


conormalIdeal = method(Options => options conormalRing);
-- Computes the conormal variety
conormalIdeal (Ideal, ConormalRing) := Ideal => opts -> (I,C) -> (
  if not ring I === C.Factors_0 then error "expected ideal in primal ring";

  c := codim I;
  jacI := sub(diff(matrix{C.Coordinates_0}, transpose gens I), C.AmbientRing);
  jacBar := sub(matrix{C.Coordinates_1}, C.AmbientRing) || jacI;
  J' := sub(I,C.AmbientRing) + minors(c+1, jacBar);
  J := saturate(J', minors(c, jacI));
  J
)
conormalIdeal Ideal := Ideal => opts -> I -> conormalIdeal(I, conormalRing(I), opts)
TEST ///

///

--------------------
--projectiveDual
--------------------

projectiveDual = method(Options => options conormalRing);
-- (Alg. 5.1 in SIAM book)
-- Takes homogeneous ideal as input, returns ideal of dual of the projective variety
projectiveDual (Ideal, ConormalRing) := Ideal => opts -> (I,S) -> (
  if not isHomogeneous I then error("Ideal has to be homogeneous");
  R := ring I;

  primalCoordinates := S.Coordinates_0 / (i->sub(i,S.AmbientRing));
  dualCoordinates := S.Coordinates_1 / (i->sub(i,S.AmbientRing));

  J := conormalIdeal(I, S);

  sub(eliminate(primalCoordinates, J), S.Factors_1)
)
projectiveDual Ideal := Ideal => opts -> I -> projectiveDual(I, conormalRing(I, opts))

TEST ///
S = QQ[x_0..x_2]
I = ideal(x_2^2-x_0^2+x_1^2)
dualI = projectiveDual(I)
S = ring dualI
assert( dualI == ideal(S_0^2 - S_1^2 - S_2^2))
///


--------------------
--probabilisticEDDegree
--------------------
probabilisticEDDegree = method(Options => {Projective => null, Data => null});

probabilisticEDDegree Ideal := ZZ => opts -> I -> (
  R := ring I;
  jacI := transpose jacobian I;
  c := codim I;
  Ising := I + minors(c, jacI);
  u := if opts.Data === null then (gens R / (i -> random(coefficientRing R))) else opts.Data;
  proj := if opts.Projective === null then (if isHomogeneous I then true else false) else opts.Projective;
  local Ibar;
  J := if not proj then (
    Ibar = I + minors(c+1, matrix{u} - vars R || jacI);
    saturate(Ibar, Ising)
  ) else (
    Ibar = I + minors(c+2, matrix{u} || vars R || jacI);
    Q := gens R / (i -> i^2) // sum // ideal;
    saturate(Ibar, Ising * Q)
  );
  degree J
)
TEST ///
R = QQ[x,y]
I = ideal"x2 + y2 - 1"
assert(probabilisticEDDegree(I, Data => {1/3, 2/5}) == 2)
J = ideal((x^2+y^2+x)^2 - x^2 - y^2)
assert(probabilisticEDDegree(J, Data => {1,2}) == 3)
R = QQ[x,y,z]
I = ideal"x2 - y2 - z2"
assert(probabilisticEDDegree(I, Data => {2/4,1/2,-1/2}, Projective => true) == 2)
assert(probabilisticEDDegree(I, Data => {2/4,1/2,-1/2}, Projective => false) == 2)
///


---------------------------
-- probabilisticFritzJohnEDdegree ------
---------------------------
probabilisticFritzJohnEDDegree = method(Options => {Projective => false, Data => null})
probabilisticFritzJohnEDDegree (Ideal, Ideal) := ZZ => opts -> (WI, I) -> (
  R := ring I;
  l := symbol l;
  S := (coefficientRing(R))[l_1..l_(#WI_*)];
  RS := R ** S;
  J := ideal (sub(vars S, RS) * sub(transpose jacobian WI, RS));
  randomAffine := sub(random(1,S) - 1, RS);
  WIsing := J + sub(I,RS) + randomAffine; -- witness of the singular locus of I
  RWIsing := sub(eliminate(gens S / (i -> sub(i,RS)), WIsing) , R);
  u := if opts.Data === null then (gens R / (i -> random(coefficientRing R))) else opts.Data;
  uMatrix := matrix{u};
  m := symbol m;
  Ibar := if not opts.Projective
    then
      (vars R - uMatrix) || transpose jacobian WI
    else
      vars R || uMatrix || transpose jacobian WI;
  T := (coefficientRing(R))[m_1..m_(numRows Ibar)];
  RT := R**T;
  WIbar := ideal(sub(vars T, RT)*sub(Ibar, RT)) + sub(I,RT) + sub(random(1,T) - 1, RT);  -- witness of Ibar
  RWIbar := sub(eliminate(gens T / (i -> sub(i,RT)), WIbar), R);
  critIdeal := if not opts.Projective
    then
      saturate(RWIbar, RWIsing)
    else (
      Q := gens R / (i -> i^2) // sum // ideal;
      saturate(RWIbar, RWIsing * Q)
  );
  degree critIdeal
)
probabilisticFritzJohnEDDegree (Ideal) := ZZ => opts -> (I) -> (
  c := codim I;
  if codim I == numgens I then probabilisticFritzJohnEDDegree(I,I,opts)
  else (
    R := ring I;
    -- use a random linear combination of generators as witness
    witness := gens I * random(R^(numgens I), R^c);
    probabilisticFritzJohnEDDegree(ideal witness, I, opts)
  )
)
TEST ///
R = QQ[x,y]
I = ideal"x2 + y2 - 1"
assert(probabilisticFritzJohnEDDegree(I, Data => {1/3, 2/5}) == 2)
J = ideal((x^2+y^2+x)^2 - x^2 - y^2)
assert(probabilisticFritzJohnEDDegree(J, Data => {1,2}) == 3)
R = QQ[x,y,z]
I = ideal"x2 - y2 - z2"
assert(probabilisticFritzJohnEDDegree(I, Data => {2/4,1/2,-1/2}, Projective => true) == 2)
assert(probabilisticFritzJohnEDDegree(I, Data => {2/4,1/2,-1/2}, Projective => false) == 2)
R = QQ[x,y,z,w]
I = ideal"xz-y2,yw-z2,xw-yz"
assert(probabilisticFritzJohnEDDegree(ideal(I_0,I_1),I, Projective => true) == 7)
assert(probabilisticFritzJohnEDDegree(ideal(I_0,I_1),I, Projective => false) == 7)
assert(probabilisticFritzJohnEDDegree(I) == 7)
///





--------------------
--symbolicEDDegree
--------------------
symbolicEDDegree = method(Options => {Projective => null});

symbolicEDDegree Ideal := ZZ => opts -> I -> (
  R := ring I;
  u := symbol u;
  paramRing := ((coefficientRing R)[u_0..u_(numgens R - 1)]);
  S :=  (frac paramRing) monoid R;
  IS := sub(I,S);
  jacIS := transpose jacobian IS;
  c := codim I;
  ISsing := IS + minors(c, jacIS);
  proj := if opts.Projective === null then (if isHomogeneous I then true else false) else opts.Projective;
  uMatrix := matrix {gens paramRing / (i->sub(i,S))};
  local ISbar;
  J := if not proj then (
    ISbar = IS + minors(c+1, uMatrix - vars S || jacIS);
    saturate(ISbar, ISsing)
  ) else (
    ISbar = IS + minors(c+2, uMatrix || vars S || jacIS);
    Q := gens S / (i -> i^2) // sum // ideal;
    saturate(ISbar, ISsing * Q)
  );
  degree J
)
TEST ///
R = QQ[x,y]
I = ideal"x2 + y2 - 1"
assert(symbolicEDDegree(I) == 2)
-- this test is slow, maybe should be removed
J = ideal((x^2+y^2+x)^2 - x^2 - y^2)
assert(symbolicEDDegree(J) == 3)
---------------------------------------------
R = QQ[x,y,z]
I = ideal"x2 - y2 - z2"
assert(symbolicEDDegree(I, Projective => true) == 2)
assert(symbolicEDDegree(I, Projective => false) == 2)
///


------------------------
-- edDegreeStrategies --
------------------------
-- Takes a symbol and an ideal,
-- outputs ED-degree computed using
-- the corresponding strategy
edDegreeStrategies = (I,strat) -> (
  if strat == Probabilistic then probabilisticEDDegree I
  else if strat == Symbolic then symbolicEDDegree I
  else error "invalid Strategy"
)


--------------------
-- checkGeneralCoordinates -
--------------------
-- Checks if the conormal variety intersects the diagonal
-- This checks a sufficient condition
-- Needs more testing
checkGeneralCoordinates = method();
checkGeneralCoordinates Ideal := Boolean => I -> (
  R := ring I;
  Q := gens R / (i -> i^2) // sum // ideal;
  InQ := I + Q;
  c := codim I;
  cc := codim InQ;
  Ising := minors(c, jacobian I);
  InQsing := minors(cc, jacobian InQ) + InQ;
  if saturate(InQsing, ideal gens R) == R and saturate(InQ + Ising, ideal gens R) == R then true else false
)

--------------------
-- randomProjection-
--------------------
randomProjection = method();
randomProjection Ideal := Ideal => I -> (
  c := codim I;
  if c <= 1 then error "expected codimension >= 1";
  R := ring I;
  n := numgens R;
  L := symbol L;
  S := coefficientRing R[L_0..L_(n-c)];
  M := random(R^n, R^(n-(c-1)));
  f := map(R,S, vars R * M);
  preimage(f,I)
)


-------------------
-- projectionEDDegree-
-------------------
projectionEDDegree = method(Options => {Strategy => Probabilistic});
projectionEDDegree Ideal := ZZ => opts -> I -> (
  c := codim I;
  J := randomProjection I;
  edDegreeStrategies(J,opts.Strategy)
)
TEST ///
R = QQ[x_0..x_6]
I = ideal(apply(2, i-> random(1,R)))
assert(projectionEDDegree I == 1)
-- TODO this test may be too slow --
S = QQ[y_0..y_3,z]
J = ideal det(matrix{{y_0, y_1, y_2}, {y_1, y_0, y_3}, {y_2, y_3, y_0}})
assert(probabilisticEDDegree (J+z) == 13)
-------------------------------------
///


-------------------
-- randomSection --
-------------------
randomSection = method();
randomSection Ideal := Ideal => I -> (
  R := ring I;
  I + ideal random(1,R)
)

---------------------
-- sectionEDDegree --
---------------------
sectionEDDegree = method(Options => {Strategy => Probabilistic});
sectionEDDegree Ideal := ZZ => opts -> I -> (
  Idual := projectiveDual I;
  sections := {I} | accumulate((J, j) -> randomSection J, I, toList(1..(dim I - 1)));
  intermediateSections := drop(sections, -1);
  degs := intermediateSections / (I -> (Istar := projectiveDual(I); if codim Istar == 1 then degree Istar else 0));
  edDegreeStrategies(last sections, opts.Strategy) + sum degs
)
TEST ///
R = QQ[x_0..x_6]
I = ideal(apply(2, i-> random(1,R)))
assert(sectionEDDegree I == 1)
-- TODO this test may be too slow
R = QQ[x_0,x_1,x_2,x_3]
M = matrix{{x_0,x_1,x_2},{x_1,x_0,x_3},{x_2,x_3,x_0}}
I = ideal det M
assert(sectionEDDegree I == 13)
--
///



--------------------
--multidegreeEDDegree
--------------------


symbolicMultidegreeEDDegree = method();
symbolicMultidegreeEDDegree Ideal := ZZ => I -> (
  S := conormalRing ring I;
  N := conormalIdeal(I,S);
  (mon,coef) := coefficients multidegree N;
  sub(sum flatten entries coef, ZZ)
)

TEST ///
R = QQ[x_0..x_3]
J = ideal det(matrix{{x_0, x_1, x_2}, {x_1, x_0, x_3}, {x_2, x_3, x_0}})
assert(symbolicMultidegreeEDDegree(J) == 13)
///

probabilisticMultidegreeEDDegree = method();
probabilisticMultidegreeEDDegree Ideal := ZZ => I -> (
  S := conormalRing ring I;
  N := conormalIdeal(I,S);
  d := dim N - 2;
  R := ring N;
  dehomog := ideal(random({1,0}, R) - 1, random({0,1}, R) - 1);
  multideg := for i from 0 to d list (
      slices := apply(i, j->random({1,0}, R)) | apply(d-i, j->random({0,1},R));
      degree(N + ideal(slices) + dehomog)
  );
  sum multideg
)
TEST ///
R = QQ[x_0..x_3]
J = ideal det(matrix{{x_0, x_1, x_2}, {x_1, x_0, x_3}, {x_2, x_3, x_0}})
assert(probabilisticMultidegreeEDDegree(J) == 13)
R = QQ[x,y,z,w]
I = ideal"xz-y2,yw-z2,xw-yz"
assert(probabilisticMultidegreeEDDegree I == 7)
///

--------------------
--MLequationsDegree
--------------------
MLequationsIdeal = method()
MLequationsIdeal (Ideal,List) := (I,u)-> (
    if not (isHomogeneous I) then error("The Ideal isn't Homogeneous");
    if not (isPrime I) then error("The Ideal isn't Prime");
    
    c := codim I;
    jacI := transpose jacobian I;
    Q := minors(c, jacI);
    
    R := ring I;
    numVars := #gens R;
    i1 := for i from 1 to numVars list 1;
    J := matrix {i1} || jacI;
    diagM := diagonalMatrix gens R;
    J' := J * diagM;
    M := ker sub(J', R/I); -- compute kernel of J' over the coordinate ring
    
    g := generators M;
    g' := matrix drop(entries g,-numrows g+#u);
    Iu' := sub(ideal (matrix {u} * g'), R); -- put the ideal Iu' back in the original ring R
    MLIdeal := saturate(saturate(saturate(Iu', Q), sum gens R), product gens R);
    MLIdeal
)

MLequationsDegree = method(Options => {Data => null})
MLequationsDegree (Ideal) := ZZ => opts -> (I) -> (
    R := ring I;
    numVars := #gens R;
    u := if opts.Data ===null then  for i from 0 to numVars-1 list random(1, 10^5) else opts.Data;
    MLIdeal := MLequationsIdeal(I,u);
    MLdegree := degree MLIdeal;
    MLdegree
)

TEST ///
R = QQ[p0, p1, p2, p12]
I = ideal (2*p0*p1*p2 + p1^2*p2 + p1*p2^2 - p0^2*p12 + p1*p2*p12)
u= {4,2, 11, 15}
assert( MLequationsDegree (I) == 3)
assert( MLequationsDegree (I ,  Data => u) == 3)
///

--------------------
--parametricMLDegree
--------------------
parametricMLIdeal = method();
parametricMLIdeal (List,List) := (F,u)-> (
    if not (sum F ==1) then error("The sum of functions is not equal to one.");
    m1 := diagonalMatrix F;
    m2 := for i in F list transpose jacobian ideal(i);
    m2p := fold(m2, (i,j) -> i || j);
    M := m1 | m2p;

    g := generators ker M;
    g' := matrix drop(entries g,-numrows g+#u);
    Ju' := ideal (matrix {u} * g');
    MLIdeal := saturate(Ju');
    MLIdeal
)

parametricMLDegree = method(Options => {Data => null});
parametricMLDegree (List) := ZZ => opts -> (F)-> (
    u := if opts.Data ===null then  for i from 0 to #F-1 list random(1, 10^5) else opts.Data;
    MLIdeal := parametricMLIdeal(F,u);
    MLdegree := degree MLIdeal;
    MLdegree
)

TEST ///
R = QQ[t]
s=1
u = {2,3,5,7}
F = {s^3*(-t^3-t^2-t+1),s^2*t,s*t^2,t^3}
assert( parametricMLDegree (F) == 3)
assert( parametricMLDegree (F ,  Data => u) == 3)
///

--------------------
--LagrangeMultiplierEDDegree
--------------------

probabilisticLagrangeMultiplierEDDegree = method(Options => {Data => null});
probabilisticLagrangeMultiplierEDDegree (Ideal,Ideal) := ZZ => opts -> (WI,I) -> (
    aLI := lagrangeIdeal(WI,I);
    X := gens ring I;
    g := if opts.Data===null then apply(X,i->random(1,1000) ) else opts.Data;
    degree criticalIdeal(gradient(X-g),aLI)
    )
--probabilisticLagrangeMultiplierEDDegree Ideal := ZZ => opts -> I ->probabilisticLagrangeMultiplierEDDegree(I,I)


TEST///
R=QQ[x,y]
I =WI =ideal(x^2+y^2-1)
assert(2==probabilisticLagrangeMultiplierEDDegree(WI,I))
I = WI = ideal ((x^2+y^2+x)^2-x^2-y^2)
assert(3==probabilisticLagrangeMultiplierEDDegree(WI,I))
///

------------------------------
--Lagrange multipliers code
------------------------------

LagrangeIdeal = new Type of MutableHashTable;
--LagrangeIdeal always have these keys (Is for the parametric version)
--  JacobianConstraint
--  Ideal
--  CornomalRing
--  WitnessPrimalIdeal  (Ideal so that the parameterization is generically finite to one and we have a sqare system.)
--Optional keys
--  PrimalIdeal   (Parameterization)

--------------------
--LagrangeIdeal code
--------------------

lagrangeIdeal = method(Options => {DualVariable => null,LagrangeVariable => null});
-- Creates a LagrangeRing from a primal ring R
lagrangeIdeal Ideal := LagrangeIdeal => opts -> WI -> (
    CR := conormalRing ring WI;--Pass options?
    lambda := if opts.LagrangeVariable === null then symbol lambda else opts.LagrangeVariable;
    c := numgens WI;
    lagrangeR := newRingFromSymbol(c,lambda, (coefficientRing ring WI));
    CR.AmbientRing = CR.AmbientRing**lagrangeR;
    CR.Coordinates = CR.Coordinates|{gens lagrangeR};
    CR.Factors = CR.Factors|{lagrangeR};
    jacWI := transpose jacobian WI;
    y:=CR.Coordinates#1;--dual coordinates
    jacBar := sub( matrix { y } , CR.AmbientRing) || sub(jacWI,CR.AmbientRing);
    Lam :=CR.Coordinates#2;
    J2 := ideal (sub(matrix{{1}|Lam},CR.AmbientRing)*jacBar);
    aLI := new LagrangeIdeal from {};
    aLI.Ideal =    (J2+sub(WI,CR.AmbientRing));
    aLI.ConormalRing =CR;
    aLI.WitnessPrimalIdeal = WI;
    aLI.JacobianConstraint = J2;
    aLI)

lagrangeIdeal (Ideal,Ideal) := LagrangeIdeal => opts -> (WI,I) -> (
    aLI := lagrangeIdeal(WI);
    aLI.PrimalIdeal = I;
    aLI
    )

-* Depracated test because lagrangeIdeal is no longer exported
TEST ///
   R=QQ[x]; WI=ideal(x)
   lagrangeIdeal(WI)
   peek oo

   R=QQ[x]; WI=ideal(x);I=ideal (x,x)
   aLI = lagrangeIdeal(WI,I)
   peek oo

R=QQ[x,y]
I=ideal(x^2+y^2-1)
aLI = lagrangeIdeal(I)
assert(4==degree aLI.Ideal)
///
*-

--------------------
--methods LagrangeIdeal code
--------------------

coefficientRing(ConormalRing) := CR ->coefficientRing CR.AmbientRing
ring (LagrangeIdeal) := aLI -> ring aLI#JacobianConstraint

-* Depracated because LagrangeIdeal is not exported
degree (List,LagrangeIdeal) := (v,aLI) -> (
--TODO: How to document this?
    if degreeLength  ring aLI == 4 then(
	u := gens coefficientRing ring aLI;
	if #v=!=#u then error "data does not agree with number of parameters. ";
    	subData :=apply(u,v,(i,j)->i=>j);
	return degree sub(sub(aLI.PrimalIdeal,aLI) + aLI.JacobianConstraint,subData)
	)
    else error"degreeLength is not 4."--TODO: should be able to handle any degree length.
    )
degree (Nothing,LagrangeIdeal) := (a,LVW) -> (
	u := gens coefficientRing ring LVW;
	kk := ultimate(coefficientRing,ring LVW);
    	v := apply(u,i->random kk);
	degree(v,LVW)
	)
--Degree with parameters as indeterminants
degree (LagrangeIdeal) := LVW -> (if LVW#?PrimalIdeal then  degree(LVW.Ideal) else error" PrimalIdeal key is missing. ")
*-

sub(RingElement, LagrangeIdeal) := (f,aLI) -> sub(f,ring aLI)
sub(List, LagrangeIdeal) := (L,aLI) -> L/(f -> sub(f,ring aLI))
sub(Ideal, LagrangeIdeal) := (I,aLI) -> sub(I,ring aLI)

-*
--lagrangeIdeal no longer expoerted
TEST///
    R = QQ[u][x,y,z,w]
    I=minors(2,matrix{{x,y,z},{y,z,w}})
    WI=WI1 = ideal(I_0,I_1)
    WI2 = ideal(I_0,I_2)
    codim I
    LVW=LVW1 = lagrangeIdeal(WI1,I)
    LVW2 = lagrangeIdeal(WI2,I)
    peek oo
    assert(6 == numgens LVW1.Ideal)
    assert(6 == numgens LVW2.Ideal)

    assert(LVW1#WitnessPrimalIdeal =!=    LVW2#WitnessPrimalIdeal )

    LVW2.PrimalIdeal=I
    assert(20 == degree LVW2)
    assert(20 == degree LVW1)
    assert(16 == degree({482}, LVW1))
    assert(16 == degree(, LVW1))

    LVW3 = lagrangeIdeal(WI2)
    assert(not  LVW3#?PrimalIdeal)
    LVW3.PrimalIdeal = I
    assert(20 == degree LVW3)

    R=QQ[u][x,y,z,w]

    WI = ideal(u*x*z-y^2,y*w-z^2)
    I = ideal(u*x*w-z*y)+WI
    LVW1 = lagrangeIdeal(WI,I)
    assert(16 == degree({1},LVW1)	)
    assert(16 == degree(,LVW1)	)
    assert(6 == degree({0},LVW1)	)
    assert(39==degree LVW1)

///
*-


--------------------
--Gradient code
--------------------

Gradient = new Type of MutableHashTable
--We need this because frac CC[x]**CC[y] does not work.
gradient = method(Options => {});
gradient (List,List) := Gradient => opts  -> (n,d) ->(
    new Gradient from {
	"Numerators" => n,
	"Denominators" => d
	})
gradient (List) := Gradient => opts  -> (g) ->(
    n := apply(g,i-> if instance(ring i,FractionField) then numerator i else i);
    d := apply(g,i-> if instance(ring i,FractionField) then denominator i else 1_(ring(i)));
    gradient(n,d))

sub(Gradient,LagrangeIdeal) :=  (g,aLI) -> (
    n := apply(g#"Numerators",i->sub(i,aLI));
    d := apply(g#"Denominators",i->sub(i,aLI));
    gradient(n,d)
    )


--gradient no longer exported
-*
TEST///
R=QQ[x,y]
assert(2==#keys gradient({x}))
assert(2 == # keys gradient({x},{y}))
///
*-

--------------------
--CriticalIdeal code
--------------------

--witnessCriticalVariety and Optimization degree
CriticalIdeal = new Type of MutableHashTable
criticalIdeal = method(Options => {Data=>null});--Evaluate data option.
criticalIdeal (Gradient,LagrangeIdeal) := CriticalIdeal => opts  -> (g,aLI) ->(
	u := gens coefficientRing ring (aLI);
	dataSub := if opts.Data===null then {} else apply(u,opts.Data,(i,j) -> i => j);
    	gCN := sub(g,aLI);
    	newJC := aLI.JacobianConstraint;
    	Lam := sub(aLI.ConormalRing.Factors#2//gens,aLI);
	y:=sub(aLI.ConormalRing.Factors#1//gens,aLI);
    	newJC = ideal apply(#y,
	    i->(
	    	lamSub := Lam/(j->j=>j*gCN#"Denominators"#i);
	    	gCN#"Numerators"#i + sub( newJC_i, lamSub )-y_i
		)
	    );
	CI := new CriticalIdeal from {
	    Data => opts.Data,
	    Gradient => g,
	    LagrangeIdeal => aLI,
	    JacobianConstraint => sub(newJC,dataSub)
	    };
	return CI
    )

--criticalIdeal (List,LagrangeIdeal) := CriticalIdeal => opts  -> (g,aLI) ->criticalIdeal(gradient g,aLI,opts)
criticalIdeal (RingElement,LagrangeIdeal) := CriticalIdeal =>opts -> (psi,aLI) -> (
    g := gradient apply(gens ring psi,x->diff(x,psi));
    criticalIdeal(g,aLI,opts)
    )

criticalIdeal (Gradient,Ideal) := CriticalIdeal =>opts -> (g,WI) -> (
    aLI := lagrangeIdeal WI;
    criticalIdeal(g,aLI,opts)
    )
--criticalIdeal (List,Ideal) := CriticalIdeal =>opts -> (g,WI) ->criticalIdeal(gradient g,WI,opts)
criticalIdeal (RingElement,Ideal) := CriticalIdeal =>opts -> (psi,WI) -> (
    g := gradient apply(gens ring psi,x->diff(x,psi));
    criticalIdeal(g,WI,opts)
    )

criticalIdeal (Gradient,Ideal,Ideal) := CriticalIdeal =>opts -> (g,WI,I) -> (
    aLI := lagrangeIdeal(WI,I);
    criticalIdeal(g,aLI,opts)
    )
--criticalIdeal (List,Ideal,Ideal) := CriticalIdeal =>opts -> (g,WI,I) ->criticalIdeal(gradient g,WI,I,opts)
criticalIdeal (RingElement,Ideal,Ideal) := CriticalIdeal =>opts -> (psi,WI,I) -> (
    g := gradient apply(gens ring psi,x->diff(x,psi));
    criticalIdeal(g,WI,I,opts)
    )

degree (CriticalIdeal) :=  CI -> (
    if not(CI#LagrangeIdeal#?PrimalIdeal) then error"CriticalIdeal#LagrangeIdeal#?PrimalIdeal is false. ";
    w := CI#JacobianConstraint;
    w = w+sub(CI#LagrangeIdeal#PrimalIdeal,CI#LagrangeIdeal);
    u := gens coefficientRing ring (CI#LagrangeIdeal);
    dataSub := if CI.Data===null then {} else apply(u,CI.Data,(i,j)->i=>j);
    sCI := sub(w,dataSub);
    g := sub(CI#Gradient,CI#LagrangeIdeal);
    print (peek g);
    scan( g#"Denominators" , d -> sCI = saturate(sCI, d) );
    print(toString sCI);
    targetCodim := #gens ring(CI#LagrangeIdeal#WitnessPrimalIdeal)+ #gens(CI#LagrangeIdeal.ConormalRing#Factors#2);
    if codim sCI =!= targetCodim
    then sum \\ degree \ select(primaryDecomposition sCI, i-> codim i ==targetCodim)
    else degree sCI
    )


--lagrangeIdeal no longer exported
-*
TEST///
R=QQ[a,b][x,y]
I=ideal(x^2+y^2-1)
WI=I
aLI = lagrangeIdeal(WI,I)
peek criticalIdeal
ring aLI
 WCI = criticalIdeal({x-a,y-b},aLI)
peek WCI
assert(4==degree WCI)

WCI = criticalIdeal({x-a,y-b},aLI,Data=>{2,19})
assert(2==degree WCI)--ED degree of the circle
///
*-


--lagrangeIdeal and criticalIdeal no longer exported
-*
TEST///
R=QQ[x,y]
I=ideal(x^2+y^2-1)
WI=I
aLI = lagrangeIdeal(WI,I)
peek criticalIdeal
ring aLI
 WCI = criticalIdeal({x-2,y-19},aLI)
peek WCI
assert(2==degree WCI)

///
*-

----------------------------------------
-- Toric ML Degree Code
----------------------------------------
toricMLIdeal = method(Options => {CoeffRing => QQ})
toricMLIdeal(Matrix, List, List) := Ideal => opts -> (A, c, u) -> (
    if not (rank A == min(numgens target A, numgens source A)) then error("The matrix is not full rank.");
    t := symbol t;
    n := #c;
    R := (opts.CoeffRing)[t_1..t_(numgens target A)];
    N := sum u;
    toricMapA := transpose matrix {for i from 0 to n-1 list c_i*R_(entries A_i)};
    u = transpose matrix {u};
    A = sub(A,R);
    MLIdeal := saturate(saturate(ideal(A*(N*toricMapA - u)), product gens R), ideal sum entries toricMapA);
    MLIdeal
    )

toricMLDegree = method(Options => {CoeffRing => QQ, Data => null})
toricMLDegree(Matrix, List) := Number => opts -> (A,c) -> (
    if not (rank A == min(numgens target A, numgens source A)) then error("The matrix is not full rank.");
    u := if opts.Data === null then for i from 0 to #c-1 list random(1, 10^5) else opts.Data;
    D := smithNormalForm(A, ChangeMatrix => {false, false}, KeepZeroes => false);
    MLIdeal := toricMLIdeal(A, c, u, CoeffRing => opts.CoeffRing);
    MLdegree := (degree MLIdeal) / (det D);
    MLdegree
    )



TEST ///
A = matrix {{1,1,1,0,0,0,0,0,0}, {0,0,0,1,1,1,0,0,0},{0,0,0,0,0,0,1,1,1},
    {1,0,0,1,0,0,1,0,0},{0,1,0,0,1,0,0,1,0}};
c = {1, 1, 1, 1, 1, 1, 1, 1, 1};
assert(1 == toricMLDegree(A, c));
c = {1,2,3,1,1,1,1,1,1};
assert(3 == toricMLDegree(A,c));
///

--Used to find WI symbollically without using randomization.
--Instead: We could also take a random linear combination.
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

newRingFromSymbol = (n,s,kk)->(
    kk[s_0..s_(n - 1)]
    )


probabilisticLagrangeMultiplierOptimizationDegree = method(Options => {Data => null});
probabilisticLagrangeMultiplierOptimizationDegree (List,Ideal,Ideal) := ZZ => opts -> (g,WI,I) -> (
    aLI := lagrangeIdeal(WI,I);
    CI := criticalIdeal(gradient g,aLI,opts);
    degree CI
    )
probabilisticLagrangeMultiplierOptimizationDegree (RingElement,Ideal,Ideal) := ZZ => opts -> (psi,WI,I) -> (
    aLI := lagrangeIdeal(WI,I);
    CI := criticalIdeal(psi,aLI,opts);
    degree CI
    )


TEST///

R=QQ[x,y]
WI = I = ideal((x^2+y^2+x)^2-x^2-y^2)
psi =(x-3)^2+(y-2)^2
probabilisticLagrangeMultiplierOptimizationDegree(psi,WI,I)
assert(3==probabilisticLagrangeMultiplierOptimizationDegree(psi,WI,I))

R=QQ[u,v][x,y]
WI = I = ideal((x^2+y^2+x)^2-x^2-y^2)
psi =(x-u)^2+(y-v)^2
assert(10==probabilisticLagrangeMultiplierOptimizationDegree(psi,WI,I))
assert(3==probabilisticLagrangeMultiplierOptimizationDegree(psi,WI,I,Data=>{2,3}))

///



probabilisticConormalVarietyOptimizationDegree = method(Options => {Data => null});
probabilisticConormalVarietyOptimizationDegree (List,Ideal) := ZZ => opts -> (g,I) -> (
  --n are numerators; d are denominators
  (n,d) := toSequence transpose apply(g,i-> if instance(ring i,FractionField) then {numerator i, denominator i} else {i,1});
  R := ring I;
  kk := ultimate(coefficientRing,R);
  --v := if opts.Data ===null then apply(gens coefficientRing R,i->random kk ) else opts.Data;
  v := if opts.Data ===null then gens coefficientRing R else opts.Data;
  c := codim I;
  jacI := diff(matrix{gens ring I}, transpose gens I);
  jacBar := matrix{n} || (jacI*diagonalMatrix (d));
  jacBar = sub(jacBar,apply(gens coefficientRing R,v,(i,j)-> i=>j));
  J' := I + minors(c+1, jacBar);
  J := saturate(J', minors(c, jacI));
  scan(d, h -> J = saturate(J,sub(h,R)));
  targetCodim := #gens R;
  if codim J =!= targetCodim
  then sum \\ degree \ select(primaryDecomposition J, i-> codim i ==targetCodim)
  else degree J
  )
probabilisticConormalVarietyOptimizationDegree (RingElement,Ideal) := ZZ => opts -> (psi,I) -> (
    g := apply(gens ring I,i->diff(i,psi));
    probabilisticConormalVarietyOptimizationDegree(g,I,opts)--Don't forget to pass along the opts
    )

TEST///

R=QQ[x,y]
I = ideal((x^2+y^2+x)^2-x^2-y^2)
psi =(x-3)^2+(y-2)^2
probabilisticConormalVarietyOptimizationDegree(psi,I)
assert(3==probabilisticConormalVarietyOptimizationDegree(psi,I))

R=QQ[u,v][x,y]
I = ideal((x^2+y^2+x)^2-x^2-y^2)
psi =(x-u)^2+(y-v)^2--TODO make a consistent choice for what to do when Data=>null.
assert(7==probabilisticConormalVarietyOptimizationDegree(psi,I))
assert(3==probabilisticConormalVarietyOptimizationDegree(psi,I,Data=>{2,3}))
assert(1==probabilisticConormalVarietyOptimizationDegree(psi,I,Data=>{0,0}))

///




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
    References: \break
    [1] Seth Sullivant,
    Algebraic Statistics, American Mathematical Soc. \break
    [2]  Jan Draisma, Emil Horobeţ, Giorgio Ottaviani, Bernd Sturmfels, and Rekha R. Thomas,
    The Euclidean distance degree of an algebraic variety, Found. Comput. Math. 16 (2016), no. 1, 99–149. MR 3451425. \break
    [3] Serkan Hoşten, Amit Khetan,and Bernd Sturmfels,
    Solving the likelihood equations, Found. Comput. Math. 5 (2005), no. 4, 389–407. \break
    [4] Carlos  Am ́endola,  Nathan  Bliss,  Isaac  Burke,  Courtney  R.  Gibbons,
    Martin  Helmer,  Serkan  Ho ̧sten,  Evan  D.  Nash,Jose  Israel  Rodriguez,
    and  Daniel  Smolkin.  The  maximum  likelihood  degree  of  toric  varieties.
    Journal  of  SymbolicComputation, 92:222–242, May 2019.
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
--doc ///
--Key
--Headline
--Usage
--Inputs
--Outputs
--Consequences
--  Item
--Description
--  Text
--  Code
--  Pre
--  Example
--  CannedExample
--Subnodes
--Caveat
--SeeAlso
--///

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
  (projectiveDual, Ideal, ConormalRing)
Headline
  Compute projective dual
Usage
  projectiveDual(I, C)
Inputs
  I:
    a homogeneous @TO2{Ideal, "ideal"}@
  C:ConormalRing
Outputs
  :Ideal
    the projective dual of {\tt I} as an ideal of the second factor of the @TO ConormalRing@ $C$.
--Consequences
--  asd
Description
  Text
    Compute the projective dual of a homogeneous ideal in the specified @TO ConormalRing@.

  Example
    S = QQ[x_0..x_2]
    C = conormalRing(S, DualVariable => symbol y)
    I = ideal(x_2^2-x_0^2+x_1^2)
    I' = projectiveDual(I,C)
    ring I' === C.Factors_1
--  Code
--    todo
--  Pre
--    todo
Caveat
  The optional input @TO DualVariable@ is not used.
SeeAlso
  projectiveDual
///


doc ///
Key
  conormalRing
  (conormalRing,Ring)
  (conormalRing,Ideal)
  [conormalRing, DualVariable]
Headline
  Creates a ring with primal and dual variables
Usage
  conormalRing R
  conormalRing I
Inputs
  R:Ring
  I:Ideal
  DualVariable=>
    a user defined @TO2{Symbol, "symbol"}@ used to denote dual variables

Outputs
  :ConormalRing
Description
  Text
    Creates an element of type ConormalRing
  Example
    R = QQ[x_0..x_2]
    conormalRing(R)
    I = ideal(x_0^2)
    conormalRing(I, DualVariable => symbol l)
SeeAlso
  conormalIdeal
///

doc ///
Key
  conormalIdeal
  (conormalIdeal, Ideal, ConormalRing)
  (conormalIdeal, Ideal)
  [conormalIdeal, DualVariable]
--Headline
--  todo
Inputs
  I:
    a homogeneous @TO2{Ideal, "ideal"}@ defined in the primal variables only
  S:ConormalRing
  DualVariable:
    a user defined @TO2{Symbol, "symbol"}@ used to denote dual variables. This option is ignored if a @TO ConormalRing@ is supplied.
Usage
  conormalIdeal(I,S)
  conormalIdeal I
Description
  Text
    For a projective variety $X = \mathbb V(I) \subseteq \mathbb P^n$, the conormal variety is the closure of the set of points
    $(x,u) \in \mathbb P^n \times \mathbb P^n$ such that $x$ is a regular point on $X$ and $u$ is tangent to $X$ at $x$.

    If an instance $S$ of @TO ConormalRing@ is supplied, the resulting ideal will reside in {\tt S.AmbientRing}.
  Example
    R = QQ[x,y,z]
    I = ideal(x^2 + y^2 - z^2)
    S = conormalRing R
    conormalIdeal(I,S)
///

doc ///
Key
  probabilisticEDDegree
  (probabilisticEDDegree, Ideal)
  [probabilisticEDDegree, Projective]
  [probabilisticEDDegree, Data]
Headline
  compute ED-degree for a random point
Usage
  probabilisticEDDegree I
  probabilisticEDDegree(I, Projective => true)
  probabilisticEDDegree(I, Projective => false)
  probabilisticEDDegree(I, Data => L)
Inputs
  I:
    a prime @TO2{Ideal, "ideal"}@ corresponding to an irreductible variety.
  Projective =>
    specifies if the ideal is homogeneous or not. The default value @TO null@ chooses automatically.
    The automatic choice can be overriden by specifying a @TO Boolean@ value.
  Data => List
    specifies coordinates of the point from which the ED degree is computed.
    By default, this point is chosen at random from the coefficient ring using @TO (random,Type)@.
Outputs
  :ZZ
    the ED-degree of $I$.
--Consequences
--  Item
Description
  Text
    The function computes the Euclidean distance degree of an irreducible variety corresponding to
    the prime ideal $I$. In other words, we choose a random point $u$ and output the number of critical
    points of the distance function from the variety to $u$. A random point will give the correct ED degree
    with probability 1.

    In the example below, we see that the ED degree of a circle is 2, and the ED degree of a cardioid is 3
  Example
    R = QQ[x,y]
    I = ideal(x^2 + y^2 - 1)
    probabilisticEDDegree I--2
    J = ideal((x^2+y^2+x)^2 - x^2 - y^2)
    probabilisticEDDegree J--3

  Text
    Instead of a random point, the user can specify their own point
  Example
    probabilisticEDDegree(I, Data => {2,3})--2

  Text
    If the variety corresponding to $I$ is projective, the projective
    ED degree is defined as the ED degree of the corresponding affine cone. Nonetheless, the algorithm
    for computing the ED degree of a homogeneous ideal is slightly faster than for non-homogeneous ideals.
    By default, the function checks whether or not the ideal is homogeneous
    and chooses an algorithm based on the result. The user can force the choice of algorithm by specifying
    {\tt Projective => true} or {\tt Projective => false}.
  CannedExample
    i1 : R = QQ[x_0..x_3];

    i2 : I = ideal(random(2,R), random(3,R));

    o2 : Ideal of R

    i3 : elapsedTime probabilisticEDDegree(I, Projective => true)
          1.55738 seconds elapsed

    o3 = 24

    i4 : elapsedTime probabilisticEDDegree(I, Projective => false)
          108.958 seconds elapsed

    o4 = 24

--  Code
--  Pre
--  Example
--  CannedExample
--Subnodes
--Caveat
--SeeAlso
///


doc ///
Key
  probabilisticFritzJohnEDDegree
  (probabilisticFritzJohnEDDegree, Ideal, Ideal)
  [probabilisticFritzJohnEDDegree, Data]
  [probabilisticFritzJohnEDDegree, Projective]
Headline
  compute ED-degree for a random point using Fritz John conditions
Usage
  probabilisticFritzJohnEDDegree(WI,I)
  probabilisticFritzJohnEDDegree(WI, I, Projective => true)
  probabilisticFritzJohnEDDegree(WI, I, Projective => false)
  probabilisticFritzJohnEDDegree(WI, I, Data => L)
Inputs
  WI:
    an @TO2{Ideal, "ideal"}@ with ${codim}(I)$ generators such that $\mathbb V(WI)$ contains
    $\mathbb V(I)$ as an irreducible component
  I:
    an @TO2{Ideal, "ideal"}@ corresponding to an irreducible variety.
  Projective => Boolean
    specifies whether or not to use a specialized algorithm for projective varieties.
    Note that if $I$ is homogeneous, both {\tt true} and {\tt false} should return the same answer
  Data => List
    specifies coordinates of the point from which the ED degree is computed.
    By default, this point is chosen at random from the coefficient ring using @TO (random,Type)@.
Outputs
  :ZZ
    the ED-degree of $I$.
--Consequences
--  Item
Description
  Text
    The function computes the Euclidean distance degree of an irreducible variety corresponding to
    the prime ideal $I$ using the Fritz John conditions. In other words, we choose a random point $u$ and output the number of critical
    points of the distance function from the variety to $u$. A random point will give the correct ED degree
    with probability 1.

    In this function, rank conditions on a polymomial matrix $M$ are expressed by adding equations of the form
    $\Lambda M = 0$, where $\Lambda$ is a row vector of new indeterminates $\lambda_i$. If $M$ is of full rank
    (e.g. $M$ is the Jacobian or augmented Jacobian of $WI$), solutions of the system
    $\Lambda M = 0$, $\sum_{i} c_i\lambda_i = 1$ lying on $\mathbb V(I)$ are points where the rank
    of $M$ drops (here the $c_i$ are random constants).

    We can confirm that the EDDegree of the twisted cubic is 7.
  Example
    R = QQ[x,y,z,w]
    I = ideal"xz-y2,yw-z2,xw-yz"
    WI = ideal(I_0, I_1)
    probabilisticFritzJohnEDDegree(WI,I)
  Text
    Instead of a random point, the user can specify their own point
  Example
    probabilisticFritzJohnEDDegree(I, Data => {2,3,4,5})

  Text
    This function tends to perform well compared to e.g. @TO probabilisticEDDegree@ when the number of generators is larger than the codimension.
    In the example below, we have an ideal $I$ of codimension 2 with 7 generators.
    We will use two random linear combinations of the 7 generators as our witness ideal $WI$.
  CannedExample
    i2 : R = QQ[x_0..x_3];

    i3 : f1 = random(2,R);

    i4 : f2 = random(2,R);

    i5 : I = ideal(matrix{{f1,f2}} * random(R^2, R^5) | matrix{{f1,f2}});

    o5 : Ideal of R

    i6 : WI = ideal (gens I * random(R^7,R^2));

    o6 : Ideal of R

    i7 : elapsedTime probabilisticEDDegree I
         2.8346 seconds elapsed

    o7 = 12

    i8 : elapsedTime probabilisticFritzJohnEDDegree (WI,I)
         0.707514 seconds elapsed

    o8 = 12



  Text
    If the variety corresponding to $I$ is projective, the projective
    ED degree is defined as the ED degree of the corresponding affine cone.
    By default, the function uses the non-projective algorithm, as it is requires
    fewer new $\lambda_i$ variables. The user can force the projective algorithm
    by setting {\tt Projective => true}.
  CannedExample
    i5 : R = QQ[x_0..x_3];

    i6 : I = ideal(random(2,R), random(2,R));

    o6 : Ideal of R

    i7 : elapsedTime probabilisticFritzJohnEDDegree(I,I, Projective => false)
         0.812368 seconds elapsed

    o7 = 12

    i8 : elapsedTime probabilisticFritzJohnEDDegree(I,I, Projective => true)
         8.19129 seconds elapsed

    o8 = 12

--Subnodes
--Caveat
SeeAlso
  probabilisticEDDegree
  --symbolicFritzJohnEDDegree
///

doc ///
Key
  (probabilisticFritzJohnEDDegree, Ideal)
Headline
  compute ED-degree for a random point using Fritz John conditions
Usage
  probabilisticFritzJohnEDDegree I
Inputs
  I:
    an @TO2{Ideal, "ideal"}@ corresponding to an irreducible variety.
Outputs
  :ZZ
    the ED-degree of $I$.
--Consequences
--  Item
Description
  Text
    Computes the ED-degree using Frtiz John conditions. See @TO (probabilisticFritzJohnEDDegree, Ideal, Ideal)@ for more detail.

    If the codimension of $I$ is equal to the number of generators, this function calls {\tt probabilisticFritzJohnEDDegree(I,I)}.
    If not, we construct a witness ideal $WI$ by taking $codim(I)$ many random linear combinations
    of generators, and  call {\tt probabilisticFritzJohnEDDegree(WI,I)}.
  Example
    R = QQ[x,y,z,w]
    I = ideal"xz-y2,yw-z2,xw-yz"
    probabilisticFritzJohnEDDegree I
--Subnodes
Caveat
  This function does not check whether or not $\mathbb V(WI)$ cotains $\mathbb V(I)$ as an irreducible component.
SeeAlso
  probabilisticFritzJohnEDDegree
  --symbolicFritzJohnEDDegree
  probabilisticEDDegree
///


doc ///
Key
  symbolicEDDegree
  (symbolicEDDegree, Ideal)
Headline
  Compute EDDegree symbolically
Usage
  symbolicEDDegree I
  symbolicEDDegree(I, Projective => true)
  symbolicEDDegree(I, Projective => false)
Inputs
  I:
    a prime @TO2{Ideal, "ideal"}@ corresponding to an irreductible variety.
  Projective =>
    specifies if the ideal is homogeneous or not. The default value @TO null@ chooses automatically.
    The automatic choice can be overriden by specifying a @TO Boolean@ value.
Outputs
  :ZZ
    the ED-degree of $I$.
Description
  Text
    The function computes the Euclidean distance degree of an irreducible variety corresponding to
    the prime ideal $I$. If $I \subseteq \mathbb{K}[x_1,\dots,x_n]$ is the prime ideal corresponding
    to the variety $X$, the function computes the number of critical points of the distance function from
    $X$ to a generic point $(u_1,\dots,u_n)$. The algorithms used are the same as in @TO probabilisticEDDegree@,
    except that computations are done over the field of fractions of $\mathbb{K}[u_1,\dots,u_n]$.

    We can confirm that the ED-degree of the circle is 2.
  Example
    R = QQ[x,y]
    I = ideal"x2 + y2 - 1"
    symbolicEDDegree I

  Text
    As opposed to @TO probabilisticEDDegree@, this function is deterministic, however
    it is usually much slower.
  CannedExample
    i4 : I = ideal((x^2+y^2+x)^2 - x^2 - y^2)

                4     2 2    4     3       2    2
    o4 = ideal(x  + 2x y  + y  + 2x  + 2x*y  - y )

    o4 : Ideal of R

    i5 : elapsedTime symbolicEDDegree I
          3.24044 seconds elapsed

    o5 = 3

    i6 : elapsedTime probabilisticEDDegree I
          0.0097821 seconds elapsed

    o6 = 3


SeeAlso
  probabilisticEDDegree
  probabilisticFritzJohnEDDegree
///


doc ///
Key
  projectionEDDegree
  (projectionEDDegree, Ideal)
Headline
  ED-degree via random linear projections
Usage
  projectionEDDegree I
Inputs
  I:
    a homogeneous @TO2{Ideal, "ideal"}@
Outputs
  :ZZ
    the projective ED-degree
Description
  Text
    Let $X$ be a projective variety in $\mathbb{P}^n$ of codimension $\geq 2$, and let $\pi : \mathbb P^n \to \mathbb P^{n-1}$
    be a rational map induced by a general linear map $\mathbb C^{n+1} \to \mathbb C^n$.
    Under some regularity assumptions (see Caveat), the ED-degree of $\pi(X)$ is equal to the ED-degree
    of $X$ @TO2{AlgebraicOptimization,"[2, Cor. 6.1.]"}@.

    This function repeatedly applies such a map $\pi$ until the image becomes a hyperlane, and then
    calls @TO probabilisticEDDegree@ or @TO symbolicEDDegree@, depending on the optional argument @TO [projectionEDDegree,Strategy]@.
    This may provide significant computational speedups compared to e.g. @TO probabilisticEDDegree@, @TO symbolicEDDegree@ or @TO symbolicMultidegreeEDDegree@,
    especially the codimension of $X$ is large.
  CannedExample
    i4 : R = QQ[x_0..x_5]

    o4 = R

    o4 : PolynomialRing

    i5 : I = ideal(apply(3, i-> random(1,R)));

    o5 : Ideal of R

    i6 : elapsedTime symbolicEDDegree I
          1.84153 seconds elapsed

    o6 = 1

    i7 : elapsedTime projectionEDDegree I
          0.0341013 seconds elapsed

    o7 = 1

Caveat
  The variety $\mathbb V(I)$ must be in general coordinates, i.e. the conormal variety cannot intersect the diagonal $\Delta(\mathbb{P}^{n-1}) \subset \mathbb{P}^{n-1} \times \mathbb{P}^{n-1}$.
  The function @TO checkGeneralCoordinates@ checks a sufficient condition.
///

doc ///
Key
  sectionEDDegree
  (sectionEDDegree, Ideal)
Headline
  ED-degree via random linear sections
Usage
  sectionEDDegree I
Inputs
  I:
    a projective @TO2{Ideal, "ideal"}@
Outputs
  :ZZ
    the projective ED-degree
Description
  Text
    TODO
    --Let $X$ be a projective variety in $\mathbb{P}^n$ of codimension $\geq 2$, and let $\pi : \mathbb P^n \to \mathbb P^{n-1}$
    --be a rational map induced by a general linear map $\mathbb C^{n+1} \to \mathbb C^n$.
    --Under some regularity assumptions (see Caveat), the ED-degree of $\pi(X)$ is equal to the ED-degree
    --of $X$ [1, Cor. 6.1.].

    --This function repeatedly applies such a map $\pi$ until the image becomes a hyperlane, and then
    --calls @TO probabilisticEDDegree@ or @TO symbolicEDDegree@, depending on the optional argument @TO [projectionEDDegree,Strategy]@.
    --This may provide significant computational speedups compared to @TO probabilisticEDDegree@, @TO symbolicEDDegree@ or @TO symbolicMultidegreeEDDegree@,
    --especially the codimension of $X$ is large.
  Text
    References: [1] Draisma, J., Horobeţ, E., Ottaviani, G., Sturmfels, B., & Thomas, R. R. (2016). The Euclidean distance degree of an algebraic variety. {\em Foundations of computational mathematics}, 16(1), 99-149.
Caveat
  The variety $\mathbb V(I)$ must be in general coordinates, i.e. the conormal variety cannot intersect the diagonal $\Delta(\mathbb{P}^{n-1}) \subset \mathbb{P}^{n-1} \times \mathbb{P}^{n-1}$.
  The function @TO checkGeneralCoordinates@ checks a sufficient condition.
///







doc ///
Key
  symbolicMultidegreeEDDegree
  (symbolicMultidegreeEDDegree, Ideal)
Headline
  compute ED-degree symbolically via multidegrees
Inputs
  I:
    a homogeneous @TO2{Ideal,"ideal"}@ in general coordinates.
Outputs
  :ZZ
    the ED-degree of $I$
Usage
  symbolicMultidegreeEDDegree(I)
Description
  Text
    Computes the ED degree symbolically by taking the sum of multidegrees of the conormal ideal.
    @TO2{AlgebraicOptimization,"[2, Th. 5.4]"}@

    As an example, we see that the ED-degree of Cayley's cubic surface is 13
  Example
    R = QQ[x_0..x_3]
    J = ideal det(matrix{{x_0, x_1, x_2}, {x_1, x_0, x_3}, {x_2, x_3, x_0}})
    symbolicMultidegreeEDDegree(J)

Caveat
  The variety $\mathbb V(I)$ must be in general coordinates, i.e. the conormal variety cannot intersect the diagonal $\Delta(\mathbb{P}^{n-1}) \subset \mathbb{P}^{n-1} \times \mathbb{P}^{n-1}$.
  The function @TO checkGeneralCoordinates@ checks a sufficient condition.
///



doc ///
Key
  probabilisticMultidegreeEDDegree
  (probabilisticMultidegreeEDDegree, Ideal)
Headline
  compute ED-degree probabilistically via multidegrees
Inputs
  I:
    a homogeneous @TO2{Ideal,"ideal"}@ in general coordinates.
Outputs
  :ZZ
    the ED-degree of $I$
Usage
  probabilisticMultidegreeEDDegree(I)
Description
  Text
    Computes the ED degree by taking the sum of multidegrees of the conormal ideal 
    @TO2{AlgebraicOptimization,"[2, Th. 5.4]"}@. The multidegree is computed probabilistically 
    by looking at degrees of complementary dimensional linear slices of the conormal variety in $\mathbb P^n \times P^n$.

  Example
    R = QQ[x_0..x_3]
    J = ideal det(matrix{{x_0, x_1, x_2}, {x_1, x_0, x_3}, {x_2, x_3, x_0}})
    probabilisticMultidegreeEDDegree(J)

Caveat
  The variety $\mathbb V(I)$ must be in general coordinates, i.e. the conormal variety cannot intersect the diagonal $\Delta(\mathbb{P}^{n-1}) \subset \mathbb{P}^{n-1} \times \mathbb{P}^{n-1}$.
  The function @TO checkGeneralCoordinates@ checks a sufficient condition.
///


doc ///
Key
    MLequationsIdeal
   ( MLequationsIdeal,Ideal,List)
Headline
  compute ML-ideal for Homogeneous prime ideal
Usage
  MLequationsIdeal (I,u)
Inputs
  I:
    an @TO2{Ideal, "ideal"}@, Homogeneous prime ideal.
  u:
    a @TO2{List, "list"}@ of natural number as data.
Outputs
  :Ideal
    the likelihoood ideal of $I$
Description
  Text
    Computes the likelihood ideal by taking an Ideal and List of numerical data when the ideal is homogeneous and prime. @TO2{AlgebraicOptimization,"[1, Alg. 7.2.4][3, Alg. 6]"}@
  Example
    R = QQ[p0, p1, p2, p12]
    I = ideal (2*p0*p1*p2 + p1^2*p2 + p1*p2^2 - p0^2*p12 + p1*p2*p12)
    u= {4,2, 11, 15}
    MLequationsIdeal (I,u)
--Caveat
--  todo
SeeAlso
  MLequationsDegree
  parametricMLIdeal
  toricMLIdeal
///

doc ///
Key
    MLequationsDegree
   ( MLequationsDegree, Ideal)
   [ MLequationsDegree, Data]
Headline
  compute ML-degree for Homogeneous prime ideal
Usage
  MLequationsDegree (I)
  MLequationsDegree (I, Data => u)
Inputs
  I:
    an @TO2{Ideal, "ideal"}@, Homogeneous prime ideal.
  Data => List
    By default, this data is chosen at random from natural number.
Outputs
  :Number
    the ML-degree of $I$
Description
  Text
    Computes the maximum likelihood degree of homogeneous prime ideal.
    In other words, we choose a random data u and output is
    the number of complex critical points of the likelihood equations
     for random data u. @TO2{AlgebraicOptimization,"[3, Alg. 6][1]"}@
  Example
    R = QQ[p0, p1, p2, p12]
    I = ideal (2*p0*p1*p2 + p1^2*p2 + p1*p2^2 - p0^2*p12 + p1*p2*p12)
    MLequationsDegree (I)
--Caveat
--  todo
SeeAlso
  MLequationsIdeal
  parametricMLDegree
  toricMLDegree
///

doc ///
Key
   parametricMLIdeal
   (parametricMLIdeal,List,List)
Headline
  compute parametric ML-ideal for List of Polynomials
Usage
  parametricMLMLIdeal (F,u)
Inputs
  F:
    a @TO2{List, "list"}@ of Polynomials, the summation of polynomials is equal to one.
  u:
    a @TO2{List, "list"}@ of natural number as data.
Outputs
  :Ideal
    the parametric ML-ideal of $F$
Description
  Text
    Computes the parametric likelihood ideal by taking List of function and
    List of numerical data when summation F equal to 1. @TO2{AlgebraicOptimization,"[3, Alg. 18]"}@
  Example
    R = QQ[t]
    s=1
    u = {2,3,5,7}
    F = {s^3*(-t^3-t^2-t+1),s^2*t,s*t^2,t^3}
    parametricMLIdeal (F,u)
--Caveat
--  todo
SeeAlso
  parametricMLDegree
  MLequationsIdeal
  toricMLIdeal
///

doc ///
Key
   parametricMLDegree
   (parametricMLDegree,List)
   [parametricMLDegree, Data]
Headline
  compute parametric ML-degree for List of Polynomials
Usage
  parametricMLDegree (F)
Inputs
  F:
    a @TO2{List, "list"}@ of Polynomials, the summation of polynomials is equal to one.
  Data => List
    By default, this data is chosen at random from natural number.
Outputs
  :Number
    the ML-degree of $F$
Description
  Text
    Computes the maximum likelihood degree by taking List of Polynomials
    when summation of polynomials is equal to one. In other words,
    we choose a random data u and output is the number of complex critical points
    of the parametric likelihood equations for random data u. @TO2{AlgebraicOptimization,"[3, Alg. 18]"}@
  Example
    R = QQ[t]
    s=1
    F = {s^3*(-t^3-t^2-t+1),s^2*t,s*t^2,t^3}
    parametricMLDegree (F)
--Caveat
--  todo
SeeAlso
  parametricMLIdeal
  MLequationsDegree
  toricMLDegree
///


doc ///
Key
  checkGeneralCoordinates
  (checkGeneralCoordinates, Ideal)
Headline
  checks if projective variety is in general coordinates
Usage
  checkGeneralCoordinates I
Inputs
  I:
    a projective @TO2(Ideal,"ideal")@
Outputs
  :Boolean
Description
  Text
    Let $X \subseteq \mathbb P^n$ be the variety corresponding to $I$ and let $N \subseteq \mathbb P^n \times \mathbb P^n$.
    We say that $X$ is in general coordinates if $N$ does not intersect the diagonal of $\mathbb P^n \times \mathbb P^n$,
    i.e. there is no point $x \in \mathbb P^n$ such that $x \in X$ and $x \in X^*$, where $X^*$ is the projective dual of $X$.

    Let $Q = \{x = [x_0 : x_1 : \dots : x_n] \in \mathbb P^n : x_0^2 + x_1^2 + \dots + x_n = 0\}$ be the variety corresponding to
    the isotropic quadric. This funciton checks a sufficient condition:
    $X$ is in general coordinates if $X \cap Q$ is smooth and disjoint from the singular locus of $X$.

    The assumption that $X$ is in general coordinates is required for @TO symbolicMultidegreeEDDegree@, @TO probabilisticMultidegreeEDDegree@, @TO sectionEDDegree@ and @TO projectionEDDegree@.
  Example
    R = QQ[x_0..x_3]
    M = matrix{{x_0,x_1,x_2},{x_1,x_0,x_3},{x_2,x_3,x_0}}
    I = ideal det M
    checkGeneralCoordinates I
    symbolicMultidegreeEDDegree I == probabilisticEDDegree I
  Text
    If @TO checkGeneralCoordinates@ returns {\tt false}, the behavior of these functions is undefined.
  Example
    S = QQ[y_0..y_2]
    J = ideal(y_1^2 + y_2^2 - y_0^2)
    checkGeneralCoordinates J
    sectionEDDegree J == probabilisticEDDegree J
///




doc ///
Key
   toricMLIdeal
   (toricMLIdeal,Matrix,List,List)
   [toricMLIdeal, CoeffRing]

Headline
  compute toric ML-ideal
Usage
  toricMLIdeal(A, c, u)
Inputs
  A:
    A full rank @TO2{Matrix, "matrix"}@ of exponents defining the monomial map that parameterizes the toric variety
  c:
    @TO2{List, "list"}@ of numbers used to create the scaled toric variety
  u:
    @TO2{List, "list"}@ of numerical data
  CoeffRing =>
    A the ring of coefficients for the computation to be performed over. By default this ring is QQ.  CoeffRing =>
Outputs
  :Ideal
    the critical ideal of likelihood equations for the corresponding scaled toric variety
    as described in Birch's theorem. @TO2{AlgebraicOptimization,"[1, Cor. 7.2.9]"}@
Description
  Text
    Computes the critical ideal of a scaled toric variety using the equations
    defined in Birch's theorem for given data $u$.
  Example
    A = matrix {{1,1,1,0,0,0,0,0,0}, {0,0,0,1,1,1,0,0,0},{0,0,0,0,0,0,1,1,1},{1,0,0,1,0,0,1,0,0},{0,1,0,0,1,0,0,1,0}}
    c = {1,2,3,1,1,1,1,1,1}
    u = {15556, 84368, 98575, 27994, 61386, 84123, 62510, 37430, 34727};
    toricMLIdeal(A, c, u)
  Text
    References:\break
    [1] Seth Sullivant,
    Algebraic Statistics, American Mathematical Soc.\break
    [2] Carlos  Am ́endola,  Nathan  Bliss,  Isaac  Burke,  Courtney  R.  Gibbons,
    Martin  Helmer,  Serkan  Ho ̧sten,  Evan  D.  Nash,Jose  Israel  Rodriguez,
    and  Daniel  Smolkin.  The  maximum  likelihood  degree  of  toric  varieties.
    Journal  of  SymbolicComputation, 92:222–242, May 2019.
Caveat
    The vector $(1,1,\ldots 1)$ must be in the rowspan of A.
--  todo
SeeAlso
    toricMLDegree
    MLequationsIdeal
    parametricMLIdeal
--
///


doc ///
Key
   toricMLDegree
   (toricMLDegree,Matrix,List)
   [toricMLDegree, Data]
   [toricMLDegree, CoeffRing]
Headline
  compute toric ML-degree
Usage
  toricMLDegree(A, c)
Inputs
  A:
    A full rank @TO2{Matrix, "matrix"}@ of exponents defining the monomial map that parameterizes the toric variety
  c:
    @TO2{Ideal, "ideal"}@ of numbers used to create the scaled toric variety
  Data =>
    A @TO2{Ideal, "ideal"}@ of numerical data. By default, this data is chosen at random from the natural numbers.
  CoeffRing =>
    A the ring of coefficients for the computation to be performed over. By default this ring is QQ.
Outputs
  :Number
    the ML-degree of the corresponding toric variety
Description
  Text
    Computes the maximum likelihood degree of a toric variety using the equations
    defined in Birch's theorem and randomly generated data. The Smith Normal Form is automatically
    used to determine if the parameterization is many-to-one and correct for this. @TO2{AlgebraicOptimization,"[1, Cor. 7.2.9]"}@
  Example
    A = matrix {{1,1,1,0,0,0,0,0,0}, {0,0,0,1,1,1,0,0,0},{0,0,0,0,0,0,1,1,1},{1,0,0,1,0,0,1,0,0},{0,1,0,0,1,0,0,1,0}}
    c = {1,2,3,1,1,1,1,1,1}
    toricMLDegree(A,c)
  Text
    References:\break
    [1] Seth Sullivant,
    Algebraic Statistics, American Mathematical Soc.\break
    [2] Carlos  Am ́endola,  Nathan  Bliss,  Isaac  Burke,  Courtney  R.  Gibbons,
    Martin  Helmer,  Serkan  Ho ̧sten,  Evan  D.  Nash,Jose  Israel  Rodriguez,
    and  Daniel  Smolkin.  The  maximum  likelihood  degree  of  toric  varieties.
    Journal  of  SymbolicComputation, 92:222–242, May 2019.
Caveat
    The vector $(1,1,\ldots 1)$ must be in the rowspan of A.

-- todo
SeeAlso
    toricMLDegree
    MLequationsDegree
    parametricMLIdeal
--
///

doc ///
Key
  probabilisticConormalVarietyOptimizationDegree
  (probabilisticConormalVarietyOptimizationDegree, RingElement, Ideal)
  (probabilisticConormalVarietyOptimizationDegree, List, Ideal)
  [probabilisticConormalVarietyOptimizationDegree, Data]
Headline
  compute ED-degree for a random point
Usage
  probabilisticConormalVarietyOptimizationDegree(psi, I)
  probabilisticConormalVarietyOptimizationDegree(psi, I, Data => L)
  probabilisticConormalVarietyOptimizationDegree(g, I)
  probabilisticConormalVarietyOptimizationDegree(g, I, Data => L)
Inputs
  I:
    an @TO2{Ideal, "ideal"}@ corresponding to an equidimensional variety.
  g:
    a List that gives the gradient of an objective function psi.
  psi:
    an objective function such as squared Euclidean distance.
  Data => List
    specifies parameters.
Outputs
  :ZZ
    the optimization degree of $I$ with respect to an objective function psi with parameters evaluated at Data when specified and gradient g.
Description
  Text
    The function computes the optimization degree of an equidimensional variety corresponding to
    the ideal $I$.

    We can confirm that the optimization-degree for Euclidean distance for the cardioid curve is 3.
  Example
    R=QQ[x,y]
    I = ideal((x^2+y^2+x)^2-x^2-y^2)
    psi =(x-3)^2+(y-2)^2
    probabilisticConormalVarietyOptimizationDegree(psi,I)

  Text
    The function can handle polynomial objective functions psi or objective functions with rational functions as derivatives.

  Example
    R=QQ[x,y]
    I = ideal((x^2+y^2+x)^2-x^2-y^2)
    psi =x^2+2*x*y+3*y
    probabilisticConormalVarietyOptimizationDegree(psi,I)--6
    g ={3*x^2,3/y}--psi = x^3+ + 3*ln y
    probabilisticConormalVarietyOptimizationDegree(g,I)--14

  Text
    The function works with parameters as well when the Data option is specified otherwise the total degree of the critical ideal with parameters as indeterminants is returned.  --TODO: decide what to do here.

  Example
    R=QQ[u,v][x,y]
    I = ideal((x^2+y^2+x)^2-x^2-y^2)
    psi =(x-u)^2+(y-v)^2
    probabilisticConormalVarietyOptimizationDegree(psi,I,Data=>{2,3})--this is three
    probabilisticConormalVarietyOptimizationDegree(psi,I)--TODO: decide what to do here.

SeeAlso
  probabilisticEDDegree
  probabilisticLagrangeMultiplierEDDegree
  probabilisticLagrangeMultiplierOptimizationDegree

///


doc ///
Key
  probabilisticLagrangeMultiplierOptimizationDegree
  (probabilisticLagrangeMultiplierOptimizationDegree, RingElement, Ideal, Ideal)
  (probabilisticLagrangeMultiplierOptimizationDegree, List, Ideal, Ideal)
  [probabilisticLagrangeMultiplierOptimizationDegree, Data]
Headline
  compute ED-degree for a random point
Usage
  probabilisticLagrangeMultiplierOptimizationDegree(psi,WI, I)
  probabilisticLagrangeMultiplierOptimizationDegree(psi,WI,I, Data => L)
  probabilisticLagrangeMultiplierOptimizationDegree(g,WI, I)
  probabilisticLagrangeMultiplierOptimizationDegree(g,WI,I, Data => L)
Inputs
  WI:
    an ideal with codim(I) generators such that V(WI) contains an each irreducible component V(I) as an irreducible component.
  I:
    an @TO2{Ideal, "ideal"}@ corresponding to an equidimensional variety.
  g:
    a List that gives the gradient of an objective function psi.
  psi:
    an objective function such as squared Euclidean distance.
  Data => List
    specifies parameters.
Outputs
  :ZZ
    the optimization degree of $I$ with respect to an objective function psi with parameters evaluated at Data when specified and gradient g.
Description
  Text
    The function computes the optimization degree of an equidimensional variety corresponding to
    the ideal $I$.

    We can confirm that the optimization-degree for Euclidean distance for the cardioid curve is 3.
  Example
    R=QQ[x,y]
    WI = I = ideal((x^2+y^2+x)^2-x^2-y^2)
    psi =(x-3)^2+(y-2)^2
    probabilisticLagrangeMultiplierOptimizationDegree(psi,WI,I)--3

  Text
    The function can handle polynomial objective functions psi or objective functions with rational functions as derivatives.

  Example
    R=QQ[x,y]
    WI = I = ideal((x^2+y^2+x)^2-x^2-y^2)
    psi =x^2+2*x*y+3*y
    probabilisticLagrangeMultiplierOptimizationDegree(psi,WI,I)--6
    g ={3*x^2,3/y}--psi = x^3+ + 3*ln y
    probabilisticLagrangeMultiplierOptimizationDegree(g,WI,I)--14

  Text
    The function works with parameters as well when the Data option is specified otherwise the total degree of the critical ideal with parameters as indeterminants is returned.

  Example
    R=QQ[u,v][x,y]
    WI = I = ideal((x^2+y^2+x)^2-x^2-y^2)
    psi =(x-u)^2+(y-v)^2
    probabilisticLagrangeMultiplierOptimizationDegree(psi,WI,I,Data=>{2,3})--this is three
    probabilisticLagrangeMultiplierOptimizationDegree(psi,WI,I)--this is ten

SeeAlso
  probabilisticEDDegree
  probabilisticLagrangeMultiplierEDDegree

///


doc ///
Key
  probabilisticLagrangeMultiplierEDDegree
  (probabilisticLagrangeMultiplierEDDegree, Ideal,Ideal)
  [probabilisticLagrangeMultiplierEDDegree, Data]
Headline
  Compute EDDegree symbolically using Lagrange multipliers
Usage
  probabilisticLagrangeMultiplierEDDegree (WI,I)
  probabilisticLagrangeMultiplierEDDegree(WI,I, Data => L)
Inputs
  WI:
    an ideal with codim(I) generators such that V(WI) contains an each irreducible component V(I) as an irreducible component.
  I:
    an @TO2{Ideal, "ideal"}@ corresponding to an equidimensional variety.
  Data => List
    specifies coordinates of the point from which the ED degree is computed.
    By default, this point is chosen at random from the coefficient ring using @TO (random,Type)@.
Outputs
  :ZZ
    the ED-degree of $I$.
Description
  Text
    The function computes the Euclidean distance degree of an equidimensional variety corresponding to
    the ideal $I$.

    We can confirm that the ED-degree of the affine cone of the twisted cubic is
  Example
    R = QQ[x0,x1,x2,x3]
    WI = ideal(x0*x2-x1^2 ,x1*x3-x2^2)
    I = WI + ideal(x0*x3-x1*x2)
    probabilisticLagrangeMultiplierEDDegree(WI, I)--7

  Text
    This function is probabilistic.

  Example
    R = QQ[x0,x1,x2,x3]
    WI = ideal(x0*x2-x1^2,x1*x3-x2^2)
    I = WI+ideal(x0*x3-x1*x2)
    probabilisticLagrangeMultiplierEDDegree(WI,I)--7

  Text
    This function is probabilistic and chooses the data at random by default.
    A user may specify the data they want to use.

    In the example below, the ED degree of a cardioid is 3 but the non-generic data choice does not recover this result
  Example
    R = QQ[x,y]
    WI = I = ideal((x^2+y^2+x)^2 - x^2 - y^2)
    probabilisticLagrangeMultiplierEDDegree(WI,I)--3
    probabilisticLagrangeMultiplierEDDegree(WI,I,Data=>{0,0})--3

SeeAlso
  probabilisticLagrangeMultiplierOptimizationDegree
///
-------------------
--Symbols doc
------------------
doc ///
Key
  CoeffRing
Headline
  Incomplete  +
--Usage
--Inputs
--Outputs
--Consequences
--  Item
--Description
--  Text
--  Code
--  Pre
--  Example
--  CannedExample
--Subnodes
--Caveat
--SeeAlso
///

doc ///
Key
  Data
Headline
  Incomplete + 
--Usage
--Inputs
--Outputs
--Consequences
--  Item
Description
  Text
    The option Data is a @TO2{List,"list"}@. 
    This Method is used by the commands @TO2{MLequationsDegree,"MLequationsDegree"}@, 
    @TO2{parametricMLDegree,"parametricMLDegree"}@, 
    @TO2{probabilisticConormalVarietyOptimizationDegree,"probabilisticConormalVarietyOptimizationDegree"}@, 
    @TO2{probabilisticEDDegree,"probabilisticEDDegree"}@, 
    @TO2{probabilisticFritzJohnEDDegree,"probabilisticFritzJohnEDDegree"}@, 
    @TO2{probabilisticLagrangeMultiplierEDDegree,"probabilisticLagrangeMultiplierEDDegree"}@, 
    @TO2{probabilisticLagrangeMultiplierOptimizationDegree,"probabilisticLagrangeMultiplierOptimizationDegree"}@ 
    and @TO2{toricMLDegree,"toricMLDegree"}@.
--  Code
--  Pre
  Example
    R = QQ[p_111,p_112,p_121,p_122,p_211,p_212,p_221,p_222]
    I = ideal (p_111^2*p_222^2+p_121^2*p_212^2+p_122^2*p_211^2+p_112^2*p_221^2-2*p_121*p_122*p_211*p_212-2*p_112*p_122*p_211*p_221-2*p_112*p_121*p_212*p_221-2*p_111*p_122*p_211*p_222-2*p_111*p_121*p_212*p_222-2*p_111*p_112*p_221*p_222+4*p_111*p_122*p_212*p_221+4*p_112*p_121*p_211*p_222)
    u = {2,3,5,7,11,13,17,19}
    MLequationsDegree (I, Data => u)
--  CannedExample
--Subnodes
--Caveat
--SeeAlso
///

doc ///
Key
  DualVariable
Headline
  Incomplete +
--Usage
--Inputs
--Outputs
--Consequences
--  Item
--Description
--  Text
--  Code
--  Pre
--  Example
--  CannedExample
--Subnodes
--Caveat
--SeeAlso
///

--------------------

TEST ///
  -- test code and assertions here
  -- may have as many TEST sections as needed
///

-*
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
*-


end


--Example
restart
path={"/Users/jo/Documents/GoodGit/M2020/Workshop-2020-Cleveland/alg-stat/AlgebraicOptimization"}|path
path={"/home/fatemeh/w/Workshop-2020-Cleveland/alg-stat/AlgebraicOptimization"}|path
loadPackage("AlgebraicOptimization",Reload=>true)
debug AlgebraicOptimization

check"AlgebraicOptimization"
installPackage"AlgebraicOptimization"

M= QQ[x_1..x_2]
I = ideal(4*(x_1^4+x_2^4),4*x_1^3,4*x_2^3)
dualI = projectiveDual(I)
radical I==I
S = ring dualI

-* For parametric ML degree
restart
R=QQ[s,t]
S =QQ[x,y,z,w]
d = {x=>s^3, y=>s^2*t,z=>s*t^2, w=>t^3}
m = map(R,S,d)
kernel m
toString oo

m y
help eliminate
help map
image m


restart--
data ={2,3,5,7}
s=1
R=QQ[t]; --target m
S =QQ[x,y,z,w]--source m
d = {x=>s^3, y=>s^2*t,z=>s*t^2, w=>t^3}
m = map(R,S,d)
affineI = kernel m--this is the twisted cubic's ideal
homogenize(affineI,x)--twisted cubic again.

f= d/last--
sum f ==1--This isn't true, so we replace one of the f's to get this condition to hold.
g = drop(f,1)
f = {1- sum g}|g
sum f ==1 --

m1 = diagonalMatrix f
m2 = transpose matrix{for i in f list jacobian ideal(i)}
M = m1 | m2
gk = generators ker M
gk'=matrix drop(entries gk,-numrows gk+#data)
V = matrix{data}


Ju' =ideal(V*gk'   )
Ju =Ju'
scan(f,i->Ju = saturate(Ju,i))
degree Ju


degree coimage m

degree coimage m

methods class m
*-
