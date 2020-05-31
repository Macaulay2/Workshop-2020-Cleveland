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
    {Name => "Your name here",
    Email => "Your email here",
    HomePage => "Your page here"}
  },
  Headline => "A package for algebraic optimization",
  DebuggingMode => true,
  PackageImports => {"Elimination","NumericalAlgebraicGeometry","Bertini"}
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
  "sectionEDDegree",
  "multiDegreeEDDegree",
  "MLDegree",
  "probabilisticLagrangeMultiplierEDDegree",
  "toricMLIdeal",
  "toricMLDegree",
  -- Options
  "DualVariable", "coeffRing",
  --Types and keys
  "ConormalRing","CNRing","PrimalRing","DualRing","PrimalCoordinates","DualCoordinates",
  --More Types
  "LagrangeVarietyWitness","LagrangeIdeal", "IsolatedCriticalPointSet",
  --Methods
  --"isolatedRegularCriticalPointSet","criticalIdeal","lagrangeIdeal",
  --"gradient",
  "probabilisticLagrangeMultiplierOptimizationDegree",
  --More Keys
  "LagrangeVariable","PrimalIdeal","JacobianConstraint","AmbientRing","LagrangeCoordinates","WitnessPrimalIdeal",
  "Data", "Gradient", "WitnessSuperSet", "SaveFileDirectory",
  -- Tolerances
  "MultiplicityTolerance","EvaluationTolerance", "ConditionNumberTolerance",
  --"updateMultiplicityTolerance","updateEvaluationTolerance","updateConditionNumberTolerance",
  "Coordinates", "Factors",
  "Numerators","Denominators",
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
projectiveDual Ideal := Ideal => opts -> I -> (
  if not isHomogeneous I then error("Ideal has to be homogeneous");
  R := ring I;
  S := conormalRing(R, opts);

  primalCoordinates := S.Coordinates_0 / (i->sub(i,S.AmbientRing));
  dualCoordinates := S.Coordinates_1 / (i->sub(i,S.AmbientRing));

  J := conormalIdeal(I, S);

  sub(eliminate(primalCoordinates, J), S.Factors_1)
)

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



--------------------
-- checkProjective -
--------------------
-- Checks if the conormal variety intersects the diagonal
-- This checks a sufficient condition
-- Needs more testing
checkProjective = method();
checkProjective Ideal := Boolean => I -> (
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
-- sectionEDDegree-
-------------------
sectionEDDegree = method(Options => {Strategy => Probabilistic});
sectionEDDegree Ideal := ZZ => opts -> I -> (
  c := codim I;
  J := randomProjection I;
  if opts.Strategy == Probabilistic then probabilisticEDDegree J
  else if opts.Strategy == Symbolic then symbolicEDDegree J
  else error "invalid Strategy"
)
TEST ///
R = QQ[x_0..x_6]
I = ideal(apply(2, i-> random(1,R)))
assert(sectionEDDegree I == 1)
-- TODO this test may be too slow -- 
S = QQ[y_0..y_3,z]
J = ideal det(matrix{{y_0, y_1, y_2}, {y_1, y_0, y_3}, {y_2, y_3, y_0}})
assert(probabilisticEDDegree (J+z) == 13)
-------------------------------------
///



--------------------
--multiDegreeEDDegree
--------------------


multiDegreeEDDegree = method();
multiDegreeEDDegree Ideal := ZZ => I -> (
  S := conormalRing ring I;
  N := conormalIdeal(I,S);
  (mon,coef) := coefficients multidegree N;
  sub(sum flatten entries coef, ZZ)
)

TEST ///
R = QQ[x_0..x_3]
J = ideal det(matrix{{x_0, x_1, x_2}, {x_1, x_0, x_3}, {x_2, x_3, x_0}})
assert(multiDegreeEDDegree(J) == 13)
///


--------------------
--MLDegree
--------------------
MLDegree = method(); 
MLDegree (List,List) := (F,u)-> (
    if not (sum F ==1) then error("The sum of functions is not equal to one.");
    m1 := diagonalMatrix F;
    m2 := for i in F list transpose jacobian ideal(i);
    m2p := fold(m2, (i,j) -> i || j);
    M := m1 | m2p;
    
    g := generators ker M;
    g' := matrix drop(entries g,-numrows g+#u);
    Ju' := ideal (matrix {u} * g');
    Ju := saturate(Ju');
    
    degree Ju
)

TEST ///
R = QQ[t]
s=1
u = {2,3,5,7}
F = {s^3*(-t^3-t^2-t+1),s^2*t,s*t^2,t^3}
assert( MLDegree (F,u) == 3) 
///

--------------------
--LagrangeMultiplierEDDegree
--------------------

probabilisticLagrangeMultiplierEDDegree = method(Options => {Data => null});
probabilisticLagrangeMultiplierEDDegree (Ideal,Ideal) := ZZ => opts -> (WI,I) -> (
    aLI := lagrangeIdeal(WI,I);
    X := gens ring I;
    g := if opts.Data===null then apply(X,i->random(1,1000) ) else opts.Data;
    degree criticalIdeal(X-g,aLI)
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
	Numerators => n,
	Denominators => d
	})
gradient (List) := Gradient => opts  -> (n) ->gradient(n,apply(n,i->1_(ring i)))

sub(Gradient,LagrangeIdeal) :=  (g,aLI) -> (
    n := apply(g.Numerators,i->sub(i,aLI));
    d := apply(g.Denominators,i->sub(i,aLI));
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
    if degreeLength  ring aLI<=4 then(
	u := gens coefficientRing ring (aLI);
	dataSub := if opts.Data===null then {} else apply(u,opts.Data,(i,j) -> i => j);
    	gCN := sub(g,aLI);
    	newJC := aLI.JacobianConstraint;
    	Lam := sub(aLI.ConormalRing.Factors#2//gens,aLI);
	y:=sub(aLI.ConormalRing.Factors#1//gens,aLI);
    	newJC = ideal apply(#y,
	    i->(
	    	lamSub := Lam/(j->j=>j*gCN.Denominators#i);	    	    
	    	gCN.Numerators#i + sub( newJC_i, lamSub )-y_i
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
    else error"degreeLength is not 4."--Should be able to handle any degree length
    )

criticalIdeal (List,LagrangeIdeal) := CriticalIdeal => opts  -> (g,aLI) ->criticalIdeal(gradient g,aLI,opts)
criticalIdeal (RingElement,LagrangeIdeal) := CriticalIdeal =>opts -> (psi,aLI) -> (
    g := apply(gens ring psi,x->diff(x,psi));
    criticalIdeal(g,aLI,opts)
    )

criticalIdeal (Gradient,Ideal) := CriticalIdeal =>opts -> (g,WI) -> (
    aLI := lagrangeIdeal WI;
    criticalIdeal(g,aLI,opts)
    )
criticalIdeal (List,Ideal) := CriticalIdeal =>opts -> (g,WI) ->criticalIdeal(gradient g,WI,opts)
criticalIdeal (RingElement,Ideal) := CriticalIdeal =>opts -> (psi,WI) -> (
    g := apply(gens ring psi,x->diff(x,psi));
    criticalIdeal(g,WI,opts)
    )

criticalIdeal (Gradient,Ideal,Ideal) := CriticalIdeal =>opts -> (g,WI,I) -> (
    aLI := lagrangeIdeal(WI,I);
    criticalIdeal(g,aLI,opts)
    )
criticalIdeal (List,Ideal,Ideal) := CriticalIdeal =>opts -> (g,WI,I) ->criticalIdeal(gradient g,WI,I,opts)
criticalIdeal (RingElement,Ideal,Ideal) := CriticalIdeal =>opts -> (psi,WI,I) -> (
    g := apply(gens ring psi,x->diff(x,psi));
    criticalIdeal(g,WI,I,opts)
    )

degree (CriticalIdeal) :=  CI -> (
    w := CI#JacobianConstraint;
    if CI#LagrangeIdeal#?PrimalIdeal 
    then w= w+sub(CI#LagrangeIdeal#PrimalIdeal,CI#LagrangeIdeal)
    else error"CriticalIdeal#LagrangeIdeal#?PrimalIdeal is false. ";
    u := gens coefficientRing ring (CI#LagrangeIdeal);
    dataSub := if CI.Data===null then {} else apply(u,CI.Data,(i,j)->i=>j);
    sCI := sub(w,dataSub);
    g := sub(CI#Gradient,CI#LagrangeIdeal);    
    scan( g.Denominators , d -> sCI = saturate(sCI, d) );
    degree sCI
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
toricMLIdeal = method(Options => {coeffRing => QQ})
toricMLIdeal(Matrix, List, List) := Ideal => opts -> (A, c, u) -> (
    t := symbol t;
    n := #c;
    R := QQ[t_1..t_(numgens target A)];
    N := sum u;
    toricMapA := transpose matrix {for i from 0 to n-1 list c_i*R_(entries A_i)};
    u = transpose matrix {u};
    A = sub(A,R); 
    MLIdeal := ideal(A*(N*toricMapA - u));  -- N A*v = A*u
    MLIdeal
    )

toricMLDegree = method(Options => {coeffRing => QQ})
toricMLDegree(Matrix, List) := Number => opts -> (A,c) -> (
    u := for i from 0 to #c-1 list random(1, 10^5);
    MLIdeal := toricMLIdeal(A, c, u);
    MLdegree := degree saturate(MLIdeal, (product gens ring MLIdeal)); 
    MLdegree
    )

TEST ///
A = matrix {{1,1,1,0,0,0,0,0,0}, {0,0,0,1,1,1,0,0,0},{0,0,0,0,0,0,1,1,1},
    {1,0,0,1,0,0,1,0,0},{0,1,0,0,1,0,0,1,0},{0,0,1,0,0,1,0,0,1}};
c = {1, 1, 1, 1, 1, 1, 1, 1, 1};
assert(2 == toricMLDegree(A, c));
c = {1,2,3,1,1,1,1,1,1};
assert(6 == toricMLDegree(A,c));
///


----------------------------------------
--Using witness sets code
----------------------------------------

--Each method in this section will rely on strategies 
-- These vary by implementation and algorithms used. 
-*
strategyIndex=new HashTable from {
	0=>regenerateBertiniIsolatedRegularCriticalPointSet,
	1=>bezoutBertiniIsolatedRegularCriticalPointSet
	}
*-

------------------------------
--IsolatedCriticalPointSet code
------------------------------

--code to compute witness points with various strategies.
IsolatedCriticalPointSet = new Type of WitnessSet;
--Always has the following keys.
-- CriticalIdeal
-- MultiplicityTolerance
-- EvaluationTolerance
-- ConditionNumberTolerance
-- WitnessSuperSet
-- SaveFileDirectory
-- Data => u
-- Gradient => g,
-- Slice => matrix{{}}
-- IsIrreducible => null,
-- Points --An index of points
-- Strategy


isolatedRegularCriticalPointSet = method(Options => {Strategy=>0});--Carry options over?
isolatedRegularCriticalPointSet (List,List,LagrangeIdeal) := IsolatedCriticalPointSet => opts  -> (u,g,aLI) ->(
    strategyIndex := new HashTable from {
	0=>regenerateBertiniIsolatedRegularCriticalPointSet,
	1=>bezoutBertiniIsolatedRegularCriticalPointSet
	};
    f := strategyIndex#(opts.Strategy);
    f(u,g,aLI)
    )


------------------------------
--UpdateWitnessSet code
------------------------------

--TODO: This needs to be redone like isolatedRegularCriticalPointSet and branch off into Bertini sections. 

updateEvaluationTolerance=(evalTol,ICPS)->(
    sols:=ICPS.WitnessSuperSet;
    wpIndex := delete(null,
	apply(#sols,i->(
		fn := "evaluation_"|i|"_mt_primal";
	    	p := sols_i;
	    	if isEvaluationZero(ICPS.SaveFileDirectory,fn,p,evalTol) then return i
	    	)));
    ICPS.EvaluationTolerance = evalTol;
    ICPS.Points=wpIndex;)

updateMultiplicityTolerance=(multiplicityTol,ICPS)->(
    sols:=ICPS.WitnessSuperSet;
    wpIndex := delete(null,
	apply(#sols,i->(
	    	p := sols_i;
		m := p.Multiplicity;
		if m<=multiplicityTol then return i
	    	)));
    ICPS.MultiplicityTolerance=multiplicityTol;
    ICPS.Points=wpIndex;)

updateConditionNumberTolerance=(conditionNumberTol,ICPS)->(
    sols:=ICPS.WitnessSuperSet;
    wpIndex := delete(null,
	apply(#sols,i->(
	    	p := sols_i;
		c := p.ConditionNumber;
		if c<=conditionNumberTol then return i
	    	)));
    ICPS.ConditionNumberTolerance=conditionNumberTol;
    ICPS.Points=wpIndex;)


--------------------
--bertiniCriticalPointSet code
--------------------


--Data,gradient,aLI,bic	
bertiniCriticalPointSet = (u,g,LVW,bic)->(
    evalTol :=-6;
    CI := criticalIdeal(g,LVW);
    dir := temporaryFileName();
    if not fileExists dir then mkdir dir;
    arCoords := CI#LagrangeIdeal.ConormalRing.Coordinates;
    avg := AffVariableGroup=>{arCoords#0,arCoords#2};
    bc := B'Constants => apply(gens coefficientRing ring LVW,u,(i,j)->i=>j);
    JC := CI.JacobianConstraint;
    WI := LVW.WitnessPrimalIdeal;
    makeB'InputFile(dir,avg,bc,
	NameB'InputFile=>"input_ss",
	BertiniInputConfiguration=>bic,
	B'Polynomials =>WI_*|JC_*);
    runBertini(dir,NameB'InputFile=>"input_ss");
    sols := importMainDataFile(dir);
    moveB'File(dir,"main_data","main_data_ss");
    I := LVW.PrimalIdeal;
    makeB'InputFile(dir,
	avg,bc,
	NameB'InputFile=>"input_mt_primal",
	BertiniInputConfiguration=>{"TrackType" => -4},
	B'Polynomials =>I_*);
    scan(#sols,i->(
	    p := sols_i;
	    writeStartFile(dir,{coordinates p},
		NameStartFile=>"start");
	    runBertini(dir,NameB'InputFile =>"input_mt_primal");
	    fn := "evaluation_"|i|"_mt_primal";
	    moveB'File(dir,"function",fn)));
    ICPS:=new IsolatedCriticalPointSet from {
    	EvaluationTolerance => evalTol,
    	SaveFileDirectory => dir,
    	Data => u,
	Gradient => g,
	Slice => matrix{{}},
    	WitnessSuperSet => sols,
	Points => null,
	IsIrreducible => null,
    	CriticalIdeal => CI
	};
    updateEvaluationTolerance(evalTol,ICPS);
    updateMultiplicityTolerance(1,ICPS);
    updateConditionNumberTolerance(1e10,ICPS);    
    ICPS
    )
 
 --test for the numerical version
 -*
TEST/// 
R=QQ[a,b][x,y] 
I=ideal(x^2+1*y^2-1)
LVW = lagrangeIdeal(I,I)
ring LVW
u ={7,99}
g= {x-a,y-b}
bic={}
--bertiniCriticalPointSet(u,g,LVW,bic)
ICPS = isolatedRegularCriticalPointSet (u,g,LVW)

ICPS = isolatedRegularCriticalPointSet (u,g,LVW,Strategy=>1)
--assert(2==#ICPS.Points)--Issue with keys here TODO. 
updateEvaluationTolerance(-100,ICPS)	
peek ICPS
--assert({}==ICPS.Points)--Issue with keys here TODO. 
isolatedRegularCriticalPointSet(u,g,LVW)
isolatedRegularCriticalPointSet(u,g,LVW,Strategy=>1)
peek oo

///
*-
------------------------------
--Index the stategies  code
------------------------------
--Five functions are needed to have a strategy.
----solve: From aLI and possible other arguments, outputs an IsolatedCriticalPointSet
----updateEvaluationTolerance 
----updateMultiplicityTolerance
----updateConditionNumberTolerance
-----Each update should also reclassify witness points. 

--------------------
--Stategy=>0 regenerateBertiniIsolatedRegularCriticalPointSet
--------------------

    --TODO: Fix print display.
regenerateBertiniIsolatedRegularCriticalPointSet = (u,g,LVW)->(
    bic := {"TrackType"=>0,"UseRegeneration"=>1};
    bertiniCriticalPointSet(u,g,LVW,bic))

----------
--Stategy=>1 bezoutBertiniIsolatedRegularCriticalPointSet 
----------

bezoutBertiniIsolatedRegularCriticalPointSet = (u,g,LVW)->(
    bic := {"TrackType"=>0,"UseRegeneration"=>0};
    bertiniCriticalPointSet(u,g,LVW,bic))


--TODO : bertiniSolve
--TODO : monodromySolve


--------------------
--Helper functions
--------------------

--Used to read Bertini function files which contain information about evaluations of a point. 
isEvaluationZero = (dir,fn,p,evalTol)->(
	    isRoot:= true;	    
	    scanLines(line->(
		     num := separateRegexp("[e ]", line);
		     if #num==4 
		     then (if min(value(num#1),value(num#3))>evalTol then isRoot=false)
		     else if #num>1 then error("parsing file incorrectly"|line)
		     ),
		     dir|"/"|fn
		     );		     
	    isRoot)


--Used to easily create options.
newPairs=(A,B)->apply(A,B,(i,j)-> i=>j)


--Used to determine if a symbolic method can be used
isCofficientRingInexact = R -> (
 -- This checks if kk is a ComplexField or RealField 
    kk := ultimate(coefficientRing,R);
--    instance(kk,InexactField)--This is probably better, but not sure. 
    member(kk,{ComplexField,RealField}) 
    )


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
    degree criticalIdeal(g,aLI,opts)
    )
probabilisticLagrangeMultiplierOptimizationDegree (RingElement,Ideal,Ideal) := ZZ => opts -> (psi,WI,I) -> (
    aLI := lagrangeIdeal(WI,I);
    degree criticalIdeal(psi,aLI,opts)
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
  conormalIdeal
///

doc ///
Key
  conormalIdeal
  (conormalIdeal, Ideal, ConormalRing)
--Headline
--  todo
Inputs
  I:Ideal
    defined in the primal variables only
  S:ConormalRing
Usage
  conormalIdeal(I,S)

Caveat
  The ring containing $I$ and $p$ must have primal variables in degree $\{1,0\}$ and dual variables in degree $\{0,1\}$.
  Such a ring can be obtained using @TO{conormalRing}@.
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
    probabilisticEDDegree I
    J = ideal((x^2+y^2+x)^2 - x^2 - y^2)
    probabilisticEDDegree J

  Text
    Instead of a random point, the user can specify their own point
  Example
    probabilisticEDDegree(I, Data => {2,3})

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
///


doc ///
Key
  sectionEDDegree
  (sectionEDDegree, Ideal)
Headline
  ED-degree via random linear sections
Description
  Text
    Let $X$ be a projective variety in $\mathbb{P}^n$ of codimension $\geq 2$, and let $\pi : \mathbb P^n \to \mathbb P^{n-1}$
    be a rational map induced by a general linear map $\mathbb C^{n+1} \to \mathbb C^n$. 
    Under some regularity assumptions (see Caveat), the ED-degree of $\pi(X)$ is equal to the ED-degree
    of $X$ [1, Cor. 6.1.].

    This function repeatedly such a map $\pi$ until the image becomes a hyperlane.
    Then, the function calls @TO probabilisticEDDegree@ or @TO symbolicEDDegree@, depending on the optional argument @TO [sectionEDDegree,Strategy]@.
    This may provide significant computational speedups compared to @TO probabilisticEDDegree@, @TO symbolicEDDegree@ or @TO multiDegreeEDDegree@,
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

    i7 : elapsedTime sectionEDDegree I
          0.0341013 seconds elapsed

    o7 = 1

  Text
    References: [1] Draisma, J., Horobeţ, E., Ottaviani, G., Sturmfels, B., & Thomas, R. R. (2016). The Euclidean distance degree of an algebraic variety. {\em Foundations of computational mathematics}, 16(1), 99-149.
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

    As an example, we see that the ED-degree of Cayley's cubic surface is 13
  Example
    R = QQ[x_0..x_3]
    J = ideal det(matrix{{x_0, x_1, x_2}, {x_1, x_0, x_3}, {x_2, x_3, x_0}})
    multiDegreeEDDegree(J)

Caveat
  The conormal variety cannot intersect the diagonal $\Delta(\mathbb{P}^{n-1}) \subset \mathbb{P}^{n-1} \times \mathbb{P}^{n-1}$.
  At the moment this is not checked.
///

doc ///
Key
   MLDegree
   (MLDegree,List,List) 
Usage
  MLDegree (F,u)
Inputs
  F:
    list of function
  u:
    list of numerical data
Outputs
  :Number
    the ML-degree of $F$
Description
  Text
    Computes the maximum likelihood degree by taking List of function and List of numerical data when summation F equal to 1.
    See algorithm 18. Solving the Likelihood Equations https://arxiv.org/pdf/math/0408270
  Example
    R = QQ[t]
    s=1
    u = {2,3,5,7}
    F = {s^3*(-t^3-t^2-t+1),s^2*t,s*t^2,t^3}
    MLDegree (F,u)
--Caveat
--  todo
--SeeAlso
--  
///


doc ///
Key
   toricMLIdeal
   (toricMLIdeal,Matrix,List,List) 
Usage
  toricMLIdeal(A, c, u)
Inputs
  A:
    the matrix of exponents defining the monomial map that parameterizes the toric variety
  c: 
    list of numbers used to create the scaled toric variety
  u:
    list of numerical data
Outputs
  :Ideal
    the critical ideal of likelihood equations for the corresponding scaled toric variety 
    as described in Birch's theorem.
Description
  Text
    Computes the critical ideal of a scaled toric variety using the equations 
    defined in Birch's theorem for given data $u$.
  Example
    A = matrix {{1,1,1,0,0,0,0,0,0}, {0,0,0,1,1,1,0,0,0},{0,0,0,0,0,0,1,1,1},{1,0,0,1,0,0,1,0,0},{0,1,0,0,1,0,0,1,0},{0,0,1,0,0,1,0,0,1}}
    c = {1,2,3,1,1,1,1,1,1}
    u = {15556, 84368, 98575, 27994, 61386, 84123, 62510, 37430, 34727};
    toricMLIdeal(A, c, u)
--Caveat
--  todo
--SeeAlso
--  
///


doc ///
Key
   toricMLDegree
   (toricMLDegree,Matrix,List) 
Usage
  toricMLDegree(A, c)
Inputs
  A:
    the matrix of exponents defining the monomial map that parameterizes the toric variety
  c: 
    list of numbers used to create the scaled toric variety
Outputs
  :Number
    the ML-degree of the corresponding toric variety
Description
  Text
    Computes the maximum likelihood degree of a toric variety using the equations 
    defined in Birch's theorem and randomly generated data
  Example
    A = matrix {{1,1,1,0,0,0,0,0,0}, {0,0,0,1,1,1,0,0,0},{0,0,0,0,0,0,1,1,1},{1,0,0,1,0,0,1,0,0},{0,1,0,0,1,0,0,1,0},{0,0,1,0,0,1,0,0,1}}
    c = {1,2,3,1,1,1,1,1,1}
    toricMLDegree(A,c)
--Caveat
--  todo
--SeeAlso
--  
///




doc /// --EDIT
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
    probabilisticLagrangeMultiplierOptimizationDegree(psi,WI,I)

  Text
    The function can handle polynomial objective functions psi or objective functions with rational functions as derivatives. 

  Example
    R=QQ[x,y]
    WI = I = ideal((x^2+y^2+x)^2-x^2-y^2)
    psi =x^2+2*x*y+3*y
    probabilisticLagrangeMultiplierOptimizationDegree(psi,WI,I)
    g ={3*x^2,3/y}--psi = x^3+ + 3*ln y
    probabilisticLagrangeMultiplierOptimizationDegree(g,WI,I)

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
    probabilisticLagrangeMultiplierEDDegree(WI, I)

  Text
    This function is probabilistic.

  Example
    R = QQ[x0,x1,x2,x3]
    WI = ideal(x0*x2-x1^2,x1*x3-x2^2)
    I = WI+ideal(x0*x3-x1*x2)
    probabilisticLagrangeMultiplierEDDegree(WI,I)

  Text
    This function is probabilistic and chooses the data at random by default. 
    A user may specify the data they want to use. 
    
    In the example below, the ED degree of a cardioid is 3 but the non-generic data choice does not recover this result
  Example
    R = QQ[x,y]
    WI = I = ideal((x^2+y^2+x)^2 - x^2 - y^2)
    probabilisticLagrangeMultiplierEDDegree(WI,I)
    probabilisticLagrangeMultiplierEDDegree(WI,I,Data=>{0,0})

SeeAlso
  probabilisticLagrangeMultiplierOptimizationDegree
///





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