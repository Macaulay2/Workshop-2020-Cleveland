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
  PackageImports => {"Elimination","NumericalAlgebraicGeometry","Bertini"}
)

-----GOALS (5/15)
-- June 10 is the deadline for ISSAC Poster Submission: 
-- https://issac-conference.org/2020/calls/call-for-demo-posters.txt
-- Idea: Have the symbolic methods ready and call this package AlgebraicOptimizationDegree. 
-- If things go well, then we can do a JSAG submission called AlgebraicOptimization, which is an extended version that computes critical points 

--------------------
--Exports
--------------------

export {
  -- Methods
  "projectiveDual",
  "conormalRing",
  "conormalIdeal",
  "multiDegreeEDDegree",
  "symboliclagrangeMultiplierEDDegree",
  -- Options
  "DualVariable",
  --Types and keys
  "ConormalRing","CNRing","PrimalRing","DualRing","PrimalCoordinates","DualCoordinates",
  --More Types
  "LagrangeVarietyWitness","LagrangeIdeal", "IsolatedCriticalPointSet",
  --Methods
  "isolatedRegularCriticalPointSet","criticalIdeal","lagrangeIdeal",
  --More Keys
  "LagrangeVariable","PrimalIdeal","JacobianConstraint","AmbientRing","LagrangeCoordinates","WitnessPrimalIdeal",
  "Data", "Gradient", "WitnessSuperSet", "SaveFileDirectory",
  -- Tolerances
  "MultiplicityTolerance","EvaluationTolerance", "ConditionNumberTolerance",
  "Coordinates", "Factors",
  "Numerators","Denominators"
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
--LagrangeMultiplierEDDegree
--------------------
symboliclagrangeMultiplierEDDegree = method(Options => {Data => null});
symboliclagrangeMultiplierEDDegree Ideal := ZZ => opts -> I -> (
    aLI := lagrangeIdeal(I,I);
    X := gens ring I;
    g := if opts.Data==null then apply(X,i->random(1,1000) ) else opts.Data;
    degree criticalIdeal(X-g,aLI)
    )

TEST///
symboliclagrangeMultiplierEDDegree(ideal(x^2+y^2-1))
symboliclagrangeMultiplierEDDegree(ideal((x^2+y^2+x)^2-x^2-y^2))
///

------------------------------
-- Lagrange multipliers code
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

sub(x,aLI)
sub({x},aLI)//first
sub(ideal x, aLI)

///



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
TEST///
R=QQ[x,y]
assert(2==#keys gradient({x}))
assert(2 == # keys gradient({x},{y}))
///
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
    criticalIdeal(g,aLI,opts);
    )

criticalIdeal (Gradient,Ideal) := CriticalIdeal =>opts -> (g,WI) -> (
    aLI := lagrangeIdeal WI;
    criticalIdeal(g,aLI,opts);
    )
criticalIdeal (List,Ideal) := CriticalIdeal =>opts -> (g,WI) ->criticalIdeal(gradient g,WI)
criticalIdeal (RingElement,Ideal) := CriticalIdeal =>opts -> (psi,WI) -> (
    g := apply(gens ring psi,x->diff(x,psi));
    criticalIdeal(g,WI,opts);
    )

criticalIdeal (Gradient,Ideal,Ideal) := CriticalIdeal =>opts -> (g,WI,I) -> (
    aLI := lagrangeIdeal(WI,I);
    criticalIdeal(g,aLI,opts);
    )
criticalIdeal (List,Ideal,Ideal) := CriticalIdeal =>opts -> (g,WI,I) ->criticalIdeal(gradient g,WI,I)
criticalIdeal (RingElement,Ideal,Ideal) := CriticalIdeal =>opts -> (psi,WI,I) -> (
    g := apply(gens ring psi,x->diff(x,psi));
    criticalIdeal(g,WI,I,opts);
    )

degree (CriticalIdeal) :=  CI -> (
    w := CI#JacobianConstraint;
    if CI#LagrangeIdeal#?PrimalIdeal 
    then w= w+sub(CI#LagrangeIdeal#PrimalIdeal,CI#LagrangeIdeal)
    else error"CriticalIdeal#LagrangeIdeal#?PrimalIdeal is false. ";
    u := gens coefficientRing ring (CI#LagrangeIdeal);
    dataSub := if CI.Data===null then {} else apply(u,CI.Data,(i,j)->i=>j);
    degree sub(w,dataSub)
    )    


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

WCI = criticalIdeal({x-a,y-b},aLI,Data=>{2,19})
assert(2==degree WCI)--ED degree of the circle
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
    print avg;
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
    print currentTime();
    updateEvaluationTolerance(evalTol,ICPS);
    updateMultiplicityTolerance(1,ICPS);
    updateConditionNumberTolerance(1e10,ICPS);    
    ICPS
    )
 
TEST/// 
R=QQ[a,b][x,y] 
I=ideal(x^2+1*y^2-1)
LVW = lagrangeIdeal(I,I)
ring LVW
u ={7,99}
g= {x-a,y-b}
bic={}
bertiniCriticalPointSet(u,g,LVW,bic)
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

TEST///
R=QQ[a,b][x,y]
I=ideal(x^2+y^2-1)
WI=I
LVW = witnessLagrangeVariety(WI,I)
ring LVW
needsPackage"Bertini"
///


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



