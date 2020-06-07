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

