-- Copyright 1997 by Mike Stillman and Harry Tsai

Subring = new Type of HashTable
subring = method()
subring Matrix := M -> (
    R := ring M;
    new Subring from {
    	AmbientRing => R,
    	Generators => M,
	cache => new CacheTable from {}
	}
    )
subring List := L -> subring matrix{L}

gens Subring := o -> A -> A#Generators
numgens Subring := A -> numcols gens A
ambient Subring := A -> A#AmbientRing

debug Core

---------------------------------
-- Inhomogeneous SAGBI bases ----
---------------------------------

-- Sorts and adds the elements of the matrix m to the pending list of R
    -- R is a subalgebra
    -- candidates is a matrix of elements of the subalgebra.
    -- Algorithm makes a pass through the elements in m and places them in the correct sublist of pending.

insertPending = (R, candidates, maxDegree) -> (

    -- Check R.cache.pending exists!!!
    -- ADD THIS!!!

    -- i steps through the columns of candiates
    i := 0;
    while i < numcols candidates do (

        -- get the entry of the column and its degree
        candidate := candidates_(0,i);
        level := (degree candidate)_0;

        -- if the degree isn't too large, then add f to the correct list
        if level <= maxDegree then R.cache.Pending#level = append(R.cache.Pending#level, candidate);
        i = i+1;
    );
)

-- Finds the lowest nonempty list in Pending
    -- R is a subalgebra
    -- Algorithm makes a pass through the lists of Pending until it finds something nonempty

lowestDegree = (R, maxDegree) -> (
    -- i steps through the lists of Pending
    i := 0;
    while i <= maxDegree and R.cache.Pending#i === {} do i=i+1;
    i
)

-- Adds generators to the set of generators and computes the syzygies of the generators.  Also defines the appropriate ring maps for future use.
    -- R is a subalgebra
    -- newGens is a matrix of generators to be added

appendToBasis := (R, newGens) -> (
    
    -- Add the new generators to the subalgebra generators
    R.cache.SagbiGens = R.cache.SagbiGens | newGens;
    
    -- Find the number of generators of the ambient ring and the current list of subalgebra generators
    nBaseGens := numgens R.AmbientRing;
    nSubalgGens := numcols R.cache.SagbiGens;
    
    -- Create a ring with combined generators of base and subalgebra.  Monoid is needed for constructing a monomial order and the coefficient ring is used to construct the new ring.
    MonoidAmbient := monoid R.AmbientRing;
    CoeffField := coefficientRing R.AmbientRing;
    
    -- Add on an elimination order that eliminates the generators of the base.
    -- Create a monoid with variables for both nBaseGens and nSubalgGens.
    -- Degrees of generators are set so that the SyzygyIdeal is homogeneous.
    -- Original code, replaced by code from function.
    -- newOrder := appendElimination(MonoidAmbient.Options.MonomialOrder, Weights=>nBaseGens, nSubalgGens);
    newOrder := append(MonoidAmbient.Options.MonomialOrder, Weights=>nBaseGens:1);
    
    NewVariables := monoid[
        Variables=>nBaseGens+nSubalgGens,
        Degrees=>join(degrees source vars R.AmbientRing, degrees source R.cache.SagbiGens),
        MonomialOrder => newOrder];
    
    -- Construct the free monoid ring with coefficients in CoeffField and and variables for both the base and subalgebra.
    R.cache.TensorRing = CoeffField NewVariables;
    
    -- Construct maps between our rings to allow us to move polynomials around
    -- ProjectionInclusion sets the variables corresponding to the base equal to 0.  The result is in the tensor ring.
    -- ProjectionBase sets the variables corresponding to the subalgebra generators equal to 0 and maps into the ambient ring.
    -- InclusionBase is the inclusion map from the base ring to the tensor ring.  The variables are mapped to themselves
    -- Substitution repalces elements of the tensor ring with their formulas in terms of the base ring.
    R.cache.ProjectionInclusion = map(R.cache.TensorRing, R.cache.TensorRing,
        matrix {toList(nBaseGens:0_(R.cache.TensorRing))} |
	(vars R.cache.TensorRing)_{nBaseGens .. nBaseGens+nSubalgGens-1});
    
    R.cache.ProjectionBase = map(R.AmbientRing, R.cache.TensorRing,
        (vars R.AmbientRing) | matrix {toList(nSubalgGens:0_(R.AmbientRing))});
    
    R.cache.InclusionBase = map(R.cache.TensorRing, R.AmbientRing,
        (vars R.cache.TensorRing)_{0..nBaseGens-1});
    
    R.cache.Substitution = map(R.cache.TensorRing, R.cache.TensorRing,
        (vars R.cache.TensorRing)_{0..nBaseGens-1} | R.cache.InclusionBase(R.cache.SagbiGens));
    
    -- Construct an ideal consisting of variables repesenting subalgebra generators minus their leading term
    R.cache.SyzygyIdeal = ideal(
        (vars R.cache.TensorRing)_{nBaseGens..nBaseGens+nSubalgGens-1}-
	R.cache.InclusionBase(leadTerm R.cache.SagbiGens));
)    
    
-- ROW REDUCE FROM COMMON.
-- MONOMIAL FLAG DOES NOT SEEM TO WORK AT ALL.
-- WHAT IS THE CONSEQUENCE OF THIS???

rowReduce = (elems, d) -> (
    -- elems is a one row matrix of polynomials, all of degree d.
    -- return a (one row) matrix whose elements are row reduced
    -- CAUTION: Only the monomial orders GRevLex, Eliminate, Lex, and RevLex
    --              are supported by this routine.  The monomial orders
    --             Lex and ProductOrder ARE NOT SUPPORTED.
    (RH, RtoRH, RHtoR, elemsH) := 4:null;
    R := ring elems;
    n := numgens R;
    M := monoid R;
    moFlag := setMonomialOrderFlag R; -- THIS ISN'T DOING ANYTHING RIGHT NOW
    k := coefficientRing R;
    if moFlag == 5 then (
    N := monoid [Variables=>n+1, MonomialOrder => RevLex, Degrees => prepend({1},M.Options.Degrees)];
    RH = k N;
    RtoRH = map(RH,R,(vars RH)_{1..n});
    RHtoR = map(R,RH,matrix{{1_R}} | vars R);
    elemsH = homogenize(RtoRH elems, RH_0);)
    else (
    if moFlag == 2 then (
    << "WARNING: GLex is an unstable order for rowReduce" << endl)
    else if moFlag == 4 then (
    N = monoid [Variables=>n+1,
    MonomialOrder => append(M.Options.MonomialOrder,1),
    Degrees => append(M.Options.Degrees,{1})];
    RH = k)
    else (
    N = monoid [Variables=>n+1,
    MonomialOrder => M.Options.MonomialOrder,
    Degrees => append(M.Options.Degrees,{1})];
    RH = k N);
    RtoRH = map(RH,R,(vars RH)_{0..n-1});
    RHtoR = map(R,RH,vars R | matrix{{1_R}});
    elemsH = homogenize(RtoRH elems, RH_n););
    RHtoR gens gb(elemsH, DegreeLimit=>d)
)
-- END COPY OF ROW REDUCE

-- BEGINNING OF MONOMIAL ORDER FUNCTION

-- SAGBI-COMMON HELPER FUNCTIONS.
-- inscrutable -- Looks to be completely broken.
-- temporary patch fix given. preferrably won't need this function
setMonomialOrderFlag = (R) -> (
    tempflag := 0;
    temp := (monoid R).Options.MonomialOrder;
    if (class temp) === Nothing then (tempflag = 0)
    else if temp#1#0 === Lex then (tempflag = 1)
    else if (temp#1#0 === Weights and temp#2#0 === Lex) then (tempflag = 2)       --GLex
  --  else if (class temp) === Eliminate then (tempflag = 3)                       
  --  else if (class temp) === ProductOrder then (tempflag = 4)
    else if (#(temp#1#1) < # gens R) and temp#1#0 === Weights then (tempflag = 3) --Eliminate
    else if temp#2#0 != Position and temp#1#0 != Weights then (tempflag = 4)      --Product
    else if temp#1#0 === GRevLex then (tempflag = 0)                              --GRevLex                                  --Lex
    else if temp#1#0 === RevLex then (tempflag = 5);	    	    	    	  --RevLex
    tempflag)

-- END COPY OF MONOMIAL ORDER FUNCTION


--Accepts a matrix inputMatrix and returns a matrix of columns of inputMatrix whose entries all have total degree less than maxDegree
submatrixBelowDegree = (inputMatrix,maxDegree) -> (

    -- Selected cols are the columns where the degree condition is satisfied.
    selectedCols := positions(0..numcols inputMatrix - 1,
        i -> (degrees source inputMatrix)_i < {maxDegree});

    -- Construct the submatrix using only the columns selected above.
    inputMatrix_selectedCols)

--Accepts a matrix inputMatrix and returns a matrix of columns of inputMatrix where the highest degree entry has total degree equal to currDegree
    -- Why does this function require the input to be a matrix and an integer while the previous function does not.
submatrixByDegrees (Matrix,ZZ) := (inputMatrix,currDegree) -> (

    -- Selected cols are the columns where the degree condition is satisfied.
    selectedCols := positions(0..numcols inputMatrix - 1,
        i -> (degrees source inputMatrix)_i === {currDegree});

    -- Construct the submatrix using only the columns selected above.
    inputMatrix_selectedCols)

-- Reduces the lowest degree list in the pending list.  Adds the results to Pending.  The new lowest degree list in pending is added to the subalgebra basis.  Returns the number of elements added.
    -- !!!Assumes that the pending list has been subducted!!!
    -- R is the subalgebra

grabLowestDegree = (R, maxDegree) -> (
    -- Finds the current lowest degree of the pending list.
    currentLowest := lowestDegree(R, maxDegree);
    -- If there are elements in the pending list, then work on them.
    if currentLowest <= maxDegree then (    
    	-- Row reduce the matrix of the pending elements of lowest degree
    	-- WHAT IS THIS DOING???
    	reducedGenerators = rowReduce(matrix{R.cache.Pending#currentLowest}, currentLowest);
    	R.cache.Pending#currentLowest = {};
    	insertPending(R, reducedGenerators, maxDegree);
    	-- Find the lowest degree elements after reduction.
    	currentLowest = lowestDegree(R, maxDegree);
    	-- Count the number of new generators and add them to the basis
    	numNewGenerators := 0;
    	if currentLowest <= maxDegree then (
            numNewGenerators = #R.cache.Pending#currentLowest;
            appendToBasis(R, matrix{R.cache.Pending#currentLowest});
            R.cache.Pending#currentLowest = {};
	    );
    	-- If number of new generators is zero, then nothing was added because pending was empty.  There is no way for pending to be empty unless currentLowest is maxDegree + 1.
    	);
    currentLowest
)

-- Declaration of default options
    -- Strategy decides which algorithm to call for subduction
    -- Limit is a variable that bounds the number of computations (e.g., max degree, …)
    -- PrintLevel is a variable that determines output, larger values have more printing.

subalgebraBasis = method(Options => {
    Strategy => null,
    Limit => 100,
    PrintLevel => 0})

-- Main function for computing a subalgebraBasis.
    -- Input is a subring (which is an algebra).
    -- The default strategy is the engine-level strategy.

subalgebraBasis Subring := o -> R -> (

<< "Beginning of subalgebraBasis" << endl;

-- Declaration of variables
    -- baseRing is the ring of the input matrix
    -- sagbiGens is a list/matrix of all the generators
    -- semiRing is the free semigroup ring formed from the SAGBI generators
        -- I don't think that this is ever used.  Should be deleted!
    -- tensorRing is the ring formed from the tensor of the base ring and semigroup ring
    -- Pending is a list of lists, sorting elements of the algebra by degree

    -- projectionInclusion is the projection from the tensor ring to the semiRing by sending the base ring generators to 0.
    -- projectionToBase is the projection from the tensor ring to the baseRing by sending the SAGBI generators to 0.
    -- inclusionOfBase is the inclusion of the baseRing into the tensorRing

    -- currDegree is a number representing the current degree of interest
    -- nLoops is the number of loops of the algorithm
    -- maxDegree is the maximum degree of interest by the algorithm
    -- nNewGenerators is the number of new generators found in a loop

    -- CHECK IF THESE EXIST to avoid recomputing???

    R.cache.SagbiGens = null;   -- G
    R.cache.GensDegrees = null;
    R.cache.SemiRing = null;    -- S -- Does this get used???
    R.cache.TensorRing = null;  -- RS
    R.cache.SyzygyIdeal = null; -- J

    R.cache.ProjectionInclusion = null; -- RStoS
    R.cache.ProjectionBase = null;      -- RStoR
    R.cache.InclusionBase = null;       -- RtoRS
    R.cache.Substitution = null;        -- Gmap

    currDegree := null;     -- d
    nLoops := null;         -- nloops
    nNewGenerators := null; -- numnewsagbi
    isDone := false;
    sagbiGB := null;
    syzygyPairs := null;
    newElems := null;

    R.cache.Pending = new MutableList from toList(o.Limit+1:{}); -- Pending

    -- Create an empty matrix of generators.
    R.cache.SagbiGens = matrix(R.AmbientRing,{{}});

    -- Get the maximum degree of the generators.
        -- This is used as a stopping condition.
    maxGensDeg := (max degrees source R.Generators)_0;

    -- Only look at generators below degree limit.  Add those generators to the SubalgebraGenerators
    reducedGens := compress submatrixBelowDegree(R.Generators, o.Limit+1);
    insertPending(R, reducedGens, o.Limit);

    -- Remove elements of coefficient ring
    R.cache.Pending#0 = {};

    -- Get the lowest degree of the pending list.  Add 1 and initialize to number of loops
currDegree = grabLowestDegree(R, o.Limit) + 1;

    nLoops = currDegree;

    -- While the number of loops is within the limit and the isDone flag is false, continue to process
    while nLoops <= o.Limit and not isDone do (
        nLoops = nLoops + 1;
        
        << "Current Degree is " << currDegree << endl;
        << "Sagbi gens is " << peek R.cache.SagbiGens << endl;
    
        -- Construct a Groebner basis to eliminiate the base elements generators from the SyzygyIdeal.
        sagbiGB = gb(R.cache.SyzygyIdeal, DegreeLimit=>currDegree);
	<< "Current Degree is " << currDegree << endl;
    << "generators of GB " << gens sagbiGB << endl;
    << "selectInSubring is " << selectInSubring(1, gens sagbiGB) << endl;
    << "submatrixByDegrees is " << submatrixByDegrees(selectInSubring(1, gens sagbiGB), currDegree) << endl;
        syzygyPairs = R.cache.Substitution(submatrixByDegrees(selectInSubring(1, gens sagbiGB), currDegree));
    	<< "Syzygy pairs is " << syzygyPairs << endl;
        if R.cache.Pending#currDegree != {} then (
            syzygyPairs = syzygyPairs | R.cache.InclusionBase(matrix{R.cache.Pending#currDegree});
            R.cache.Pending#currDegree = {};
        );
        
        << "Before rawsubduction" << endl;
        << "R is " << describe R.AmbientRing << endl;
        << "spairs is " << syzygyPairs << endl;
        << "Gmap is " << R.cache.Substitution << endl;
        << "gbJ is " << sagbiGB << endl;
        
        subducted = R.cache.ProjectionBase(map(R.cache.TensorRing,rawSubduction(rawMonoidNumberOfBlocks raw monoid R.AmbientRing, raw syzygyPairs, raw R.cache.Substitution, raw sagbiGB)));
	<< "subducted is " << subducted << endl;
        newElems = compress subducted;
    	<< "number generators" << newElems << endl;
        if numcols newElems > 0 then (
            << numcols newElems << " generators added" << endl;
            insertPending(R, newElems, o.Limit);
            currDegree = grabLowestDegree(R, o.Limit);
        )
        else (
            nNewGenerators = 0;
            -- There was a toList here before.  Unnecessary (I think), so I deleted it.
	    -- T: no sum for MutableList
            -- Is the rawStatus even needed?
            if sum toList apply(R.cache.Pending, i -> #i) === 0 and rawStatus1 raw sagbiGB == 6 and currDegree > maxGensDeg then (
                isDone = true;
                << "SAGBI basis is FINITE!" << endl;
            	)
            );
            currDegree = currDegree + 1;
	<< "is Done is " << isDone << endl;
	<< "Loops is " << nLoops << endl;
    	);
    R
)
    

-- Main function for computing a subalgebraBasis.
    -- Input is a matrix of generators for the algebra.
    -- The default strategy is the engine-level strategy.

subalgebraBasis Matrix := o -> gensMatrix -> (
    R := subring gensMatrix;
    subalgebraBasis(R,o)
)

end--
restart
needs "sagbi.m2"
R=QQ[x,y]
A = subring matrix{{x+y,x*y,x*y^2}}
gens A -- gets the use-specified generators 
subalgebraBasis(A, Limit=>100)
