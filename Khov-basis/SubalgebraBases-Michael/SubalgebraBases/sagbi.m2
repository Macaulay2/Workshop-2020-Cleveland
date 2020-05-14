-- Copyright 1997 by Mike Stillman and Harry Tsai

needs "subring.m2"

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
    i;
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
        (vars R.TensorRing)_{nBaseGens..nBaseGens+nSubalgGens-1}-
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

-- inscrutable -- Looks to be completely broken.
setMonomialOrderFlag = (R) -> (
    tempflag := 0;
    temp := (monoid R).Options.MonomialOrder;
    if (class temp) === Nothing then (tempflag = 0)
    else if temp === GRevLex then (tempflag = 0)
    else if temp === Lex then (tempflag = 1)
    else if temp === GLex then (tempflag = 2)
    else if (class temp) === Eliminate then (tempflag = 3)
    else if (class temp) === ProductOrder then (tempflag = 4)
    else if temp === RevLex then (tempflag = 5);
    tempflag)

-- END COPY OF ROW REDUCE

-- Reduces the lowest degree list in the pending list.  Adds the results to Pending.  The new lowest degree list in pending is added to the subalgebra basis.  Returns the number of elements added.
    -- !!!Assumes that the pending list has been subducted!!!
    -- R is the subalgebra

grabLowestDegree = (R, maxDegree) -> (

    -- Finds the current lowest degree of the pending list.
    currentLowest := lowestDegree(R, maxDegree);

    -- If there are elements in the pending list, then work on them.
    if currentLowest <= maxdeg then (

        -- Row reduce the matrix of the pending elements of lowest degree
        -- WHAT IS THIS DOING???
        -- THIS IS IN COMMON, MOVE IT HERE.
    reducedGenerators = rowReduce(matrix{R.cache.Pending#currentLowest}, currentLowest);
    R.cache.Pending#currentLowest = {};
    insertPending(R, reducedGenerators, maxDegree);

    -- Find the lowest degree elements after reduction.
    currentLowest = lowestDegree(R, maxDegree);

    -- Count the number of new generators and add them to the basis
    numNewGenerators := 0;
    if currentLowest <= maxDegree then (
        numNewGenerators = #R.cache.Pending#currentLowest;
        appendToBasis(R, R.cache.Pending#currentLowest);
        R.cache.Pending#currentLowest = {};)

    -- If number of new generators is zero, then nothing was added because pending was empty.  There is no way for pending to be empty unless currentLowest is maxDegree + 1.
    numNewGenerators)

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

subalgebraBasis Subring := opts -> R -> (

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

    maxDegree := Limit;                                            -- maxdeg
    R.cache.Pending = new MutableList from toList(maxDegree+1:{}); -- Pending

    -- missing inGmap, newguys, ...


-- Current edit line












     G = matrix(R, {{}});
     Gensmaxdeg := (max degrees source Gens)_0;
     Gens = compress submatrixBelowDegree(Gens, maxdeg+1);
     insertPending Gens;

<< "=================" << endl;
<< "MAIN FUNCTION DATA" << endl;
<< "G = " << G << endl;
<< "Gensmaxdeg = " << Gensmaxdeg << endl;
<< "max degrees = " << max degrees source Gens << endl;
<< "Gens = " << Gens << endl;
<< "Pending = " << Pending << endl;
<< "Elements of Pending = " << peek(Pending) << endl;
<< "=================" << endl;

     Pending#0 = {};
     d = grabLowestDegree();  -- initializes G

<< "=================" << endl;
<< "d = " << d << endl;
<< "G = " << G << endl;
<< "=================" << endl;

     d = d+1;
     nloops = d;
     isdone := false;
     while nloops <= maxnloops and not isdone do (
       ttotal := timing(
	  nloops = nloops+1;
	  if printlevel > 0 then
	    << "--- degree " << d << " ----" << endl;
     	  tgbJ := timing gb(J, DegreeLimit=>d);

<< "=================" << endl;
<< "J = " << J << endl;
<< "tgbJ = " << peek(tgbJ#1) << endl;
<< "tgbJ Generators = " << gens(tgbJ#1) << endl;
<< "=================" << endl;

	  gbJ := tgbJ#1;
	  if printlevel > 0 then 
	    << "    gb comp done in " << tgbJ#0 << " seconds" << endl;
	  -- spairs = time mingens ideal selectInSubring(1, gens gbJ);
	  spairs := submatrixByDegrees(selectInSubring(1, gens gbJ), d);
	  if printlevel > 1 then
	    << "spairs = " << transpose spairs << endl;
	  tGmap := timing Gmap(spairs);
	  spairs = tGmap#1;
	  if printlevel > 0 then 
	    << "    Gmap    done in " << tGmap#0 << " seconds" << endl;
	  if Pending#d != {} then (
	       newgens := RtoRS(matrix{Pending#d});
	       spairs = spairs | newgens;
	       Pending#d = {};);
	  tsub := timing map(RS,rawSubduction(rawMonoidNumberOfBlocks raw monoid R, raw spairs, raw Gmap, raw gbJ));
	  if printlevel > 0 then 
	    << "    subduct done in " << tsub#0 << " seconds" << endl;
     	  tRS := timing compress RStoR(tsub#1);
	  newguys := tRS#1;
	  if printlevel > 0 then
	    << "    RStoR   done in " << tRS#0 << " seconds" << endl;
	  if numgens source newguys > 0 
	  then (
	       if printlevel > 0 then 
     	         << "    GENERATORS ADDED!" << endl;
	       insertPending newguys;
	       d = grabLowestDegree();
	       if printlevel > 0 then 	       
	         << "    " << numnewsagbi << " NEW GENERATORS!" << endl;
	       )
	  else (
	       numnewsagbi = 0;
	       ngens := sum apply(toList Pending,i -> #i);
	       if ngens === 0 and gbDone gbJ and d>Gensmaxdeg then (
	           isdone = true;
		   if printlevel > 0 then 
		     << "    SAGBI basis is FINITE!" << endl;
		   );
	      );
	   );
	 if printlevel > 0 then (
	   << "    deg " << d << "  done in " << ttotal#0 << " seconds" << endl;
	   );
	 d=d+1;
	 );
     G)

-- Main function for computing a subalgebraBasis.
    -- Input is a matrix of generators for the algebra.
    -- The default strategy is the engine-level strategy.

subalgebraBasis Matrix := opts -> gensMatrix -> (
    R := subring gensMatrix;
    subalgebraBasis(R,opts);
)
