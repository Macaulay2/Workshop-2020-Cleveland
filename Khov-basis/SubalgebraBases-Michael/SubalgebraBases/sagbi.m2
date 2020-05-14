-- Copyright 1997 by Mike Stillman and Harry Tsai

needs "subring.m2"

---------------------------------
-- Inhomogeneous SAGBI bases ----
---------------------------------

-- Sorts and adds the elements of the matrix m to the pending list of R
    -- R is a subalgebra
    -- m is a matrix of elements of the subalgebra.
    -- Algorithm makes a pass through the elements in m and places them in the correct sublist of pending.

insertPending = (R, m, maxDegree) -> (

    -- Check R.cache.pending exists!!!
    -- ADD THIS!!!

    -- i steps through the columns of m
    i := 0;
    while i < numcols m do (
        -- get the entry of the column and its degree
        f := m_(0,i);
        e := (degree f)_0;

        -- if the degree isn't too large, then add f to the correct list
        if e <= maxDegree then R.cache.Pending#e = append(R.cache.Pending#e, f);
        i = i+1;
    );
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

subalgebraBasis Subring := opts -> R -> (

-- Declaration of variables
    -- baseRing is the ring of the input matrix
    -- sagbiGens is a list/matrix of all the generators
    -- semiRing is the free semigroup ring formed from the SAGBI generators
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
    R.cache.SemiRing = null;    -- S
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



     lowestDegree := () -> (
	  -- returns maxdeg+1 if Pending list is empty, otherwise
	  -- returns the smallest non-empty strictly positive degree.
	  i := 0;
	  while i <= maxdeg and Pending#i === {} do i=i+1;
	  i);




     appendToBasis := (m) -> (
	  R := ring m;
	  M := monoid R;

<< "*************" << endl;
<< "Data from append to Basis" << endl;
<< "m = " << m << endl;
<< "R = " << R << endl;
<< "M = " << M << endl;
<< "G = " << G << endl;

	  G = G | m;
	  nR := numgens R;
	  nG := numgens source G;


	  newOrder := appendElimination(M.Options.MonomialOrder, nR, nG);
	  k := coefficientRing R;
	  N := monoid [
	       Variables => nR + nG,
	       Degrees=>join(degrees source vars R, degrees source G),
	       MonomialOrder => newOrder];

<< "G = " << G << endl;
<< "nR = " << nR << endl;
<< "nG = " << nG << endl;
<< "Source of G = " << source(G) << endl;
<< "newOrder = " << newOrder << endl;
<< "k = " << k << endl;
<< "N = " << N << endl;

	  RS = k N;
	  RtoRS = map(RS,R,(vars RS)_{0..nR-1});
	  RStoS = map(RS,RS, matrix {toList(nR:0_RS)} |
	       (vars RS)_{nR .. nR+nG-1});
	  J = ideal((vars RS)_{nR..nR+nG-1}-RtoRS(leadTerm G));
	  Gmap = map(RS,RS,(vars RS)_{0..nR-1} | RtoRS(G));
	  RStoR = map(R,RS,(vars R) | matrix {toList(nG:0_R)});

<< "RS = " << RS << endl;
<< "RtoRS = " << RtoRS << endl;
<< "RStoS = " << RStoS << endl;
<< "J = " << J << endl;
<< "Generators of J = " << (vars RS)_{nR..nR+nG-1}-RtoRS(leadTerm G) << endl;
<< "Gmap = " << Gmap << endl;
<< "RStoR = " << RStoR << endl;

<< "****************" << endl;

	  );


     grabLowestDegree := () -> (
	  -- assumes: lowest degree pending list is already autosubducted.
	  -- this row reduces this list, placing all of the
	  -- entries back into Pending, but then appends the lowest
	  -- degree part into the basis.

<< "*************" << endl;
<< "Data from grabLowestDegree" << endl;

	  e := lowestDegree();
	  if e <= maxdeg then (
	       trr := timing rowReduce(matrix{Pending#e}, e);
	       timerr := trr#0;
	       if printlevel > 0 then
	         << "    rowred  done in " << timerr << " seconds" << endl;
	       m := trr#1;

<< "Matrix to be reduced = " << rowReduce(matrix{Pending#e},e) << endl;
<< "Reduced matrix m = " << m << endl;

	       Pending#e = {};
	       insertPending m;
	       e = lowestDegree();
	       numnewsagbi = #Pending#e;
	       timeapp := (timing appendToBasis matrix{Pending#e})#0;
	       if printlevel > 0 then 
	         << "    append  done in " << timeapp << " seconds" << endl;
	       Pending#e = {};
	       );
<< "*************" << endl;

	  e);





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
