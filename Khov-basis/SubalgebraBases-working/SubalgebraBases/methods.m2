load "sagbi-common.m2"
load "sagbitop.m2"
load "sagbieng.m2"

-- global variable storing options for khov-basis computation
subalgebraBasisOptions = new OptionTable from {
    Limit => 100, 
    PrintLevel => 0, 
    Strategy => new HashTable from {"subduct"=>Engine, "gb" => FourTiTwo}}

-- want to compare user-specified options with cached options
-- if different, recompute
HashTable == HashTable := (O1, O2) -> (
    keysEqual := (keys O1 == keys O2);
    (keys O1, keys O2);
    << keysEqual << endl;
    valuesEqual := (values O1 == values O2);
    << valuesEqual << endl;
    keysEqual and valuesEqual
    )


-- this will become "subalgebraBasis"
subalgebraBasis = method(Options => subalgebraBasisOptions)
subalgebraBasis Matrix := o -> Gens -> (
    -- unloading options: not currently used
    (maxnloops, printlevel) := (o.Limit, o.PrintLevel);
    (subductionStrategy, gbStrategy) := (o.Strategy#"subduct", o.Strategy#"gb");
    -- old code
    (d, maxdeg, nloops, Pending) := 4:null;
    numnewsagbi := null;
    R = ring Gens;
    maxdeg = maxnloops;
    Pending = new MutableList from toList(maxdeg+1:{});
    RtoRS := null;
    RStoR := null;
    insertPending := (m) -> (
	-- append the entries of the one row matrix 'm' to Pending.
	i := 0;
	while i < numgens source m do (
	    f := m_(0,i);
	    e := (degree f)_0;
	    Pending#e = append(Pending#e, f);
	    i = i+1;
	    )
	);
    lowestDegree := () -> (
	-- returns maxdeg+1 if Pending list is empty, otherwise
	-- returns the smallest non-empty strictly positive degree.
	i := 0;
	while i <= maxdeg and Pending#i === {} do i=i+1;
	i
	);
    appendToBasis := (m) -> (
	R := ring m;
	M := monoid R;
	G = G | m;
	nR := numgens R;
	nG := numgens source G;
	newOrder := appendElimination(M.Options.MonomialOrder, nR, nG);
	k := coefficientRing R;
	N := monoid [
	    Variables => nR + nG,
	    Degrees=>join(degrees source vars R, degrees source G),
	    MonomialOrder => newOrder];
	RS = k N;
	RtoRS = map(RS,R,(vars RS)_{0..nR-1});
	RStoS = map(RS,RS, matrix {toList(nR:0_RS)} |
	    (vars RS)_{nR .. nR+nG-1});
	J = ideal((vars RS)_{nR..nR+nG-1}-RtoRS(leadTerm G));
	Gmap = map(RS,RS,(vars RS)_{0..nR-1} | RtoRS(G));
	RStoR = map(R,RS,(vars R) | matrix {toList(nG:0_R)});
	);
    grabLowestDegree := () -> (
	-- assumes: lowest degree pending list is already autosubducted.
	-- this row reduces this list, placing all of the
	-- entries back into Pending, but then appends the lowest
	-- degree part into the basis.
	e := lowestDegree();
	if e <= maxdeg then (
	    trr := timing rowReduce(matrix{Pending#e}, e);
	    timerr := trr#0;
	    if printlevel > 0 then
	    << "    rowred  done in " << timerr << " seconds" << endl;
	    m := trr#1;
	    Pending#e = {};
	    insertPending m;
	    e = lowestDegree();
	    numnewsagbi = #Pending#e;
	    timeapp := (timing appendToBasis matrix{Pending#e})#0;
	    if printlevel > 0 then 
	    << "    append  done in " << timeapp << " seconds" << endl;
	    Pending#e = {};
	    );
	e
	);
    G = matrix(R, {{}});
    Gensmaxdeg := (max degrees source Gens)_0;
    Gens = compress submatrixBelowDegree(Gens, maxdeg+1);
    insertPending Gens;
    Pending#0 = {};
    d = grabLowestDegree();  -- initializes G 
    d = d+1;
    nloops = d;
    isDone := false;
    while nloops <= maxnloops and not isDone do (
       	ttotal := timing(
	    nloops = nloops+1;
	    if printlevel > 0 then
	    << "--- degree " << d << " ----" << endl;
     	    tgbJ := timing gb(J, DegreeLimit=>d);
	    gbJ := tgbJ#1;
	    if printlevel > 0 then 
	    << "    gb comp done in " << tgbJ#0 << " seconds" << endl;
	    spairs := time submatrixByDegrees(mingens ideal selectInSubring(1, gens gbJ), d);
	    --spairs := submatrixByDegrees(selectInSubring(1, gens gbJ), d);
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
	           isDone = true;
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
     (G, isDone)
     )
