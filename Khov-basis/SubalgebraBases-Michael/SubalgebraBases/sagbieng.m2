-- Copyright 1997 by Mike Stillman and Harry Tsai

---------------------------------
-- Inhomogeneous SAGBI bases ----
---------------------------------
sagbiEngine = (Gens, maxnloops, printlevel) -> (
     (R, G, S, RS, RStoS, Gmap, inGmap, J) := 8:null;
     (d, maxdeg, nloops, Pending) := 4:null;
     numnewsagbi := null;

<< "=================" << endl;
<< "Initializiation Data" << endl;
<< "Gens = " << Gens << endl;
<< "Class of Gens = " << class(Gens) << endl;
<< "maxnloops = " << maxnloops << endl;
<< "printlevel = " << printlevel << endl;
<< "R = " << R << endl;
<< "G = " << G << endl;
<< "S = " << S << endl;
<< "RS = " << RS << endl;
<< "RStoS = " << RStoS << endl;
<< "Gmap = " << Gmap << endl;
<< "inGmap = " << inGmap << endl;
<< "J = " << J << endl;
<< "d= " << d << endl;
<< "maxdeg = " << maxdeg << endl;
<< "nloops = " << nloops << endl;
<< "Pending = " << Pending << endl;
<< "numnewsagbi = " << numnewsagbi << endl;
<< "=================" << endl;

     R = ring Gens;
     maxdeg = maxnloops;
     Pending = new MutableList from toList(maxdeg+1:{});
     RtoRS := null;
     RStoR := null;

<< "=================" << endl;
<< "Second Initialization" << endl;
<< "R = " << R << endl;
<< "maxdeg = " << maxdeg << endl;
<< "Pending = " << Pending << endl;
<< "Elements of Pending = " << peek(Pending) << endl;
<< "RtoRS = " << RtoRS << endl;
<< "RStoR = " << RStoR << endl;
<< "=================" << endl;

     insertPending := (m) -> (
	  -- append the entries of the one row matrix 'm' to Pending.
	  i := 0;

<< "**************" << endl;
<< "Data from insert pending" << endl;
<< "m = " << m << endl;

	  while i < numgens source m do (
	      f := m_(0,i);

<< "i = " << i << endl;
<< "f = " << f << endl;

	      e := (degree f)_0;
	      Pending#e = append(Pending#e, f);

<< "e = " << e << endl;
<< "Pending = " << Pending << endl;
<< "Elements of Pending = " << peek(Pending) << endl;
	      i = i+1;
	      )
<< "************" << endl;


);

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
