debug Core

-- ?????
gbDone = (G) -> (rawStatus1 raw G == 6)

gbIsDone = (m) -> (
     -- only checks whether a 'non-syzygy' GB has completed
     m#?{false,0} and 
     (m#{false,0}).returnCode === 0)

Matrix % Ideal := (f,I) -> (
     if isHomogeneous f and isHomogeneous I then (
	  m := max degrees source f;
	  g := gb(I,DegreeLimit=>m);
          f % g)
     else f % gb I)

-- inscrutable
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

-- modifying monomial order in auxialiary ring for subduction computations
appendElimination = (monorder, nold, nnew) -> (
     -- returns a monomial order
     append(monorder, Weights=>nold:1)
     )

submatrixByDegrees (Matrix,ZZ) := (m,d) -> (
    want := positions(0..numgens source m - 1, 
	             i -> (degrees source m)_i === {d});
    m_want)

submatrixBelowDegree = (m,d) -> (
    want := positions(0..numgens source m - 1, 
	             i -> (degrees source m)_i < {d});
    m_want)

rowReduce = (elems, d) -> (
     -- elems is a one row matrix of polynomials, all of degree d.
     -- return a (one row) matrix whose elements are row reduced
     -- CAUTION: Only the monomial orders GRevLex, Eliminate, Lex, and RevLex
     --	     	 are supported by this routine.  The monomial orders
     --	    	 Lex and ProductOrder ARE NOT SUPPORTED.
     (RH, RtoRH, RHtoR, elemsH) := 4:null;
     R := ring elems;
     n := numgens R;
     M := monoid R;
     moFlag := setMonomialOrderFlag R;
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
     RHtoR gens gb(elemsH, DegreeLimit=>d))

rowReduce0 = (elems, d) -> (
     << "rowReduce(" << d << "): " << transpose elems << endl;
     result := rowReduce0(elems,d);
     << "  result: " << transpose result << endl;
     result
     )

subalgebraBasis = method(Options => {
	  Strategy => null,
	  Limit => 100,
	  PrintLevel => 0})

subalgebraBasis Matrix := opts -> (M) -> (
     if opts.Strategy =!= null then
       sagbiEngine(M, opts.Limit, opts.PrintLevel)
     else
       sagbiToplevel(M, opts.Limit, opts.PrintLevel)     
     )


--previously internal functions
insertPending = (m, Pending) -> (
	-- append the entries of the one row matrix 'm' to Pending.
	i := 0;
	while i < numgens source m do (
	    f := m_(0,i);
	    e := (degree f)_0;
	    Pending#e = append(Pending#e, f);
	    i = i+1;
	    ));
lowestDegree = (maxdeg, Pending) -> (
        -- returns maxdeg+1 if Pending list is empty, otherwise
        -- returns the smallest non-empty strictly positive degree.
	i := 0;
	while i <= maxdeg and Pending#i === {} do i=i+1;
	i);


combinedBasis = method(Options => {
    Strategy => null,
    Limit => 100,
    PrintLevel => 0})

combinedBasis := opts -> (gensMatrix) -> (

-- Declaration and Initialization of variables
    -- baseRing is the ring of the input matrix
    -- sagbiGens is a list/matrix of all the generators
    -- semiRing is the free semigroup ring formed from the SAGBI generators
    -- tensorRing is the ring formed from the tensor of the base ring and semigroup ring
    -- Pending is a list of lists, sorting elements of the algebra by degree

    -- projectionToSemi is the projection from the tensor ring to the semiRing by sending the base ring generators to 0.
    -- projectionToBase is the projection from the tensor ring to the baseRing by sending the SAGBI generators to 0.
    -- inclusionOfBase is the inclusion of the baseRing into the tensorRing

    -- currDegree is a number representing the current degree of interest
    -- nLoops is the number of loops of the algorithm
    -- maxDegree is the maximum degree of interest by the algorithm
    -- nNewGenerators is the number of new generators found in a loop

(baseRing, sagbiGens, semiRing, tensorRing, syzygyIdeal, Pending) := 6:null;
(projectionToSemi, projectionToBase, inclusionOfBase) := 3:null;
(currDegree, nLoops, maxDegree, nNewGenerators) := 4:null;

--
baseRing = ring gensMatrix;
Pending = new MutableList from toList(maxDegree+1:{});



)

end

--START ENGINE LEVEL--

sagbiEngine = (Gens, maxnloops, printlevel) -> (

Gmap,
inGmap,

Pending = new MutableList from toList(maxdeg+1:{});
insertPending := (m) -> (
-- append the entries of the one row matrix 'm' to Pending.
i := 0;
while i < numgens source m do (
f := m_(0,i);
e := (degree f)_0;
Pending#e = append(Pending#e, f);
i = i+1;
));
lowestDegree := () -> (
-- returns maxdeg+1 if Pending list is empty, otherwise
-- returns the smallest non-empty strictly positive degree.
i := 0;
while i <= maxdeg and Pending#i === {} do i=i+1;
i);
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
e);
G = matrix(R, {{}});
Gensmaxdeg := (max degrees source Gens)_0;
Gens = compress submatrixBelowDegree(Gens, maxdeg+1);
insertPending Gens;
Pending#0 = {};
d = grabLowestDegree();  -- initializes G
d = d+1;
nloops = d;
isdone := false;
while nloops <= maxnloops and not isdone do (
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


--END ENGINE LEVEL--

--START TOP LEVEL--

sagbiquo(Matrix,Ideal,ZZ,ZZ) := (Gens, I, maxnloops, printlevel) -> (
(R, G, S, RS, RStoS, Gmap, inGmap, J) := 8:null;
(d, maxdeg, nloops, Pending) := 4:null;
(newgens, newguys) := 2:null;
gbI := null;
Jquo := null;
gbJquo := null;
IinRS := null;
RtoRS := null;
RStoR := null;
numnewsagbi := null;
R = ring Gens;
MOflag := setMonomialOrderFlag R;
maxdeg = maxnloops;
Pending = new MutableList from toList(maxdeg+1:{});
autosubductionquo := (m) -> (
-- m is the matrix whose entries we wish to reduce (subduct),
-- these elements are all in the same degree d.
if I != 0 then m = m % IinRS;
reduced := map(target m, source m, 0);
while m != 0 do (
m = matrix entries m;  -- to fix degrees
errorterm1 := (leadTerm m) % gbJquo;
errorterm2 := RStoS errorterm1;
mm := split(m, errorterm2);
h := leadTerm(mm);
reduced = reduced + h;
if I == 0 then (m = m - h - (Gmap errorterm2))
else (m = m - h - ((Gmap errorterm2)%IinRS));
);
reduced = compress reduced;
reduced = matrix entries reduced; -- fix degrees
reduced
);
insertPending := (m) -> (
-- append the entries of the one row matrix 'm' to Pending.
i := 0;
while i < numgens source m do (
f := m_(0,i);
e := (degree f)_0;
Pending#e = append(Pending#e, f);
i = i+1;
));
lowestDegree := () -> (
-- returns maxdeg+1 if Pending list is empty, otherwise
-- returns the smallest non-empty strictly positive degree.
i := 0;
while i <= maxdeg and Pending#i === {} do i=i+1;
i);
appendToBasis := (m) -> (
R := ring m;
M := monoid R;
G = G | m;
nR := numgens R;
nG := numgens source G;
if MOflag == 5 then (
RS = (coefficientRing R)[Variables=>nG+nR,--b_1..b_nG,a_1..a_nR,
Degrees=>join(degrees source G, degrees source vars R),
MonomialOrder => RevLex];
RtoRS = map(RS,R,(vars RS)_{nG..nG+nR-1});
Jquo = ideal(((vars RS)_{0..nG-1} - RtoRS(leadTerm G)) |
RtoRS(leadTerm gbI));
Gmap = map(RS,RS, RtoRS(G) | (vars RS)_{nG..nG+nR-1});
IinRS = RtoRS I;
RStoR = map(R,RS,matrix {toList(nG:0_R)} | vars R);
RStoS = map(RS,RS, (vars RS)_{0..nG-1} |
matrix {toList(nR:0_RS)});)
else (
newOrder := if MOflag == 0 or MOflag == 3 then Eliminate nR
else if MOflag == 4 then append(M.Options.MonomialOrder,nG)
else M.Options.MonomialOrder;
RS = (coefficientRing R)[Variables=>nG+nR,--a_1..a_nR,b_1..b_nG,
Degrees=>join(degrees source vars R, degrees source G),
MonomialOrder => newOrder];
RtoRS = map(RS,R,(vars RS)_{0..nR-1});
RStoS = map(RS,RS, matrix {toList(nR:0_RS)} |
(vars RS)_{nR .. nR+nG-1});
Jquo = ideal(((vars RS)_{nR..nR+nG-1}-RtoRS(leadTerm G)) |
RtoRS(leadTerm gbI));
if MOflag == 3 then (
Gmap = map(R,RS, (vars R)_{0..nR-1} | G))
else (
Gmap = map(RS,RS,(vars RS)_{0..nR-1} | RtoRS(G));
IinRS = RtoRS I;
RStoR = map(R,RS,(vars R) | matrix {toList(nG:0_R)}););
);
);
grabLowestDegree := () -> (
-- assumes: lowest degree pending list is already autosubducted.
-- this row reduces this list, placing all of the
-- entries back into Pending, but then appends the lowest
-- degree part into the basis.
e := lowestDegree();
if e <= maxdeg then (
if MOflag == 2 then (
numnewsagbi = #Pending#e;
appendToBasis matrix{Pending#e};
Pending#e = {};)
else (
m := rowReduce(matrix{Pending#e}, e);
Pending#e = {};
insertPending m;
e = lowestDegree();
appendToBasis matrix{Pending#e};
numnewsagbi = #Pending#e;
Pending#e = {};);
);
e);

gbI = gens gb I;
Gens = compress (Gens % I);
G = matrix(R, {{}});
Gensmaxdeg := (max degrees source Gens)_0;
Gens = compress submatrixBelowDegree(Gens, maxdeg+1);
insertPending Gens;
Pending#0 = {};
d = grabLowestDegree();  -- initializes G
if printlevel > 0 then (
<< "--- degree " << d << " ----" << endl;
<< numnewsagbi << " new generators" << endl;
);
d = d+1;
nloops = d;
isdone := false;
while nloops <= maxnloops and not isdone do (
nloops = nloops+1;
if printlevel > 0 then
<< "--- degree " << d << " ----" << endl;
gbJquo = gb(Jquo, DegreeLimit=>d);
mtemp := gens gbJquo;
spairs := submatrixByDegrees(split2(mtemp,RStoS mtemp),d);
if printlevel > 1 then << "spairs = " << transpose spairs << endl;
spairs = compress Gmap(spairs);
if Pending#d != {} then (
if MOflag == 3 then (newgens = matrix{Pending#d})
else (newgens = RtoRS(matrix{Pending#d}));
spairs = spairs | newgens;
Pending#d = {};);
if numgens source spairs > 0 then (
if MOflag == 3 then (
newguys = subductquo(spairs, Gmap, Jquo, I, d))
else (newguys = autosubductionquo(spairs));
stopcriteria := numgens source newguys)
else stopcriteria = 0;
if stopcriteria > 0 then (
if MOflag == 3 then (insertPending newguys)
else (insertPending RStoR newguys);
d = grabLowestDegree();
if printlevel > 0 then
<< numnewsagbi << " new generators" << endl;
)
else (
ngens := sum apply(toList Pending,i -> #i);
if ngens === 0 and gbDone gbJquo and
d>Gensmaxdeg then (
isdone = true;
if printlevel > 0 then (
<< "" << endl;
<< "********************************" << endl;
<< "**** SAGBI basis is FINITE! ****" << endl;
<< "********************************" << endl;
<< "" << endl;
);
);
);
d = d+1;
);
G)

--END TOP LEVEL--

