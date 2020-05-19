--- kludge to access "hasAttribute" and "getAttribute"
hasAttribute = value Core#"private dictionary"#"hasAttribute";
getAttribute = value Core#"private dictionary"#"getAttribute";

------------------------------------------------------------------------------
-- Constructing normal toric varieties
------------------------------------------------------------------------------
NormalToricVariety = new Type of Variety
NormalToricVariety.synonym = "normal toric variety"
NormalToricVariety.GlobalAssignHook = globalAssignFunction
NormalToricVariety.GlobalReleaseHook = globalReleaseFunction
expression NormalToricVariety := X -> if hasAttribute (X, ReverseDictionary) 
    then expression getAttribute (X, ReverseDictionary) else 
    new FunctionApplication from {normalToricVariety, (rays X, max X)}

normalToricVariety = method (TypicalValue => NormalToricVariety, 
    Options => {
    	CoefficientRing   => KK,
    	MinimalGenerators => false,
    	Variable          => getSymbol "x",	  
    	WeilToClass       => null
	}
    )
normalToricVariety (List, List) := opts -> (rayList, coneList) -> (
    coneList' := sort apply(coneList, sigma -> sort sigma);
    X := new NormalToricVariety from {
    	symbol rays  => rayList,
    	symbol max   => coneList',
    	symbol cache => new CacheTable
	};
    if opts.WeilToClass =!= null then X.cache.fromWDivToCl = opts.WeilToClass;
    X.cache.CoefficientRing = opts.CoefficientRing;
    X.cache.Variable = opts.Variable;
    X
    )
normalToricVariety Matrix := opts -> vertices -> (
    if ring vertices =!= ZZ then error "--expected an integer matrix";
    lifting := matrix {toList (numColumns vertices : 1_ZZ)} || vertices;
    H := fourierMotzkin lifting;
    if opts.MinimalGenerators == true then lifting = (fourierMotzkin H)#0;
    rayList := entries transpose ( -submatrix(H#0,{1..numRows vertices},));
    M := (transpose H#0) * lifting;
    coneList := apply(numColumns M, j -> select(toList(0..numRows M - 1),  
      	    i -> M_(i,j) == 0));
    normalToricVariety (rayList, coneList,  
    	WeilToClass     => opts.WeilToClass,
    	CoefficientRing => opts.CoefficientRing,
    	Variable        => opts.Variable
	)
    )

isWellDefined NormalToricVariety := Boolean => X -> (
    -- CHECK DATA STRUCTURE
    -- check keys
    K := keys X;
    expectedKeys := set {symbol rays, symbol max, symbol cache};
    if set K =!= expectedKeys then (
	if debugLevel > 0 then (
	    added := toList (K - expectedKeys);
	    missing := toList (expectedKeys - K);
	    if #added > 0 then 
	    << "-- unexpected key(s): " << toString added << endl;
	    if #missing > 0 then 
	    << "-- missing keys(s): " << toString missing << endl
	    );	 
    	return false
    	);
    -- check types
    if not instance (X.rays, List) then (
	if debugLevel > 0 then 
	    << "-- expected `rays' to be a list" << endl;
	return false
	);
    if not all (X.rays, r -> instance (r, List)) then (
	if debugLevel > 0 then 
	    << "-- expected `rays' to be a list of lists" << endl;
	return false
	);
    if not all (X.rays, r -> all (r, i -> instance(i, ZZ))) then (
	if debugLevel > 0 then 
  	    << "-- expected `rays' to be a list of lists of integers" << endl;
	return false
	); 
    rayList := rays X;
    d := # (rayList#0);
    if not all (X.rays, r -> #r === d) then (
	if debugLevel > 0 then 
	    << "-- expected `rays' to be a list of equal length lists" << endl;
	return false
	); 
    if not instance (X.max, List) then (
	if debugLevel > 0 then 
	    << "-- expected `max' to be a list" << endl;
	return false
	);
    if not all (X.max, sigma -> instance (sigma, List)) then (
	if debugLevel > 0 then 
	    << "-- expected `max' to be a list of lists" << endl;
	return false
	); 
    if not all (X.max, sigma -> all (sigma, i -> instance (i, ZZ))) then (
	if debugLevel > 0 then 
	    << "-- expected `max' to be a list of lists of integers" << endl;
	return false
	);            
    n := # rayList; 
    if not all (X.max, sigma -> all (sigma, i -> 0 <= i and i < n)) then (
	if debugLevel > 0 then 
	    << "-- expected `max' to correspond to subsets of rays" << endl;
	return false
	);        
    if not instance (X.cache, CacheTable) then (
    	if debugLevel > 0 then 
	    << "-- expected `X.cache' to be a CacheTable" << endl;
    	return false
	);    
    -- CHECK MATHEMATICAL STRUCTURE
    coneList := max X;
    -- check whether every ray appears in some maximal cone
    if set toList (0..n-1) =!= set flatten coneList then (
    	if debugLevel > 0 then 
      	    << "-- some ray does not appear in maximal cone" << endl;
    	return false
	);
    -- check whether the cones are maximal
    if coneList =!= unique coneList or 
    any (coneList, sigma -> any (coneList, 
	    tau -> sigma != tau and all(tau, i -> member(i, sigma))
	    )
	) 
    then (
    	if debugLevel > 0 then 
	    << "-- some cone is not maximal" << endl;
    	return false
	);    
    dualCones := new MutableHashTable;
    m := # max X;
    -- loop over all maximal cones
    for i to m-1 do (
	C := transpose matrix apply (coneList#i, j -> rayList#j);
    	H := fourierMotzkin C;
    	dualCones#i = H#0 | H#1 | -H#1;
    	(C',L) := fourierMotzkin H;
    	-- check whether the maximal cone is strongly convex
    	if L != 0 then (
      	    if debugLevel > 0 then (
		<< "-- not all maximal cones are strongly convex" << endl
		);
      	    return false
	    ); 
    	-- check whether the rays are the primitive generators of the cone
    	if set entries transpose C' =!= set entries transpose C then (
      	    if debugLevel > 0 then (
		<< "-- the rays are not the primitive generators" << endl
		);
      	    return false
	    )
	);
    -- check whether the intersection of each pair of maximal cones is a cone
    for i to m-2 do (
    	for j from i+1 to m-1 do (
      	    C := set apply (
		toList (set(coneList#i)*set(coneList#j)), k -> rayList#k
		);	       
      	    (C',L) := fourierMotzkin (dualCones#i | dualCones#j);
      	    if C =!= set entries transpose C' then (
		if debugLevel > 0 then (
	  	    << "-- intersection of cones is not a cone" << endl
		    );
		return false
		)
	    )
	);
    true);

affineSpace = method (
    Options => {
    	CoefficientRing => KK,
    	Variable        => getSymbol "x"
	}
    )
affineSpace ZZ := NormalToricVariety => opts -> d -> (
    if d < 1 then error "-- expected a positive integer";
    normalToricVariety (entries id_(ZZ^d), {toList(0..d-1)}, 
    	CoefficientRing => opts.CoefficientRing, 
	Variable        => opts.Variable
	)
    );

toricProjectiveSpace = method (
    Options => {
    	CoefficientRing => KK,
    	Variable        => getSymbol "x"
	}
    )
toricProjectiveSpace ZZ := NormalToricVariety => opts -> d -> (
    if d < 1 then error "-- expected a positive integer";
    rayList := {toList(d:-1)} | entries id_(ZZ^d);
    coneList := subsets (d+1,d);
    normalToricVariety (rayList, coneList,
    	CoefficientRing => opts.CoefficientRing, 
	Variable        => opts.Variable
	)
    );

weightedProjectiveSpace = method (
    Options => {
    	CoefficientRing => KK,
    	Variable        => getSymbol "x"
	}
    )
weightedProjectiveSpace List := NormalToricVariety => opts -> q -> (
    if #q < 2 then error "-- expected a list with at least two elements";
    if not all (q, i -> i > 0) then error "-- expected positive integers";
    d := #q-1;
    if not all (subsets (q,d), s -> gcd s === 1) then (
    	error ("--  the " | toString d | "-elements have a common factor")
	);
    rayList := entries kernelLLL matrix {q};
    coneList := subsets (d+1,d);
    normalToricVariety (rayList, coneList,
    	CoefficientRing => opts.CoefficientRing, 
	Variable        => opts.Variable
	)
    );

hirzebruchSurface = method (
    Options => {
    	CoefficientRing => KK,
    	Variable        => getSymbol "x"
	}
    )
hirzebruchSurface ZZ := NormalToricVariety => opts -> a -> (
    rayList := {{1,0},{0,1},{ -1,a},{0,-1}};
    coneList := {{0,1},{1,2},{2,3},{0,3}};
    W := matrix {{1,-a,1,0},{0,1,0,1}};
    normalToricVariety (rayList, coneList, 
    	CoefficientRing => opts.CoefficientRing, 
    	Variable        => opts.Variable,
    	WeilToClass     => W
	)
    );

NormalToricVariety ** NormalToricVariety := NormalToricVariety => (X,Y) -> (
    rayList1 := transpose matrix rays X;
    rayList2 := transpose matrix rays Y;
    rayList := entries transpose (rayList1 ++ rayList2);
    coneList1 := max X;
    coneList2 := max Y;
    n := #rays X;
    coneList2 = apply (coneList2, sigma -> apply (sigma, i -> i+n));
    coneList := flatten table (coneList1, coneList2, 
	(sigma, tau) -> sigma | tau
	);
    W1 := fromWDivToCl X;
    W2 := fromWDivToCl Y;
    normalToricVariety (rayList, coneList, 
    	CoefficientRing => coefficientRing ring X,
    	WeilToClass     => W1 ++ W2
	)
    );

NormalToricVariety ^** ZZ := NormalToricVariety => (X,n) -> (
    if n <= 0 then error "-- expected a positive integer";
    if n == 1 then return X
    else return X ** (X ^** (n-1))
    );

kleinschmidt = method (
    Options => {
    	CoefficientRing => KK,
    	Variable        => getSymbol "x"
	}
    )
kleinschmidt (ZZ, List) := NormalToricVariety => opts -> (d,a) -> (
    if d < 0 then error "-- expected a nonnegative integer";
    r := #a;
    s := d-r+1;
    e := entries id_(ZZ^d);
    if r >= d then error "-- list is too long"; 
    rayList := {sum (r, i -> -e#i)} | apply(r, i -> e#i);
    rayList = rayList | apply (s-1, j -> e#(r+j));
    rayList = rayList | {sum (r, i -> a#i*e#i) - sum (s-1, j -> e#(r+j))};
    L := toList (0..r+s);
    coneList := flatten table (toList (0..r), toList (r+1..r+s), 
    	(i,j) -> select(L, k -> i =!= k and j =!= k));
    deg := {{0,1}} | apply (r, i -> { -a#i,1}) | apply (s, j -> {1,0});
    normalToricVariety (rayList, coneList, 
    	CoefficientRing => opts.CoefficientRing, 
    	Variable        => opts.Variable,
    	WeilToClass     => transpose matrix deg
	)
    );

-- THIS FUNCTION IS NOT EXPORTED. By reading an auxiliary file, this function
-- creates a HashTable with the defining data for the low dimensional smooth
-- Fano toric varieties.
smoothFanoToricVarietiesFile := currentFileDirectory | "NormalToricVarieties/smoothFanoToricVarieties.txt"
smoothFanoToricVarietiesFile5 := currentFileDirectory | "NormalToricVarieties/smoothFanoToricVarieties5.txt"
smoothFanoToricVarietiesFile6 := currentFileDirectory | "NormalToricVarieties/smoothFanoToricVarieties6.txt"
getFano := memoize(d -> (
    	local fanoFile;
    	if d < 5 then fanoFile = smoothFanoToricVarietiesFile
    	else if d === 5 then fanoFile = smoothFanoToricVarietiesFile5
    	else if d === 6 then fanoFile = smoothFanoToricVarietiesFile6;
    	if notify then stderr << "--loading file " << fanoFile << endl;
    	hashTable apply( lines get fanoFile, x -> (
		x = value x;
		((x#0,x#1), drop (x,2)) 
		)
    	    )
	)
    );

smoothFanoToricVariety = method (
    Options => {
    	CoefficientRing => KK,
    	Variable        => getSymbol "x"
	}
    )
smoothFanoToricVariety (ZZ,ZZ) := NormalToricVariety => opts -> (d, i) -> (
    if d < 1 or i < 0 then 
    	error "-- expected positive dimension or nonnegative index";
    if d === 1 and i > 0 then 
    	error "-- there is only one smooth Fano toric curve";
    if d === 2 and i > 4 then 
    	error "-- there are only five smooth Fano toric surfaces";
    if d === 3 and i > 17 then 
    	error "-- there are only 18 smooth Fano toric 3-folds";
    if d === 4 and i > 123 then 
    	error "-- there are only 124 smooth Fano toric 4-folds";
    if d === 5 and i > 865 then 
    	error "-- there are only 866 smooth Fano toric 5-folds";
    if d === 6 and i > 7621 then 
    	error "-- there are only 7622 smooth Fano toric 6-folds";
    if d > 6 then 
    	error "-- database doesn't include varieties with dimension > 6";
    if i === 0 then return toricProjectiveSpace d;
    if d < 5 then (
    	s := (getFano (d))#(d,i);
    	return normalToricVariety (s#0, s#1, 
	    CoefficientRing => opts.CoefficientRing, 
	    Variable        => opts.Variable,
	    WeilToClass     => transpose matrix s#2
	    )
	);
    s = (getFano (d))#(d,i);
    normalToricVariety (s#0, s#1,
	CoefficientRing => opts.CoefficientRing, 
	Variable        => opts.Variable
	)
    );

-- this function interfaces with the Polyhedra package
normalToricVariety Fan := opts -> F -> (
    normalToricVariety (entries transpose rays F, maxCones F,
    	CoefficientRing => opts.CoefficientRing,
	Variable        => opts.Variable,	
    	WeilToClass     => opts.WeilToClass 
	)
    );
------------------------------------------------------------------------------
-- this function interfaces with the Polyhedra package
normalToricVariety Polyhedron := opts -> (cacheValue symbol variety) (P -> (
	Q := P;
	if not isFullDimensional Q then (
	    d := dim Q;
	    C := cone Q;
	    -- restrict to the linear subspace spanned by the polytope
	    H := transpose facets C % transpose hyperplanes C;
	    Q = polyhedronFromHData (transpose H^{1..d}, transpose H^{0});
	    );
	normalToricVariety(normalFan Q,
	    CoefficientRing => opts.CoefficientRing,
	    Variable        => opts.Variable,       
	    WeilToClass     => opts.WeilToClass
	    ) 
	)
    );

------------------------------------------------------------------------------
-- Basic properties and invariants
------------------------------------------------------------------------------
-- The method 'rays' is defined in 'Polyhedra'
rays NormalToricVariety := List => X -> X.rays
max  NormalToricVariety := List => X -> X.max
dim NormalToricVariety := ZZ => (cacheValue symbol dim) (X -> #(rays X)#0)

isDegenerate = method ()
isDegenerate NormalToricVariety := Boolean => (
    cacheValue symbol isDegenerate) (
    X -> kernel matrix rays X != 0
    )

isSimplicial NormalToricVariety := Boolean => (
    cacheValue symbol isSimplicial) (
    X -> (
    	rayGenMatrix := transpose matrix rays X;
    	all (max X, sigma -> #sigma == rank rayGenMatrix_sigma) 
	)
    );

isSmooth NormalToricVariety := Boolean => (
    cacheValue symbol isSmooth) (X -> (
    	rayGenMatrix := transpose matrix rays X;
    	b := all(max X, sigma -> 
	    #sigma === rank rayGenMatrix_sigma and 
	    1 == minors(#sigma, rayGenMatrix_sigma) 
	    );
	if b === true then X.cache.isSimplicial = true;
	b 
	)
    );

isComplete NormalToricVariety := Boolean => (
    cacheValue symbol isComplete) (
    X -> (
    	-- there is only one complete normal toric variety of dimension one
    	if dim X === 1 then return (set rays X === set {{ -1},{1}});
    	if orbits (X, 1) == {} then return false;	
    	-- check to see that every torus-invariant curve is projective
    	for C in orbits (X, 1) do (
      	    m := 0;
      	    for sigma in max X when m < 2 do 
		if all (C, i -> member (i,sigma)) then m = m+1;
      	    if m < 2 then (
		if debugLevel > 0 then 
		    << "the curve " << toString C << " is not projective" << endl;
		return false
		)
	    );
    	true 
	)
    )

isProjective = method ()
isProjective NormalToricVariety := Boolean => (
    cacheValue symbol isProjective) (
    X -> (
    	if not isComplete X then return false;
    	-- projectivity is checked using Gale duality; see Theorem~V.4.8 in
    	-- Ewald's "Combinatorial convexity and algebraic geometry"
    	clX := classGroup X;
	if not isFreeModule clX then (
	    smithMatrix := presentation clX;
	    torsionlessCoord := select (rank target smithMatrix,
		i -> smithMatrix^{i} == 0
		)
	    )
	else torsionlessCoord = toList (0.. rank clX - 1);
	galeDualMatrix := matrix (fromWDivToCl X)^torsionlessCoord;
	outerNormals := matrix {
	    for sigma in max X list (
		sigma' := select(# rays X, i -> not member (i, sigma));
		dualCone := (fourierMotzkin galeDualMatrix_sigma');
		dualCone#0 | dualCone#1 | - dualCone#1
		)
	    };
	coneGens := fourierMotzkin outerNormals;
	coneGens = (coneGens#0 | coneGens#1);
	if coneGens == 0 then return false;
	0 == (fromPicToCl X)^torsionlessCoord % coneGens 
	)
    );

-- this function interfaces with the Polyhedra package
fan NormalToricVariety := Fan => X -> (
    rayMatrix := promote (matrix transpose rays X, QQ); 
    fan(rayMatrix, max X) 
    );

-- This method is not exported
facesOfCone = method ()
-- Given a matrix 'R' whose columns are the rays of a strongly convex cone and
-- a list 's' whose entries label the rays, the method makes a HashTable whose
-- keys label the faces and values give the codimension.
facesOfCone (Matrix, List) := HashTable => (R, s) -> (
    H := fourierMotzkin R;
    H = H#0 | H#1; 
    incidenceMatrix := (transpose H) * R;
    h := numColumns H;  
    hyperplaneTable := new MutableHashTable from apply(h, i -> {{i}, 
	    select(s, j -> incidenceMatrix_(i, position(s, l -> l === j)) === 0
	    	)
	    }
    	);
    faceTable := new MutableHashTable from 
        apply (values hyperplaneTable, f -> {f,1});
    faceTable#s = 0;
    d := rank R;
    Q := apply(h, i -> {i});
    while Q =!= {} do (
    	q := first Q;
    	Q = drop (Q,1);
    	for i from 0 to h-1 do if not member (i,q) then (
      	    t := select (hyperplaneTable#q, j -> member (j,hyperplaneTable#{i}));
      	    k := sort (q | {i});
      	    if t =!= {} and not hyperplaneTable#?k and not faceTable#?t then (
		hyperplaneTable#k = t;
		faceTable#t = d - rank R_(positions (s, i -> member (i,t)));
		Q = Q | {k}
		)
	    )
	);
    d = numRows R - d;
    new HashTable from apply(keys faceTable, f -> {f,d+faceTable#f}));
-- Given a list 'L' whose entries label rays in a simplicial cone and an
-- integer 'i' which is the codimension of the cone, this method makes a
-- HashTable whose keys label the faces and values give the codimension, In
-- the simplicial case, we don't actually need the rays of the cone.
facesOfCone (List,ZZ) := (L,i) -> new HashTable from 
    apply (drop (subsets (L), 1), s -> {s,#L-#s+i});

orbits = method ()   
orbits NormalToricVariety := HashTable => (
    cacheValue symbol orbits) (
    X -> (
    	hTable := new HashTable;
    	raysMatrix := transpose matrix rays X; 
    	d := dim X;
    	if isSimplicial X and not isDegenerate X then (
      	    for s in max X do (
		hTable = merge(hTable, facesOfCone (s, d - rank raysMatrix_s), 
		    (p,q) -> p
		    )
		)
	    )
    	else for s in max X do (
	    hTable = merge(hTable, facesOfCone (raysMatrix_s,s), (p,q) -> p));
    	O := new MutableHashTable from apply (d+1, i -> {i,{}});
    	for k in keys hTable do O#(hTable#k) = O#(hTable#k) | {k};
    	new HashTable from apply (keys O, k -> {k, sort O#k}) | {{d,{{}}}} 
	)
    );
orbits (NormalToricVariety, ZZ) := List => (X,i) -> (
    if i < 0 or i > dim X then 
    	error "-- expected a nonnegative integer that is at most the dimension";
    O := orbits X;
    O#i
    )



------------------------------------------------------------------------------
-- resolution of singularities
------------------------------------------------------------------------------

-- THIS METHOD IS NOT EXPORTED.  Given a normal toric variety 'X', a maximal
-- cone indexed by the list 's', and a weight vector encoded by the integer
-- list 'w', this method makes a new normal toric variety in which the maximal
-- cone corresponding to 's' has been replace by the regular subdivison
-- associated to the weight vector 'w'.  In particular, the entries in 'w' are
-- used as heights to lift the maximal cone corresponding to 's' into the next
-- dimension.  The lower faces (those for which the normal vector has negative
-- last coordinate) form a polyhedral complex and the regular subdivision is
-- the image of this complex.  For a generic weight vector, this subdivision
-- will be a triangulation.

regularSubdivisionLocal = method (TypicalValue => NormalToricVariety)
regularSubdivisionLocal (NormalToricVariety, List, List) := (X,s,w) -> (
    coneList := max X;
    rayList := rays X;
    rayMatrix := transpose matrix rayList;
    wtg := i -> if member(i,s) then w#(position (s, j -> i === j)) else 1;    
    for sigma in coneList do (
      	if #sigma === rank rayMatrix_sigma then continue;
      	w' := sigma / wtg;
      	if all (w', i -> i === 1) then continue;
      	C := rayMatrix_sigma || matrix {w'};
      	C' := fourierMotzkin C;
      	H := matrix select (entries transpose C'#0, r -> last r < 0);
      	if C'#1 !=0 then (  
  	    H' := select (entries transpose C'#1, r -> last r != 0);
  	    if #H' > 0 then H = H || matrix apply (H', 
	  	r -> if last r > 0 then -r else r)
	    );
      	inc := H * C;
      	coneList' := apply (apply (numRows inc, i -> 
		select (numColumns inc, j -> inc_(i,j) === 0)
		), 
	    t -> sigma_t
	    );
      	k := position (coneList, tau -> tau === sigma);
      	if all (coneList', tau -> #tau == rank rayMatrix_sigma) then (
	    coneList = drop (coneList,{k,k}) | coneList') 
	);
    if coneList == max X then return X;
    Y := normalToricVariety (rayList, coneList);
    Y.cache.Weights = apply (#rayList, i -> wtg i);
    Y 
    );    

makeSimplicial = method (
    TypicalValue => NormalToricVariety,
    Options => {Strategy => 0}
    )
makeSimplicial NormalToricVariety := opts -> X -> (
    Y := X;
    while true do (
	coneList := max Y;
	rayMatrix := transpose matrix rays Y;
	k := position (coneList, sigma -> #sigma =!= rank rayMatrix_sigma);
	if k === null then break
	else (
	    s := coneList#k;
	    if opts.Strategy === 1 then (
      		c := 1 + dim Y - rank rayMatrix_s;
      		i := 0;
      		edges := select (orbits (Y,c), r -> all(r, j -> member (j,s)));
      		while #select (edges, r -> not member (s#i,r)) === 1 do i = i+1;
      		Y = toricBlowup ({s#i},Y) )
    	    else (
      	    	s = coneList#k;
      	    	n := #s;
      	    	m := (n // 10) + 1;
      	    	w := apply (n, i -> random (2,100*m));
      	    	Y = regularSubdivisionLocal (Y,s,w) )));
    Y 
    );

-- THIS METHOD IS NOT EXPORTED.  Given a list 'w' of integers, this method
-- returns the associated primitive vector; it divides the entries by their
-- greatest common denominator
makePrimitive = method()
makePrimitive List := List => w -> (
   g := gcd w;
   if g === 1 then return w;
   apply(w, i -> i // g) 
   );

toricBlowup = method ()
toricBlowup (List, NormalToricVariety, List) := NormalToricVariety => (s, X, v) -> (
    coneList := max X;
    starIndex := positions (coneList, t -> all (s, i -> member (i,t)));
    star := coneList_starIndex;
    rayMatrix := transpose matrix rays X;
    d := dim X;
    clStar := {};
    for t in star do (
    	c := 1 + d - rank rayMatrix_t;
    	clStar = clStar | select (orbits(X,c), r -> all (r, j -> member(j,t)))
	);
    clStar = unique clStar;
    n := #rays X;
    coneList = coneList_(select (#coneList, i -> not member (i, starIndex)));
    if #s === 1 then (
    	coneList' := for t in clStar list (
      	    if member (s#0,t) then continue
      	    else sort (t | s)
	    );
    	return normalToricVariety (rays X, coneList | coneList') 
	);
    coneList' = for t in clStar list (
	if all (s, i -> member (i,t)) then continue
	else t | {n}
	);
    normalToricVariety (rays X | {v}, coneList | coneList') 
    );

toricBlowup (List, NormalToricVariety) := NormalToricVariety => (s,X) -> (
    v := makePrimitive sum ((rays X)_s);
    toricBlowup (s,X,v) 
    );

makeSmooth = method(
    TypicalValue => NormalToricVariety,
    Options => {Strategy => 0}
    )
makeSmooth NormalToricVariety := opts -> X -> (
    Y := X;
    while true do (
      	coneList := max Y;
      	rayMatrix := transpose matrix rays Y;
      	k := position (coneList, 
	    tau -> #tau =!= rank rayMatrix_tau or 1 != minors (#tau, rayMatrix_tau));
      	if k === null then break;
      	sigma := coneList#k;
      	tau := first select (select (subsets (sigma), t -> #t > 1), 
  	    f -> #f =!= rank rayMatrix_f or 1 != minors (#f,rayMatrix_f));
      	H := hilbertBasis (posHull rayMatrix_tau);
      	H = H / (v -> flatten entries v);
      	--time H := entries transpose hilbertBasis(Vt,"notused");
      	w := select(H, h -> not member (h, (rays Y)_sigma));
      	if w === {} then Y = makeSimplicial (Y, Strategy => opts.Strategy)
      	else Y = toricBlowup (tau,Y, first w)
	);
    Y 
    );
