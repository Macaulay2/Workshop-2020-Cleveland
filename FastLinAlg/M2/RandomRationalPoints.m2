-- -*- coding: utf-8 -*-
newPackage(
        "RandomRationalPoints",
    	Version => "1.2",
    	Date => "May 21, 2020",
    	Authors => {
	     {Name => "Sankhaneel Bisui", Email => "sbisu@tulane.edu", HomePage=>"https://sites.google.com/view/sankhaneelbisui/home"},
	     {Name=> "Thai Nguyen", Email =>"tnguyen11@tulane.edu", HomePage=>"https://sites.google.com/view/thainguyenmath "},
	     {Name=>"Karl Schwede", Email=>"schwede@math.utah.edu", HomePage=>"https://www.math.utah.edu/~schwede/" },
	     {Name => "Sarasij Maitra", Email => "sm3vg@virginia.edu", HomePage => "https://people.virginia.edu~sm3vg"},
	     {Name => "Zhan Jiang", Email => "zoeng@umich.edu", HomePage => "http://www-personal.umich.edu/~zoeng/"}
	     },
    	Headline => "A Package To Compute A Random Point In A Given Variety",
		DebuggingMode => true, 
		Reload=>true,
		AuxiliaryFiles => false -- set to true if package comes with auxiliary files
    	)

-- Any symbols or functions that the user is to have access to
-- must be placed in one of the following two lists
export {
	"genericProjection", 
	"projectionToHypersurface",
	"randomCoordinateChange",
    "randomPointViaLinearIntersection",
    "randomPointViaGenericProjection",
	"randomPoints", 
	"extendingIdealByNonVanishingMinor",
	"findANonZeroMinor",
	"mtSearchPoints",
	"MyOption",
	"NumPointsToCheck", 
	"Codimension",
	"MaxCoordinatesToReplace",
    "Replacement",
    "Simple",
    "Full", 
	"BruteForce", --a valid value for [RandomPoint, Strategy]
    "GenericProjection",  --a valid value for [RandomPoint, Strategy]
    "HybridProjectionIntersection", --a valid value for [RandomPoint, Strategy]
    "LinearIntersection",  --a valid value for [RandomPoint, Strategy]
    "ModifiedBruteForce",  --a valid value for [RandomPoint, Strategy]
	"ProjectionAttempts", --used in the GenericProjection strategy
    "IntersectionAttempts", --used in the LinearIntersection strategy
    "ExtendField", --used in GenericProjection and LinearIntersection strategy
    "checkRandomPoint",
    "PointCheckAttempts",
    "ReturnAllResults", -- used in the multi-thread search function mtSearchPoints
    "NumTrials", -- used in the multi-thread search function mtSearchPoints
    "NumThreadsToUse" -- used in the multi-thread search function mtSearchPoints
    }
exportMutable {}

needsPackage "SwitchingFields";
needsPackage "MinimalPrimes";
installMinprimes();

optRandomPoints := {
    Strategy=>BruteForce, 
    Homogeneous => true,  
    MaxCoordinatesToReplace => 0, 
    Codimension => null,
    IntersectionAttempts => 20,
    ProjectionAttempts => 20,
    ExtendField => false,
    PointCheckAttempts => 100
};

pointToIdeal = method(Options =>{Homogeneous => false});

pointToIdeal(Ring, List) := opts -> (R1, L1) -> (
        if (opts.Homogeneous == false) then (
        genList := gens R1;
        return ideal( apply(#genList, i->genList#i - (sub(L1#i, R1)) ));
        );
);

idealToPoint = method(Options => {Homogeneous => false});

idealToPoint(Ideal) := opts -> (I1) -> (
        if (opts.Homogeneous == false) then (
            genList := gens ring I1;
            return apply(genList, s -> s%I1);
        )
);

--this function was taken directly from an internal function in RationalPoints.m2 by Nathaniel Stapleton
fieldElements = (k) -> (
     J := ideal k;
     p := char k;
     els := {};
     galoisfield := class k === GaloisField;
     if galoisfield then (
          x := k.PrimitiveElement; --sometimes k_0 is not the primitive element ie. GF 9
          e := 1;
          b := 0;
          els = els|{0};
          while b != 1 do (
               b = x^e;
               e = e+1;
               els = els | {b};
               );
          );
     if not galoisfield and char ring J != 0 then (
     	  d := (degree((flatten entries gens J)_0))_0;
     	  a := (gens k)_0;
          coeffs := toList ((set toList (0..p-1)) ^** (d));
     	  for i to # coeffs - 1 do (
               x := 0;
               for j to d-1 do (
               	    x = x+coeffs_i_j*a^j;
               	    );
               els = els | {x};
               );
          );
     if not galoisfield and char ring J == 0 then els = toList (0..p-1);
     return els;
     );



  --Function to create a random point
createRandomPoints= method(TypicalValue => List, Options => {})
createRandomPoints(Ideal):=List => opts->(I1) ->(
    noVar := #generators ring I1;
    K:=coefficientRing ring (I1);
    L:=toList apply(noVar, i ->random(K));
    return L )


randomCoordinateChange = method(Options=>{Homogeneous=>true, Replacement=>Full, MaxCoordinatesToReplace => infinity});

randomCoordinateChange(Ring) := opts -> (R1) -> (
    if (debugLevel > 0) then print "randomCoordinateChange: starting.";
    local phi;
    if not class R1 === PolynomialRing then error "randomCoordinateChange: expected an ideal in a polynomial ring";
    myMon := monoid R1;
    S1 := (coefficientRing R1)(myMon);
    genList := random gens R1;
    genCount := #(genList);
    local replacementFunction;
    if (opts.Replacement == Simple) then (
        if opts.Homogeneous then (
            replacementFunction = trm -> (v2 := (random(0, R1))*trm + (random(0, R1))*(genList#(random(#genList))); if (v2 == 0) then trm else v2);) 
        else (
            replacementFunction = trm -> ((random(0, R1))*trm + random(0, R1));
        );
    )
    else if (opts.Replacement == Full) then (
        if opts.Homogeneous then (
            replacementFunction = trm -> random(1, R1);)
        else (
            replacementFunction = trm -> random(1, R1)+random(0, R1);
        );
    );
    genList = random apply(genCount, t -> if (t < opts.MaxCoordinatesToReplace) then replacementFunction(genList#t) else genList#t);
    phi = map(R1, S1, genList);
    --if it's working, great, otherwise recurse
    if (rank jacobian matrix phi >= genCount) then return phi else return randomCoordinateChange(R1, opts);

-*    if (opts.MaxCoordinatesToReplace >= genCount) then (
        if (opts.Homogeneous) then (
            phi = map(R1, S1, apply(gens R1, t -> random(1, R1)));
        )
        else(
            phi = map(R1, S1, apply(gens R1, t -> random(1, R1)+random(0, R1)));
        );
    )
    else( --if we only want to really change some (MaxCoordinatesToReplace) of the variables, and randomize the others
    
    if (opts.Homogeneous) then (
    --			genList = random apply(#(genList), t -> (if (t < opts.MaxCoordinatesToReplace) then random(1, R1) else genList#t) );
        genList = random apply(#(genList), 
            t -> (if (t < opts.MaxCoordinatesToReplace) then ((random(0, R1))*(genList#t) + (random(0, R1))*(genList#(random(#genList)))) else genList#t) 
        );
    )
    else(
    genList = random apply(#(genList), t -> (if (t < opts.MaxCoordinatesToReplace) then random(1, R1)+random(0, R1) else genList#t	) );
    );
    phi = map(R1, S1, genList);
    );
    return phi;*-
);

genericProjection = method(Options =>{Homogeneous => true, Replacement=>Simple, MaxCoordinatesToReplace => infinity});

genericProjection(Ideal) := opts -> (I1) -> (
        R1 := ring I1;
        psi := randomCoordinateChange(R1, opts);
        S1 := source psi;
        I2 := psi^-1(I1);
        kk:=coefficientRing R1;
        local Re;
        local Rs;
        Re=kk(monoid[apply(dim S1,i->S1_i),MonomialOrder => Eliminate 1]);
        rs:=(entries selectInSubring(1,vars Re))_0;
        Rs=kk(monoid[rs]);
        f:=ideal substitute(selectInSubring(1, generators gb substitute(I2,Re)),Rs);
        phi := map(S1, Rs);
        return(psi*phi, f);
);

genericProjection(ZZ, Ideal) := opts -> (n1, I1) -> (
        R1 := ring I1;
        psi := randomCoordinateChange(R1, opts);
        S1 := source psi;
        I2 := psi^-1(I1);
        kk:=coefficientRing R1;
        local Re;
        local Rs;
        Re=kk(monoid[apply(dim S1,i->S1_i),MonomialOrder => Eliminate n1]);
        rs:=(entries selectInSubring(1,vars Re))_0;
        Rs=kk(monoid[rs]);
        f:=ideal substitute(selectInSubring(1, generators gb substitute(I2,Re)),Rs);
        phi := map(S1, Rs);
        return(psi*phi, f);
);

projectionToHypersurface = method(Options =>{Homogeneous => true, Replacement=>Simple, MaxCoordinatesToReplace => infinity, Codimension => null});

projectionToHypersurface(Ideal) := opts -> (I1) -> (
        local c1;
        if (opts.Codimension === null) then (
        c1 = codim I1;
        ) else (c1 = opts.Codimension);
        local curMap;
        return genericProjection(c1-1, I1, Homogeneous => opts.Homogeneous, MaxCoordinatesToReplace => opts.MaxCoordinatesToReplace);
);

-*
projectionToHypersurface(Ideal) := opts -> (I1) -> (
	local c1;
	if (opts.Codimension === null) then (
		c1 = codim I1;
	) else (c1 = opts.Codimension);
	local curMap;
	tempList := genericProjection(I1, Homogeneous => opts.Homogeneous, MaxCoordinatesToReplace => opts.MaxCoordinatesToReplace);
	assert(target (tempList#0) === ring I1);
	if (c1 == 2) then (
		return tempList; --if we are done, stop
	);
	assert(source (tempList#0) === ring (tempList#1));
	--otherwise recurse
	tempList2 := projectionToHypersurface(tempList#1, Hoxmogeneous => opts.Homogeneous, MaxCoordinatesToReplace => opts.MaxCoordinatesToReplace, Codimension=>c1-1);
	assert(target(tempList2#0) === ring (tempList#1));
	return ((tempList#0)*(tempList2#0), tempList2#1);
);
*-

--this function just switches one strategy in an option table for another
switchStrategy := (opts, newStrat) -> (
    tempHashTable := new MutableHashTable from opts;
    tempHashTable#Strategy = newStrat;
    return new OptionTable from tempHashTable;
);


--Function to check if random point is in the variety by intersecting with a linear space
randomPointViaLinearIntersection = method(Options => optRandomPoints);
randomPointViaLinearIntersection(Ideal) := opts -> (I1) -> (
    c1 := opts.Codimension;
    if (c1 === null) then (c1 = codim I1); --don't compute it if we already know it.
    R1 := ring I1;
    local linearSpace;
    i := 0;
    j := 0 ;
    local finalPoint;
    local ptList; local newPtList;
    local phi;
    local myDeg;
    local m2;
    --1/0;
    while(i < opts.IntersectionAttempts) do ( 
        linearSpace = ideal apply((dim R1) - c1, i -> random(1, R1) + random(0, R1));
        J0 := linearSpace + I1;
        if (dim J0 == 0) then (
            ptList = random decompose(J0);
            j = 0;
            while (j < #ptList) do (
                myDeg = degree(ptList#j);
                if (myDeg == 1) then (
                    finalPoint = apply(idealToPoint(ptList#j), s -> sub(s, R1));
                    return finalPoint;
                )
                else if (opts.ExtendField == true) then (
                    if (debugLevel > 0) then print "randomPointViaLinearIntersection:  extending the field.";
                    phi = (extendFieldByDegree(myDeg, R1))#1;
                    m2 = phi(ptList#j);
                    newPtList = random decompose(m2); --make sure we are picking points randomly from this decomposition
--                    1/0;
                    if (#newPtList > 0) then ( 
                        finalPoint =  apply(idealToPoint(newPtList#0), s -> sub(s, target phi));
                        if (opts.Homogeneous) then ( --only return point in the homogeneous case if its not the origin
                            if (any(finalPoint, t -> t != 0)) then return finalPoint;
                        )
                        else(
                            return finalPoint;
                        );
                    ); 
                );
                j = j+1;
            );
        );
        if (debugLevel > 0) then print "randomPointViaLinearIntersection:  failed, looping and trying a new linear space.";
        i = i+1;
    );
    return {};
);


randomPointViaGenericProjection = method(Options => optRandomPoints);
randomPointViaGenericProjection(Ideal) := opts -> (I1) -> (
    flag := true;
    local phi;
    local I0;
    local J0;
    local pt;
    local ptList;
    local j;
    local finalPoint;
    local newPtList;
    local phi;
    local myDeg;
    local m2;
    R1 := ring I1;  
    i := 0;
    while(flag) and (i < opts.ProjectionAttempts) do (
        (phi, I0) = projectionToHypersurface(I1, Homogeneous=>opts.Homogeneous, MaxCoordinatesToReplace => opts.MaxCoordinatesToReplace, Codimension => opts.Codimension);
        if (codim I0 == 1) then (
            if (opts.Strategy == GenericProjection) then (
                pt = randomPoints(I0, switchStrategy(opts, BruteForce)))
            else if (opts.Strategy == HybridProjectionIntersection) then (
                pt = randomPoints(I0, switchStrategy(opts, LinearIntersection))
            ); --find a point on the generic projection (differently, depending on strategy)
            if (not pt === {}) then (
                J0 = I1 + sub(ideal apply(dim source phi, i -> (first entries matrix phi)#i - pt#i), target phi); --lift the point to the original locus
                if dim(J0) == 0 then( --hopefully the preimage is made of points
                    ptList = random decompose(J0);
                    j = 0;
                    while (j < #ptList) do (
                        myDeg = degree (ptList#j);
                        --print myDeg;
                        if (myDeg == 1) then (
                            finalPoint = apply(idealToPoint(ptList#j), s -> sub(s, coefficientRing ring I1));
                            if (opts.Homogeneous) then( 
                                if (any(finalPoint, t -> t != 0)) then return finalPoint;
                            )
                            else(
                                return finalPoint;
                            );
                        )                        
                        else if (opts.ExtendField == true) then (
                            if (debugLevel > 0) then print "randomPointViaGenericProjection:  extending the field.";
                            phi = (extendFieldByDegree(myDeg, R1))#1;
                            m2 = phi(ptList#j);
                            newPtList = random decompose(m2);
                            if (#newPtList > 0) then ( 
                                finalPoint =  apply(idealToPoint(newPtList#0), s -> sub(s, target phi));
                                return finalPoint
                            ); 
                        );
                        j = j+1;
                    )
                )
            );
        );
        if (debugLevel >0) then print "randomPointViaGenericProjection: That didn't work, trying again...";
        i = i+1;
    );
    return {};
);

checkRandomPoint =(I1)->(
    genList:= first entries gens I1;
	K:=coefficientRing ring I1;
    point:=randomPoints(ring I1);
	eval:= map(K,ring I1,point);
	j:=0;
	while(j< #genList) do (
        tempEval:=eval(genList_j);
        if not (tempEval==0) then return {};
        j=j+1
    );
    if (tempEval ==0) then return point else return {};
)

randomPoints = method( Options=>optRandomPoints);

randomPoints(Ring) := opts -> (R1) -> (
    if (class R1 === QuotientRing) then return randomPoints(ideal R1, opts); --if we take a polynomial ring
    if (class R1 === PolynomialRing) then (
        noVar := #generators R1;
        K:=coefficientRing R1;
        L:=toList apply(noVar, i ->random(K));
        if (opts.Homogeneous == true) then if (all(L, i->i==0)) then return randomPoints(R1, opts);
        return L
    );
    error "(randomPoints, Ring):  Only implemented for QuotientRing and PolynomialRing.";
);  



randomPoints(Ideal):=opts->(I1)->(
    local apoint;
    local outpt;
    local eval;
    K:=coefficientRing ring I1;
    local j;
    local i;
    local flag;
    --if they give us an ideal of a quotient ring, then 
    if (class ring I1 === QuotientRing) then return randomPoints(sub(I1, ambient ring I1) + ideal ring I1, opts);
    if (not class ring I1 === PolynomialRing) then error "randomPoints: must be an ideal in a polynomial ring or a quotient thereof";
    if (opts.Strategy == BruteForce) then (
    	j=0;
		while( j<opts.PointCheckAttempts) do (
			apoint=checkRandomPoint(I1);
			if not (apoint==={} ) then return apoint; 
			j=j+1;
		);
		return {};
	)
    else if (opts.Strategy == ModifiedBruteForce) then (
        j = 0;
        genList := first entries gens I1;
        while (j < opts.PointCheckAttempts) do (
            i=0;
            flag = true;
	        while(i< #genList) do (
                apoint=randomPoints(ring I1, opts);
                eval= map(K,ring I1,apoint);
                outpt=eval(genList_i);
                if not (outpt==0) then (flag = false; break);
                i=i+1
            );
            if (flag == true) then return apoint;
            j = j+1;
        );
    )
	else if (opts.Strategy == GenericProjection) then (
		return randomPointViaGenericProjection(I1, opts)
	)
    else if (opts.Strategy == LinearIntersection) then (
        return randomPointViaLinearIntersection(I1, opts)
    )
    else if (opts.Strategy == HybridProjectionIntersection) then (
        return randomPointViaLinearIntersection(I1, opts)
    )
    else (
        error "randomPoints:  Not a valid Strategy"
    )
);

randomPoints(ZZ,Ideal):=opts->(n1,I1)->(
    --todo:  The generic projection in particular, would be able to do this much better, without a loop.
        i:=0;
        local apoint;
        local L;
        L= {};
        while(i < n1 ) do ( 
            apoint=randomPoints(I1, opts);
            L = join(L,{apoint});
            i=i+1;
    );  
          return L;
);

findANonZeroMinor = method(Options => optRandomPoints);

findANonZeroMinor(ZZ, Matrix, Ideal) := opts -> (n,M,I)->(
    local P;
    local kk; 
    local R;
    local phi;
    local N; local N1; local N2; local N1new; local N2new;
    local J; local Mcolumnextract; local Mrowextract;
    R = ring I;
    kk = coefficientRing R;
    P = randomPoints(I, opts);
    if (P == {}) then  error "Couldn't find a point. Try Changing Strategy.";
    phi =  map(kk,R,sub(matrix{P},kk));
    N = mutableMatrix phi(M);
    rk := rank(N);
    if (rk < n) then return "Please try again";
    N1 = (columnRankProfile(N));
    Mcolumnextract = M_N1;
    M11 := mutableMatrix phi(Mcolumnextract);
    N2 = (rowRankProfile(M11));
    N1rand := random(N1);
    N1new = {};
    for i from  0 to n-1 do(
	N1new = join(N1new, {N1rand#i});
    );
    M3 := mutableMatrix phi(M_N1new);
    if (rank(M3)<n) then error "hoyni";
    N2 = random(rowRankProfile(M3));
    N2new = {};
    for i from 0 to n-1 do(
        N2new = join(N2new, {N2#i});
    );
    Mspecificrowextract := (M_N1new)^N2new;
    return (P, N1, N2, Mspecificrowextract);	
);

extendingIdealByNonVanishingMinor = method(Options=>optRandomPoints)
extendingIdealByNonVanishingMinor(ZZ,Matrix,Ideal):= opts -> (n, M, I) -> (
 -*   local P;
    local kk; 
    local R;
    local phi;
    local N; local N1; local N2; local N1new; local N2new;
    local J; local Mcolumnextract; local Mrowextract;
    R = ring I;
    kk = coefficientRing R;
    P = randomPoints(I);
    if (P == {}) 
    then error "No Point Found"
    else (
        phi =  map(kk,R,sub(matrix{P},kk));
        N = mutableMatrix phi(M);
        rk := rank(N);
        if (rk < n) then return I;
        N1 = random(columnRankProfile(N));
	    N1new = {};
	    for i from  0 to n-1 do(
	    N1new = join(N1new, {N1#i});
        );
	    Mcolumnextract = M_N1new;
        M3 := mutableMatrix phi(Mcolumnextract);
        if (rank(M3)<n) then error "..";
        N2 = random(rowRankProfile(M3);
        N2new = {};
        for i from 0 to n-1 do(
            N2new = join(N2new, {N2#i});
        );
        Mrowextract = Mcolumnextract^N2new;
 *-   
    local O;  local Ifin;
    O = findANonZeroMinor(n,M,I,opts); 
    L1 := ideal (det(O#3));
    Ifin = I + L1;
    return Ifin;
);



mtSearchPoints = method(TypicalValue => List, Options => {NumThreadsToUse => 4, NumTrials => 2, PointCheckAttempts => 4000, ReturnAllResults => false}); -- UsePregeneratedList => false
mtSearchPoints(Ideal) := List => opts -> (I) -> (
    genList := first entries gens I;
    R := ring I;
    K := coefficientRing R;
    n := #gens R;
    
    local taskList;
    local found;
    local resultList;
    
--    if (opts.UsePregeneratedList)
--    then (
--        randomPointsList := apply(opts.NumPoints * opts.NumThreadsToUse, (i)->(return getAPoint(n, K);));
--        taskList = apply(opts.NumThreadsToUse, (i)->(return createTask(modifiedSearchPoints, (take(randomPointsList, {i * opts.NumPoints, (i + 1) * opts.NumPoints - 1}), R, genList));));)
--    else (
--        taskList = apply(opts.NumThreadsToUse, (i)->(return createTask(searchPoints, (opts.NumPoints, R, genList));)););
    local numPointsToCheck;
    numPointsToCheck = floor(opts.PointCheckAttempts / opts.NumThreadsToUse); 
    
    local totalResultList;
    totalResultList = new MutableList;
    
--    if opts.NumThreadsToUse > allowableThreads
--    then error "mtSearch: Not enough allowed threads to use";
    
    for i from 1 to opts.NumTrials do
     (
    	 taskList := apply(opts.NumThreadsToUse, (i)->(return createTask(searchPoints, (numPointsToCheck, R, genList));));
     
         apply(taskList, t -> schedule t);
    	 while true do (
             nanosleep 100000000;--this should be replaced by a usleep or nanosleep command.
             if (all(taskList, t -> isReady(t))) then break;
             );
        resultList = apply(taskList, t -> taskResult(t));
	if any(resultList, (l) -> (#l>0))
	then if not opts.ReturnAllResults
	     then (
		 j := 0;
		 while #(resultList#j) == 0 do j = j + 1;
		 return resultList#j;
		 )
	     else (
		 for item in resultList do
		 if #item > 0
		 then totalResultList = append(totalResultList, item);
		 )
    );
    return (new List from totalResultList);
);

--some helper functions for mtSearchPoints

getAPoint = (n, K) -> (toList apply(n, (i) -> random(K)));

evalAtPoint = (R, genList, point) -> (
    K := coefficientRing R;
    n := #gens R;
    eval := map(K, R, point);
    for f in genList do ( 
	if not eval(f) == 0 
	then return false;
	);
    return true;
    );

--modifiedSearchPoints = (pointsList, R, genList) -> (
--    K := coefficientRing R;
--    n := #gens R;
--    for point in pointsList do (
--	if evalAtPoint(R, genList, point)
--	then return point
--	);
--    return {};
--    );

searchPoints = (nn, R, genList) -> (
    K := coefficientRing R;
    n := #gens R;
    for i from 1 to nn do (
	point := getAPoint(n, K);
	if evalAtPoint(R, genList, point)
	then return point
	);
    return {};
    );

---


-- A function with an optional argument


beginDocumentation()
document {
        Key => RandomRationalPoints,
        Headline => "Give a random point in a variety",
        EM "RandomRationalPoints", "Give a random point inside a affine space that lies inside a variety ."
}
doc ///
    Key
        genericProjection
        (genericProjection, Ideal)
        (genericProjection,ZZ,Ideal)
        [genericProjection, Homogeneous]
        [genericProjection, MaxCoordinatesToReplace]
    Headline
       Finds a random generic projections of the ideal.
    Usage
        genericProjection(I)
    Inputs
        I:Ideal 
            in a polynomial Ring
        n:ZZ
            an integer specifying how many dimensions down to project
        MaxCoordinatesToReplace => ZZ
            can be changed
        Homogeneous => Boolean
    Outputs
        :RingMap
            a Projection map.
        :Ideal
            defining ideal of the projection of V(I)     
    Description
        Text
            If no integer $n$ is provided, this gives the projection map from $\mathbb{A}^N \mapsto\mathbb{A}^{N-1}$ and the defining ideal of the projection of $V(I)$.
        Example
            R=ZZ/5[x,y,z]
            I = ideal(x,y^2)
            genericProjection(I)
        Text
            More generally, this gives the projection map from $\mathbb{A}^N \mapsto\mathbb{A}^{N-n}$ and the defining ideal of the projection of $V(I)$
        Example
            R=ZZ/5[x,y,z,w]
            I = ideal(x,y^2,w^3+x^2)
            genericProjection(2,I)
///
doc ///
    Key
        randomCoordinateChange
        (randomCoordinateChange, Ring)
        [randomCoordinateChange, MaxCoordinatesToReplace]
        [randomCoordinateChange, Replacement]
        [randomCoordinateChange, Homogeneous]
    Headline
        produce linear automorphism of the ring
    Usage
        randomCoordinateChange R
    Inputs
        R:Ring
            a polynomial Ring
        MaxCoordinatesToReplace => ZZ 
            how many coordinates should be replaced by linear functions
        Replacement => Symbol 
            whether coordinate replacements should be binomial (Simple) or fully random (Full) 
        Homogeneous => Boolean
            whether coordinate replacements should be Homogeneous
    Outputs
        :RingMap
            the coordinate change map.
    Description
        Text
            Given a polynomial ring, this will produce a linear automorphism of the ring. 
        Example
            R=ZZ/5[x,y,z]
            randomCoordinateChange(R)
        Text
            In some applications, a full change of coordinates is not desired, as it might cause code to run slowly, and so a simpler change of coordinates might be preferred.  
            These simpler changes of coordinates can be accomplished with the options {\tt Replacement} and {\tt MaxCoordinatesToReplace}.
            {\tt Replacement} can take either {\tt Simple} or {\tt Full}.  If {\tt Simple} is specified, then only binomial changes of coordinates will be produced. 
        Example
            S = ZZ/11[a..e]
            randomCoordinateChange(S, Replacement=>Simple)
        Text
            On the other hand, the user can specify that only a specified number of coordinates should be non-monomial changes.
        Example
            randomCoordinateChange(S, MaxCoordinatesToReplace=>2)
        Text
            Finally, if {\tt Homogeneous} is set to {\tt false}, then our change of coordinates is not homogeneous (although it is still linear).
        Example 
            randomCoordinateChange(R, Homogeneous=>false)
        Text
            Note, this function already checks whether the function is an isomorphism by computing the Jacobian.
///

doc ///
    Key
        projectionToHypersurface
        (projectionToHypersurface, Ideal)
    Headline
        Projection to a random hypersurface.
    Usage
        projectionToHypersurface I   
    Inputs
        I:Ideal
            an ideal in a polynomial Ring
        MaxCoordinatesToReplace => ZZ
            can be changed
        Codimension => ZZ
        Homogeneous => Boolean
    Outputs
        :RingMap
            a Projection map.
        :Ideal
            defining ideal of the projection of V(I)  
    Description
        Text
            Gives a projection to a random hypersurface.  
        Example
            R=ZZ/5[x,y,z]
            I = ideal(random(3,R)-2, random(2,R))
            projectionToHypersurface(I)
///

doc ///
    Key
        [randomPoints, Strategy]
        [findANonZeroMinor, Strategy]
        [extendingIdealByNonVanishingMinor, Strategy]
        BruteForce
        GenericProjection
        LinearIntersection
        HybridProjectionIntersection
    Headline
        values for the option Strategy when calling randomPoints
    Description
        Text
            When calling {\tt randomPoints}, set the strategy to one of these.
            {\tt BruteForce} simply tries random points and sees if they are on the variety.
            {\tt GenericProjection} projects to a hypersurface, via {\tt projectionToHypersurface} and then uses a {\tt BruteForce} strategy.
            {\tt LinearIntersection} intersects with an appropriately random linear space.
            {\tt HybridProjectionIntersection} does a generic projection, followed by a linear intersection. Notice that speed, or success, varies depending on the strategy.
    SeeAlso
        randomPoints
        randomKRationalPoint
        projectionToHypersurface
///

doc ///
    Key
        randomPoints
        (randomPoints,ZZ,Ideal)
        (randomPoints, Ring)
        (randomPoints, Ideal)
        [randomPoints,ProjectionAttempts]
        [randomPoints, PointCheckAttempts]
        [randomPoints, MaxCoordinatesToReplace]
        [randomPoints, IntersectionAttempts]
        [randomPoints, Homogeneous ]
        [randomPoints,ExtendField]
        [randomPoints,Codimension]
    Headline
        a function to find random points  in a variety. 
    Usage
        randomPoints(n,I)
        randomPoints(I)
        randomPoints(R)
        randomPoints(n,I, Strategy => GenericProjection)
        randomPoints(n,I, Strategy=> LinearIntersection )
    Inputs
        n: ZZ
            an integer denoting the number of desired points.
        I:Ideal
            inside a polynomial ring.
        R:Ring
            a polynomial ring
        Strategy => String
            to specify whether to use method of Linear Intersection, Generic Projection, HybridProjectionIntersection
        ProjectionAttempts => ZZ
            can be changed
        PointCheckAttempts => ZZ
            can be changed
        MaxCoordinatesToReplace => ZZ
            can be changed
        Codimension => ZZ
            can be changed
        ExtendField =>Ring
        IntersectionAttempts => ZZ
            can be changed
        Homogeneous => Boolean
    Outputs
        :List
            a list of points in the variety with possible repetitions.
    Description
        Text  
           Gives at most $n$ many point in a variety $V(I)$. 
        Example
            R=ZZ/5[t_1..t_3];
            I = ideal(t_1,t_2+t_3);
            randomPoints(3,I)
            randomPoints(4,I, Strategy => GenericProjection)
            randomPoints(4,I, Strategy => LinearIntersection)
///

doc ///
    Key
        findANonZeroMinor
        (findANonZeroMinor, ZZ, Matrix, Ideal)
    Headline
        finds a non-vanishing minor at some randomly chosen point 
    Usage
        findANonZeroMinor(n,M,I)
        findANonZeroMinor(n,M,I, Strategy => GenericProjection)
        findANonZeroMinor(n,M,I, Strategy => LinearIntersection)
        findANonZeroMinor(n,M,I, Strategy => HybridProjectionIntersection)
    Inputs
        I: Ideal
            in a polynomial ring over QQ or ZZ/p for p prime 
        M: Matrix
            over the polynomial ring
        n: ZZ
            the size of the minors to look at to find
            one non-vanishing minor 
        Strategy => String
            to specify whether to use method of Linear Intersection, GenericProjection or HybridProjectionIntersection
    Outputs
        : Sequence
            The functions outputs the following:
            
            1. randomly chosen point $P$ in $V(I)$, 
            
            2. the indexes of the columns of $M$ that stay linearly independent upon plugging $P$ into $M$, 

            3. the indices of the linearly independent rows of the matrix extracted from $M$ using (2), 

            4. a random $n\times n$ submatrix of $M$ that has full rank at $P$.
    Description
        Text
            Given an ideal, a matrix, an integer and a user defined Strategy, this function uses the 
            {\tt randomPoints} function to find a point in 
            $V(I)$. Then it plugs the point in the matrix and tries to find
            a non-zero  minor of size equal to the given integer. It outputs the point and also one of the submatrices of interest
            along with the column and row indices that were used sequentially. 
        Example
            R = ZZ/5[x,y,z];
            I = ideal(random(3,R)-2, random(2,R));
            M = jacobian(I);
            findANonZeroMinor(2,M,I, Strategy => GenericProjection)
    SeeAlso
        randomPoints
///


doc ///
    Key
        extendingIdealByNonVanishingMinor
        (extendingIdealByNonVanishingMinor, ZZ, Matrix, Ideal)
    Headline
        extends the ideal to aid finding singular locus
    Usage
        extendingIdealByNonvanishingMinor(n,M,I)
        extendingIdealByNonVanishingMinor(n,M,I, Strategy => GenericProjection)
        extendingIdealByNonVanishingMinor(n,M,I, Strategy => LinearIntersection)
        enxtendingIdealByNonVanishingMinor(n,M,I, Strategy => HybridProjectionIntersection)
    Inputs
        I: Ideal
            in a polynomial ring over QQ or ZZ/p for p prime 
        M: Matrix
            over the polynomial ring
        n: ZZ
            the size of the minors to look at to find
            one non-vanishing minor 
        Strategy => String
            to specify whether to use method of Linear Intersection, GenericProjection or HybridProjectionIntersection
    Outputs
        : Ideal
            the original ideal extended by the determinant of 
            the non vanishing minor found
    Description
        Text
            This function finds a submatrix of size $n\times n$ using {\tt findANonZeroMinor};  
            it extracts the last entry of the output, finds its determinant and
            adds it to the ideal $I$, thus extending $I$.
        Example
            R = ZZ/5[x,y,z];
            I = ideal(random(3,R)-2, random(2,R));
            M = jacobian(I);
            extendingIdealByNonVanishingMinor(2,M,I, Strategy => LinearIntersection)
    SeeAlso
        findANonZeroMinor
///


doc ///
    Key
        mtSearchPoints
        (mtSearchPoints, Ideal)
    Headline
        searching points in $V(I)$ using multiple threads
    Usage
        mtSearchPoints I   
    Inputs
        I:Ideal
            an ideal in a polynomial Ring
        PointCheckAttempts => ZZ
            points to search in total
        NumThreadsToUse => ZZ
            number of threads to use
        NumTrials => ZZ
            number of trails
        ReturnAllResults => Boolean
            whether to search and return all found points
    Outputs
        :List
            a list of points in the variety $V(I)$.
    Description
        Text
            This function use NumThreadsToUse threads to search for points in the variety.
        Example
            R=ZZ/101[x,y,z];
            I = ideal "xy-z,x2-y+z-1";
            mtSearchPoints I
///


 ----- TESTS -----

--this test tests ....
TEST/// 
R=ZZ/5[x,y,z,w];
I = ideal(x,y^2,w^3+x^2);
genericProjection(2,I);
--assert(map)
///

TEST///
---this tests findANonZeroMinor---
R = ZZ/5[x,y,z];
I = ideal(random(3,R)-2, random(2,R));
M = jacobian(I);
Output = findANonZeroMinor(2,M,I);
phi = map(ZZ/5, R, sub(matrix{Output#0},ZZ/5));
assert(det(phi(Output#3))!=0)
///


TEST///
---this tests extendingIdealByNonVanishingMinor---
R = ZZ/7[t_1..t_3];
I = ideal(t_1,t_2+t_3);
M = jacobian I;           
assert(dim extendingIdealByNonVanishingMinor(2,M,I,Strategy => LinearIntersection) < 1)
///

end

-- Here place M2 code that you find useful while developing this
-- package.  None of it will be executed when the file is loaded,
-- because loading stops when the symbol "end" is encountered.

installPackage "RandomRationalPoints"
installPackage("RandomRationalPoints", RemakeAllDocumentation=>true)
check RandomRationalPoints

-- Local Variables:
-- compile-command: "make -C $M2BUILDDIR/Macaulay2/packages PACKAGES=RandomRationalPoints pre-install"
-- End:
