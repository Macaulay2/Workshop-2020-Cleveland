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
	"randomPointViaMultiThreads",
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
    "MultiThreads",  --a valid value for [RandomPoint, Strategy]
	"ProjectionAttempts", --used in the GenericProjection strategy
    "IntersectionAttempts", --used in the LinearIntersection strategy
    "ExtendField", --used in GenericProjection and LinearIntersection strategy
    "PointCheckAttempts",
    "extendingIdealByNonVanishingMinor",
    "NumTrials", -- used in the MultiThreads strategy
    "NumThreadsToUse" -- used in the MultiThreads strategy
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
    PointCheckAttempts => 100,
    NumThreadsToUse => 4,
    NumTrials => 1
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

-*
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
)*-

randomPoints = method(TypicalValue => List, Options => optRandomPoints);

randomPoints(Ideal) := List => opts -> (I) -> (
    --if they give us an ideal of a quotient ring, then 
    if (class ring I === QuotientRing) 
    then return randomPoints(sub(I, ambient ring I) + ideal ring I, opts);
    
    --if it is not a quotient of polynomial ring, nor a polynomial ring, then we error
    if (not class ring I === PolynomialRing) 
    then error "randomPoints: must be an ideal in a polynomial ring or a quotient thereof";
    
    genList := first entries gens I;
    R := ring I;
   
    if (opts.Strategy == BruteForce) 
    then return searchPoints(opts.PointCheckAttempts, R, genList)
    	
    else if (opts.Strategy == GenericProjection) 
    then return randomPointViaGenericProjection(I, opts)
	
    else if (opts.Strategy == LinearIntersection) 
    then return randomPointViaLinearIntersection(I, opts)

    else if (opts.Strategy == HybridProjectionIntersection) 
    then return randomPointViaLinearIntersection(I, opts)
    
    -- after multiple times, MultiThreads causes stack error [DEBUG]
    else if (opts.Strategy == MultiThreads)
    then return randomPointViaMultiThreads(I, opts)
    
    else error "randomPoints:  Not a valid Strategy";
);

randomPoints(ZZ, Ideal) := opts -> (n1, I1) -> (
    --todo:  The generic projection in particular, would be able to do this much better, without a loop.
    local apoint;
    local L;
    L = new MutableList;
    for i from 1 to n1 do (
        apoint = randomPoints(I1, opts);
        L = append(L, apoint);
	);  
    return new List from L;
);

extendingIdealByNonVanishingMinor = method(Options=>optRandomPoints)
extendingIdealByNonVanishingMinor(Ideal,Matrix, ZZ):= opts -> (I, M, n) -> (
    local P;
    local kk; 
    local R;
    local phi;
    local N; local N1; local N2; local N1new; local N2new;
    local J; local M2;
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
        N1 = columnRankProfile(N);
        N2 = rowRankProfile(N);
        M1 := mutableMatrix M;
	N1new = {};
	N2new = {};
	for i from  0 to n-1 do(
	    N1new = join(N1new, {N1#i});
	    N2new = join(N2new, {N2#i});
	    );
	M2 = M1_N1new^N2new;
    	M3 := matrix M2;
    	L1 := ideal (det(M3));
    	Ifin := I + L1;
    	return Ifin;
    );	
);



randomPointViaMultiThreads = method(TypicalValue => List, Options => optRandomPoints);
randomPointViaMultiThreads(Ideal) := List => opts -> (I) -> (
    genList := first entries gens I;
    R := ring I;
    K := coefficientRing R;
    n := #gens R;
    
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
    
--    if opts.NumThreadsToUse > allowableThreads
--    then error "mtSearch: Not enough allowed threads to use";
    
    local flag;
    flag = new MutableList from {false};
    
    taskList := apply(opts.NumThreadsToUse, (i)->(return createTask(mtSearchPoints, (numPointsToCheck, R, genList, flag));));
    apply(taskList, t -> schedule t);
    while true do (
	nanosleep 100000000;--this should be replaced by a usleep or nanosleep command.
        if (all(taskList, t -> isReady(t))) then break;
    );
      
    resultList = apply(taskList, t -> taskResult(t));
    
    if any(resultList, (l) -> (#l>0))
    then (
	 j := 0;
	 while #(resultList#j) == 0 do j = j + 1;
	 return resultList#j;
    );

    return {};
);

--some helper functions for randomPointViaMultiThreads

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

mtSearchPoints = (nn, R, genList, flag) -> (
    local point;
    K := coefficientRing R;
    n := #gens R;
    for i from 1 to nn do (
	point = getAPoint(n, K);
	if evalAtPoint(R, genList, point)
	then (
	    flag#0 = true;
	    return point;
	    );
	if flag#0
	then return {};
	);
    return {};
    );

searchPoints = (nn, R, genList) -> (
    local point;
    K := coefficientRing R;
    n := #gens R;
    for i from 1 to nn do (
	point = getAPoint(n, K);
	if evalAtPoint(R, genList, point)
	then return point;
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
        BruteForce
        GenericProjection
        LinearIntersection
        HybridProjectionIntersection
	MultiThreads
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
        (randomPoints, Ideal)
        [randomPoints, ProjectionAttempts]
        [randomPoints, PointCheckAttempts]
        [randomPoints, MaxCoordinatesToReplace]
        [randomPoints, IntersectionAttempts]
        [randomPoints, Homogeneous]
        [randomPoints, ExtendField]
        [randomPoints, Codimension]
    Headline
        a function to find random points  in a variety. 
    Usage
        randomPoints(n, I)
        randomPoints(I)
        randomPoints(n, I, Strategy => GenericProjection)
        randomPoints(n, I, Strategy => LinearIntersection)
    Inputs
        n: ZZ
            an integer denoting the number of desired points.
        I:Ideal
            inside a polynomial ring.
        R:Ring
            a polynomial ring
        Strategy => String
            to specify whether to use method of Linear Intersection or of GenericProjection
        ProjectionAttempts => ZZ
            can be changed
        MaxCoordinatesToReplace => ZZ
            can be changed
        Codimension => ZZ
            can be changed
        ExtendField =>Ring
        IntersectionAttempts => ZZ
            can be changed
	PointCheckAttempts => ZZ
	    points to search in total
        NumThreadsToUse => ZZ
	    number of threads to use
	NumTrials => ZZ
	    number of trails
        Homogeneous => Boolean
    Outputs
        :List
            a list of points in the variety with possible repetitions.
    Description
        Text  
           Gives at most $n$ many point in a variety $V(I)$. 

        Example
            R = ZZ/5[t_1..t_3];
            I = ideal(t_1,t_2+t_3);
            randomPoints(3, I)
            randomPoints(4, I, Strategy => GenericProjection)
            randomPoints(4, I, Strategy => LinearIntersection)
///

doc ///
    Key 
    	randomPointViaGenericProjection
	(randomPointViaGenericProjection, Ideal)
    Headline
    	
    Usage
    	randomPointViaGenericProjection(I)
    Inputs
    	I:Ideal
    Outputs
    	:List    	
///

doc ///
    Key 
    	randomPointViaLinearIntersection
	(randomPointViaLinearIntersection, Ideal)
    Headline
    	
    Usage
    	randomPointViaLinearInteresection(I)
    Inputs
    	I:Ideal
    Outputs
    	:List    	
///        

doc ///
    Key
        extendingIdealByNonVanishingMinor
        (extendingIdealByNonVanishingMinor, Ideal, Matrix, ZZ)
    Headline
        extends the ideal to aid finding singular locus
    Usage
        extendingIdealByNonVanishingMinor(I,M,n, Strategy => GenericProjection)
        extendingIdealByNonVanishingMinor(I,M,n, Strategy => LinearIntersection)
    Inputs
        I: Ideal
            in a polynomial ring over QQ or ZZ/p for p prime 
        M: Matrix
            over the polynomial ring
        n: ZZ
            the size of the minors to look at to find
            one non-vanishing minor 
        Strategy => String
            to specify whether to use method of Linear Intersection or of GenericProjection	    
    Outputs
    	:Ideal
	    the original ideal extended by the determinant of 
	    the non vanishing minor found
    Description
    	Text
	    Given an ideal, a matrix and an integer, this function uses the @TO 
	    randomPointViaLinearIntersection@ function to find a point in 
	    $V(I)$. Then it plugs the point in the matrix and tries to find
	    a non-zero  minor of size equal to the given integer. 
	    It then extracts the minor from the original given matrix corresponding
	    to this non-vanishing minor, finds its determinant and
	    adds it to the original ideal. 
    	Example
	    R = ZZ/5[t_1..t_3];
            I = ideal(t_1,t_2+t_3);
	    M = jacobian I;
            extendingIdealByNonVanishingMinor(I,M,2, Strategy => LinearIntersection)
///

 ----- TESTS -----

--this test tests ....
TEST/// 
R=ZZ/5[x,y,z,w];
I = ideal(x,y^2,w^3+x^2);
genericProjection(2,I);
assert(map)
///

TEST///
 
///

TEST///
R = ZZ/7[t_1..t_3];
I = ideal(t_1,t_2+t_3);
M = jacobian I;           
assert(dim extendingIdealByNonVanishingMinor(I,M,2,Strategy => LinearIntersection) < 1)
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
