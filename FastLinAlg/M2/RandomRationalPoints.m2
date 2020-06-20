
newPackage(
        "RandomRationalPoints",
    	Version => "1.2",
    	Date => "June 6th, 2020",
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
	"genericProjection", --documented, tested
	"projectionToHypersurface", --documented, tested
    "projectionToHypersurfaceV2", --documented, tested
	"randomCoordinateChange", --documented, tested
	"randomPoints", 
	"extendingIdealByNonVanishingMinor",
	"findANonZeroMinor",
    "randomPointViaLinearIntersection", --these are here for debugging purposes
    "randomPointViaLinearIntersectionOld", --these are here for debugging purposes
    "getRandomForms", --here for debugging purposes
	"MyOption",
	"NumPointsToCheck", 
	"Codimension",
	"MaxCoordinatesToReplace",
    "MaxCoordinatesToTrivalize",
    "Replacement",
    "Full", 
    "Default", --a valid value for [RandomPoint, Strategy]
	"BruteForce", --a valid value for [RandomPoint, Strategy], documented, 
    "GenericProjection",  --a valid value for [RandomPoint, Strategy]
    "HybridProjectionIntersection", --a valid value for [RandomPoint, Strategy]
    "LinearIntersection",  --a valid value for [RandomPoint, Strategy]
--    "LinearProjection", --a valid value for [RandomPoint, Strategy]
    --"MultiThreads",  --a valid value for [RandomPoint, Strategy]
	"ProjectionAttempts", --used in the GenericProjection strategy
    "IntersectionAttempts", --used in the LinearIntersection strategy
    "ExtendField", --used in GenericProjection and LinearIntersection strategy
    "PointCheckAttempts",
    "NumThreadsToUse" -- used in the BruteForce strategy
    }
exportMutable {}

needsPackage "SwitchingFields";
needsPackage "MinimalPrimes";
installMinprimes();

optRandomPoints := {
    Strategy=>Default, 
    Homogeneous => true,  
    MaxCoordinatesToReplace => 1, 
    MaxCoordinatesToTrivalize => infinity,
    Replacement => Binomial,
    Codimension => null,
    IntersectionAttempts => 20,
    ProjectionAttempts => 30,
    ExtendField => false,
    PointCheckAttempts => 100,
    NumThreadsToUse => 1,
    Verbose => false
};

optCoorindateChange := {
    Verbose => false, 
    Homogeneous=>true, 
    Replacement=>Full, 
    MaxCoordinatesToReplace => infinity
};

optProjectionToHypersurface := {
    Codimension => null,
    Verbose => false, 
    Homogeneous=>true, 
    Replacement=>Binomial, 
    MaxCoordinatesToReplace => infinity
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


randomCoordinateChange = method(Options=>optCoorindateChange);

randomCoordinateChange(Ring) := opts -> (R1) -> (
    if (debugLevel > 0) or (opts.Verbose) then print "randomCoordinateChange: starting.";
    local phi;
    if not class R1 === PolynomialRing then error "randomCoordinateChange: expected a polynomial ring";
    myMon := monoid R1;
    S1 := (coefficientRing R1)(myMon);
    d1 := #gens R1;
    local genList;
    if (opts.Replacement == Binomial) then (
        genList = getRandomForms(R1, {0, max(d1 - opts.MaxCoordinatesToReplace, 0), 0, min(d1, opts.MaxCoordinatesToReplace), 0}, Homogeneous => opts.Homogeneous, Verbose=>opts.Verbose, Verify=>true); )
    else if (opts.Replacement == Full) then (
        genList = getRandomForms(R1, {0, max(d1 - opts.MaxCoordinatesToReplace, 0), 0, 0, min(d1, opts.MaxCoordinatesToReplace)}, Homogeneous => opts.Homogeneous, Verbose=>opts.Verbose, Verify=>true); );
--    genList = random apply(genCount, t -> if (t < opts.MaxCoordinatesToReplace) then replacementFunction(genList#t) else genList#t);
    return map(R1, S1, genList);
);


genericProjection = method(Options=>optCoorindateChange);

genericProjection(Ideal) := opts -> (I1) -> (
    return genericProjectionByKernel(1, I1, opts);
);

genericProjection(ZZ, Ideal) := opts -> (n1, I1) -> (
    return genericProjectionByKernel(n1, I1, opts);
);

--this code is based upon randomKRationalPoint
genericProjectionOriginal = method(Options=>optCoorindateChange);

genericProjectionOriginal(ZZ, Ideal) := opts -> (n1, I1) -> (
        if (debugLevel > 0) or (opts.Verbose) then print concatenate("genericProjection (dropping ", toString(n1), " dimension):  Starting, Replacement =>", toString(opts.Replacement), ", MaxCoordinatesToReplace => ", toString(opts.MaxCoordinatesToReplace));
        R1 := ring I1;
        psi := randomCoordinateChange(R1, opts);
        flag := true;
        local psiInv;
        while (flag) do (
            try psiInv = inverse(psi) then (flag = false) else (psi = randomCoordinateChange(R1, opts));
        );
        S1 := source psi;
        I2 := psiInv(I1);
        if (n1 <= 0) then return(psi, I2); --if we don't actually want to project
        kk:=coefficientRing R1;
        local Re;
        local Rs;
        Re=kk(monoid[apply(dim S1,i->S1_i), MonomialOrder => Eliminate n1]);
        rs:=first (entries selectInSubring(1,vars Re));
        Rs=kk(monoid[rs]);
        f:=ideal substitute(selectInSubring(1, generators gb substitute(I2,Re)),Rs);
        phi := map(S1, Rs);
        return(psi*phi, f);
);

--using the SubringLimit option, as in Cremona.
genericProjectionByKernel = method(Options=>optCoorindateChange);

genericProjectionByKernel(ZZ, Ideal) := opts -> (n1, I1) -> (
    if (debugLevel > 0) or (opts.Verbose) then print concatenate("genericProjectionByKernel (dropping ", toString(n1), " dimension):  Starting, Replacement =>", toString(opts.Replacement), ", MaxCoordinatesToReplace => ", toString(opts.MaxCoordinatesToReplace));
    R1 := ring I1;
    local psi;
    if not class R1 === PolynomialRing then error "genericProjectionByKernel: expected an ideal in a polynomial ring";
    if (n1 <= 0) then( --if we don't want to project
        return(map(R1, R1), I1); --if we don't actually want to project
    ); 
    kk:=coefficientRing R1;
    myVars := drop(gens R1, n1);
    Rs := kk(monoid[myVars]);
    d2 := #myVars;
    local genList;
    if (opts.Replacement == Binomial) then (
        genList = getRandomForms(R1, {0, max(d2 - opts.MaxCoordinatesToReplace, 0), 0, min(d2, opts.MaxCoordinatesToReplace), 0}, Homogeneous => opts.Homogeneous, Verbose=>opts.Verbose, Verify=>true); )
    else if (opts.Replacement == Full) then (
        genList = getRandomForms(R1, {0, max(d2 - opts.MaxCoordinatesToReplace, 0), 0, 0, min(d2, opts.MaxCoordinatesToReplace)}, Homogeneous => opts.Homogeneous, Verbose=>opts.Verbose, Verify=>true); );
--    genList = random apply(genCount, t -> if (t < opts.MaxCoordinatesToReplace) then replacementFunction(genList#t) else genList#t);
    psi = map(R1, Rs, genList);
    myMap := map(R1/I1, Rs, genList);
    K2 := ker(myMap);
    return(psi, K2);
);

genericProjection(ZZ, Ring) := opts -> (n1, R1) -> (
    J1 := ideal R1;
    l1 := genericProjection(n1, J1, opts);
    if (class R1 === PolynomialRing) then (
        return (l1#0, source (l1#0));
    )
    else (
        J2 := l1#1;
        S1 := source(l1#0);
        newMap := map(R1, S1/J2, matrix(l1#0));
        return (newMap, source newMap);
    );
);

genericProjection(Ring) := opts -> (R1) -> (
    return genericProjection(1, R1, opts);
);

projectionToHypersurface = method(Options => optProjectionToHypersurface);
-*
projectionToHypersurface(Ideal) := opts -> (I1) -> (
        local c1;
        if (opts.Codimension === null) then (
            c1 = codim I1;
        ) else (c1 = opts.Codimension);
        return genericProjection(c1-1, I1, Homogeneous => opts.Homogeneous, MaxCoordinatesToReplace => opts.MaxCoordinatesToReplace, Replacement => opts.Replacement, Verbose=>opts.Verbose);
);*-

projectionToHypersurface(Ring) := opts -> (R1) -> (
    LO := projectionToHypersurface(ideal R1, opts);
    phi := map(R1, (source (LO#0))/(LO#1), matrix (LO#0) );
    return (phi, source phi);
);

--projectionToHypersurfaceV2 = method(Options=>optProjectionToHypersurface);

projectionToHypersurface(Ideal) := opts -> (I1) -> (
    local c1;
    R1 := ring I1;
    if (class R1 =!= PolynomialRing) then error "projectionToHypersurface:  expected an ideal in a polynomial ring.";
    
    if (opts.Codimension === null) then (
        c1 = codim I1;
    ) else (c1 = opts.Codimension);
    if (c1 <= 1) then return (map(R1, R1), I1); --its already a hypersurface
    n1 := c1-1;
    
    --build the target ring
    kk:=coefficientRing R1;
    myVars := drop(gens R1, n1);
    Rs := kk(monoid[myVars]);
    d2 := #myVars;
    
    --build the replacement map
    local genList;
    if (opts.Replacement == Binomial) then (
        genList = getRandomForms(R1, {0, max(d2 - opts.MaxCoordinatesToReplace, 0), 0, min(d2, opts.MaxCoordinatesToReplace), 0}, Homogeneous => opts.Homogeneous, Verbose=>opts.Verbose, Verify=>true); )
    else if (opts.Replacement == Full) then (
        genList = getRandomForms(R1, {0, max(d2 - opts.MaxCoordinatesToReplace, 0), 0, 0, min(d2, opts.MaxCoordinatesToReplace)}, Homogeneous => opts.Homogeneous, Verbose=>opts.Verbose, Verify=>true); );
--    genList = random apply(genCount, t -> if (t < opts.MaxCoordinatesToReplace) then replacementFunction(genList#t) else genList#t);
    psi := map(R1, Rs, genList);
    myMap := map(R1/I1, Rs, genList);
    J1 := ker(myMap, SubringLimit=>1);
    return (psi, J1);
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

verifyPoint = method(Options => optRandomPoints);
verifyPoint(List, Ideal) := opts -> (finalPoint, I1) -> (
    if (opts.Homogeneous) then( 
        if (all(finalPoint, t -> t == 0)) then return false;
    );
    if (#finalPoint > 0) then (
        S1 := ring finalPoint#0;
        if (any(first entries gens I1, tt -> evalAtPoint(S1, tt, finalPoint) != 0)) then (
            if (opts.Verbose or debugLevel > 0) then print "verifyPoint: found a point that is not on the variety, if not using a projection strategy, this may indicate a problem.";
            return false;
        );
    )
    else return false;
    return true;
);

--The following gets a list of random forms in a ring.  You specify how many.  
--if Verify is true, it will check to for linear independence of the monomial, binomial and randForms 
getRandomForms = method(Options => {Verify => false, Homogeneous => false, Verbose=>false});
getRandomForms(Ring, List) := opts -> (R1, L1) ->(
    if (opts.Verbose) or (debugLevel > 0) then print "getRandomForms: starting";
    constForms := L1#0;
    monomialForms := L1#1;
    trueMonomialForms := L1#2; --forced to be monomial whether or not Homogeneous is true
    binomialForms := L1#3; 
    randForms := L1#4;
    formList := {}; 
    genList := gens R1;
    d := #genList;
    --tempList is used if Verify => true, it tries to maximize linear independence of monomial and binomial forms,
    --this is important if you are trying to verify some ring map is actually surjective 
    tempList := random genList;
    if (opts.Verify) then (
        if (#tempList < monomialForms + trueMonomialForms + binomialForms) then (tempList = tempList | apply(monomialForms + trueMonomialForms + binomialForms - #tempList, i->(genList)#(random d)));
    );
    if (opts.Homogeneous) then (
        if (opts.Verbose) or (debugLevel > 0) then print "getRandomForms: generating homogeneous forms.";
        if (opts.Verify) then (formList = formList | apply(monomialForms, i -> (tempList)#i);)
        else (formList = formList | apply(monomialForms, i -> (genList)#(random(d))););
        if (opts.Verify) then (formList = formList | apply(trueMonomialForms, i -> (tempList)#(i+monomialForms));)
        else (formList = formList | apply(trueMonomialForms, i -> (genList)#(random(d))););
        if (opts.Verify) then (formList = formList | apply(binomialForms, i -> (tempList)#(i+monomialForms+trueMonomialForms) + (random(0, R1))*(genList)#(random(d)));) 
        else (formList = formList | apply(binomialForms, i -> (genList)#(random(d)) + (random(0, R1))*(genList)#(random(d))););
        formList = formList | apply(randForms, i-> random(1, R1));
    )
    else(
        if (opts.Verbose) or (debugLevel > 0) then print "getRandomForms: generating non-homogeneous forms.";
        if (opts.Verify) then (formList = formList | apply(monomialForms, i -> random(0, R1) + (tempList)#i);)
        else (formList = formList | apply(monomialForms, i -> random(0, R1) + (genList)#(random(d))););
        if (opts.Verify) then (formList = formList | apply(trueMonomialForms, i -> (tempList)#(i+monomialForms));)
        else (formList = formList | apply(trueMonomialForms, i -> (genList)#(random(d))););        
        if (opts.Verify) then (formList = formList | apply(binomialForms, i -> random(0, R1) + (tempList)#(i+monomialForms+trueMonomialForms) + (random(0, R1))*(genList)#(random(d)));) 
        else (formList = formList | apply(binomialForms, i -> random(0, R1) + (genList)#(random(d)) + (random(0, R1))*(genList)#(random(d))););
        formList = formList | apply(randForms, i->random(0, R1) + random(1, R1));
    );
    if (opts.Verify) and (#formList > 0) then ( --if we are checking our work
        J1 := jacobian ideal formList;
        val := min(d, #formList);
        if (rank J1 < val) then ( 
            if (opts.Verbose) or (debugLevel > 0) then print "getRandomForms: forms were not random enough, trying again recusrively.";            
            return getRandomForms(R1, L1, opts);
        );
    );
    formList = formList | apply(constForms, i -> random(0, R1));

    return random formList;
);

randomPointViaLinearIntersection = method(Options => optRandomPoints);

randomPointViaLinearIntersection(ZZ, Ideal) := opts -> (n1, I1) -> (
    returnPointsList := {};
    c1 := opts.Codimension;
    if (c1 === null) then (c1 = codim I1); --don't compute it if we already know it.
    R1 := ring I1;
    dR1 := dim R1;
    d1 := dR1 - c1;
    i := 0;
    j := 0;
    local finalPoint;
    local ptList; local newPtList;
    local phi;
    local psi;
    local myDeg;
    local myDim;
    local m2;
    local targetSpace;
    local phiMatrix;
    local J1;
    local myPowerList;
    local kk; --the extended field, if we extended
    kk = coefficientRing(R1);
    varList := drop(gens R1, d1);
    toReplace := max(0, min(opts.MaxCoordinatesToReplace, c1));
    toTrivialize := min(d1, opts.MaxCoordinatesToTrivalize);
    while(i < opts.IntersectionAttempts) and (#returnPointsList < n1) do (
        targetSpace = kk[varList];
        
        if (opts.Replacement == Binomial) then (
            phiMatrix = getRandomForms(targetSpace, {toTrivialize, 0, c1-toReplace + (d1 - toTrivialize), toReplace, 0}, Homogeneous => false, Verify=>true);
        )
        else if (opts.Replacement == Full) then (
            phiMatrix = getRandomForms(targetSpace, {toTrivialize, 0, c1-toReplace + (d1 - toTrivialize), 0, toReplace}, Homogeneous => false, Verify=>true);
        );
        if (opts.Verbose) or (debugLevel > 0) then print concatenate("randomPointViaLinearIntersection: doing loop with ", toString( phiMatrix));
        if (debugLevel > 0 or opts.Verbose == true) then print concatenate("randomPointViaLinearIntersection:  Doing a loop with:", toString(phiMatrix));
        phi = map(targetSpace, R1, phiMatrix);
        J1 = phi(I1);
        if (dim J1 == 0) then (
            if (c1 == 1) then ( --if we are intersecting with a line, we can go slightly faster by using factor instead of decompose
                ptList = apply(toList factor(gcd(first entries gens J1)), t->ideal(t#0));
            )
            else (
                ptList = random decompose(J1);
            );
            j = 0;
            while (j < #ptList) and (#returnPointsList < n1) do (
                myDeg = degree(ptList#j);
                myDim = dim(ptList#j);
                if (myDim == 0) and (myDeg == 1) then (
                    finalPoint = first entries evalAtPoint(R1, matrix{phiMatrix}, idealToPoint(ptList#j));
                    --finalPoint = apply(idealToPoint(ptList#j), s -> sub(s, R1));
                    if (verifyPoint(finalPoint, I1, opts)) then returnPointsList = append(returnPointsList, finalPoint);
                )
                else if (myDim == 0) and (opts.ExtendField == true) then (
                    if (debugLevel > 0) or (opts.Verbose) then print "randomPointViaLinearIntersection:  extending the field.";
                    psi = (extendFieldByDegree(myDeg, targetSpace))#1;
                    newR1 := target psi;
                    m2 = psi(ptList#j);
                    newPtList = random decompose(m2); --make sure we are picking points randomly from this decomposition
                    --since these points are going to be conjugate, we only pick 1.  
                    if (#newPtList > 0) then ( 
                        finalPoint = first entries evalAtPoint(newR1, matrix{phiMatrix}, idealToPoint(newPtList#0));
                        --finalPoint =  apply(idealToPoint(newPtList#0), s -> sub(s, target phi));
                        if (verifyPoint(finalPoint, I1, opts)) then returnPointsList = append(returnPointsList, finalPoint);
                    ); 
                );
                j = j+1;
            );
        );
        if (debugLevel > 0) or (opts.Verbose) then(
            if (#returnPointsList < n1) then 
                print ("randomPointViaLinearIntersection:  found " | toString(#returnPointsList) | " points so far, trying a new linear space.")
            else print ("randomPointViaLinearIntersection:  found " | toString(#returnPointsList) | " points so far, stopping.");
        );
        i = i+1;
    );
    return returnPointsList;
);

randomPointViaGenericProjection = method(Options => optRandomPoints);
randomPointViaGenericProjection(ZZ, Ideal) := opts -> (n1, I1) -> (
    pointsList := {}; --a list of points to output
    flag := true;
    local phi;
    local psi;
    local I0;
    local J0;
    local pt;
    local pts; --a list of points produced by 
    local ptList;
    local j;
    local k;
    local finalPoint;
    local newPtList;
    local phi;
    local myDeg;
    local myDim;
    local m2;
    R1 := ring I1;  
    i := 0;
    while (flag) and (i < opts.ProjectionAttempts) and (#pointsList < n1) do (
        if (opts.Codimension === null) then (
            c1 := codim I1;
            if (c1 == 1) then ( --don't project, if we are already a hypersurface
                phi = map(ring I1, ring I1);
                I0 = I1;
            )
            else(
                (phi, I0) = projectionToHypersurface(I1, Homogeneous=>opts.Homogeneous, Replacement => opts.Replacement, MaxCoordinatesToReplace => opts.MaxCoordinatesToReplace, Codimension => c1, Verbose=>opts.Verbose);
            );
        )
        else if (opts.Codimension == 1) then (
            phi = map(ring I1, ring I1);
            I0 = I1;
        )
        else(
            (phi, I0) = projectionToHypersurface(I1, Homogeneous=>opts.Homogeneous, Replacement => opts.Replacement, MaxCoordinatesToReplace => opts.MaxCoordinatesToReplace, Codimension => opts.Codimension, Verbose=>opts.Verbose);
        );
        if (codim I0 == 1) then (
            if (debugLevel > 0) or opts.Verbose then print "randomPointViaGenericProjection:  found a good generic projection, now finding a point on it.";
            if (opts.Strategy == GenericProjection) then (
                pts = randomPoints(n1-#pointsList, I0, switchStrategy(opts, BruteForce)))
            else if (opts.Strategy == HybridProjectionIntersection) then (
                pts = random randomPoints(n1-#pointsList, I0, switchStrategy(opts, LinearIntersection))
            ); --find a point on the generic projection (differently, depending on strategy)
            if (#pts > 0) then (
                k = 0;
                while (k < #pts) and (#pointsList < n1) do ( --we produced some other points, now lift them
                    pt = pts#k;
                    J0 = I1 + sub(ideal apply(dim source phi, i -> (first entries matrix phi)#i - sub(pt#i, target phi)), target phi); --lift the point to the original locus
                    if dim(J0) == 0 then( --hopefully the preimage is made of points
                        ptList = random decompose(J0);
                        j = 0;
                        while (j < #ptList) and (#pointsList < n1) do ( --points we produced
                            myDeg = degree (ptList#j);
                            --print myDeg;
                            if (myDeg == 1) then (
                                finalPoint = apply(idealToPoint(ptList#j), s -> sub(s, coefficientRing ring I1));
                                if (verifyPoint(finalPoint, I1, opts)) then pointsList = append(pointsList, finalPoint);
                            )                        
                            else if (opts.ExtendField == true) then (
                                if (debugLevel > 0) or (opts.Verbose) then print "randomPointViaGenericProjection:  extending the field.";
                                psi = (extendFieldByDegree(myDeg, ring ptList#j))#1;
                                m2 = psi(ptList#j);
                                newPtList = random decompose(m2);
                                if (#newPtList > 0) then ( 
                                    finalPoint =  apply(idealToPoint(newPtList#0), s -> sub(s, target psi));
                                    if (verifyPoint(finalPoint, I1, opts)) then pointsList = append(pointsList, finalPoint);
                                ); 
                            );
                            j = j+1;
                        )
                    )
                    else(
                        if (debugLevel > 0) or opts.Verbose then print "randomPointViaGenericProjection:  Lift of point is not a point (our projection was not sufficiently generic).";
                    );
                    k = k+1;
                );
            );
        );
        if (debugLevel > 0) or (opts.Verbose) then print ("randomPointViaGenericProjection: found " | toString(#pointsList) | " points so far.  We may do another loop.");
        i = i+1;
    );
    return pointsList;
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

randomPointViaDefaultStrategy = method(Options => optRandomPoints);
randomPointViaDefaultStrategy(ZZ, Ideal) := List => opts -> (n1, I1) -> (
    pointsList := {}; --a list of points to output
    c1 := opts.Codimension;
    if (c1 === null) then (c1 = codim I1); --don't compute it if we already know it.

    if (opts.Verbose) or (debugLevel > 0) then print "randomPointViaDefaultStrategy: starting";
    --we can do a brute force attempt for hypersurfaces when the field is small
    if (c1 == 1) then (
        if (opts.Verbose) or (debugLevel > 0) then print "randomPointViaDefaultStrategy(step 0): trying BruteForce";
        kk := coefficientRing ring I1;
        fieldSize := ((degree (ideal ambient kk)_0)#0);
        pointsList = pointsList | randomPointsBranching(n1, I1, opts++{Strategy=>BruteForce, PointCheckAttempts=>min(30*n1, 4*n1*fieldSize)});
    );
    
    --lets give a quick generic projection a shot (well, the hybrid version)
    if (opts.Verbose) or (debugLevel > 0) then print "randomPointViaDefaultStrategy(step 1): trying a quick projection, coordinates only";
    pointsList = pointsList | randomPointsBranching(n1 - #pointsList, I1, 
        opts++{ Strategy=>HybridProjectionIntersection,
                MaxCoordinatesToReplace => 0,
                Replacement => Binomial,
                MaxCoordinatesToTrivalize => infinity,
                ProjectionAttempts => 2,
                IntersectionAttempts => 2*n1
            }
    );
    if (#pointsList >= n1) then return pointsList;


    --next do a very fast intersection with coordinate linear spaces
    if (#pointsList >= n1) then return pointsList;
    if (opts.Verbose) or (debugLevel > 0) then print "randomPointViaDefaultStrategy(step 2): trying a quick linear intersection, coordinates only";
    pointsList = pointsList | randomPointsBranching(n1 - #pointsList, I1, 
        opts++{ Strategy=>LinearIntersection,
                MaxCoordinatesToReplace => 0,
                IntersectionAttempts => 2*n1,
                MaxCoordinatesToTrivalize => infinity
            }
    );
    if (#pointsList >= n1) then return pointsList;
    
    --next do a very fast intersection with nearly coordinate linear spaces
    if (opts.Verbose) or (debugLevel > 0) then print "randomPointViaDefaultStrategy(step 3): trying a quick linear intersection, coordinates and one binomial only";
    pointsList = pointsList | randomPointsBranching(n1 - #pointsList, I1, 
        opts++{ Strategy=>LinearIntersection,
                MaxCoordinatesToReplace => 1,
                Replacement => Binomial,
                MaxCoordinatesToTrivalize => infinity,
                IntersectionAttempts => 4*n1
            }
    );
    if (#pointsList >= n1) then return pointsList;
    
    --next do a fast intersection with slightly less trivial coordinate linear spaces
    if (opts.Verbose) or (debugLevel > 0) then print "randomPointViaDefaultStrategy(step 4): trying a quick linear intersection, coordinates and one random term only";
    pointsList = pointsList | randomPointsBranching(n1 - #pointsList, I1, 
        opts++{ Strategy=>LinearIntersection,
                MaxCoordinatesToReplace => 1,
                Replacement => Full,
                MaxCoordinatesToTrivalize => infinity,
                IntersectionAttempts => 4*n1
            }
    );
    if (#pointsList >= n1) then return pointsList;
    
    --lets give generic projection another shot
    if (opts.Verbose) or (debugLevel > 0) then print "randomPointViaDefaultStrategy(step 5): giving projection another shot, coordinates and one binomial only";
    pointsList = pointsList | randomPointsBranching(n1 - #pointsList, I1, 
        opts++{ Strategy=>HybridProjectionIntersection,
                MaxCoordinatesToReplace => 1,
                Replacement => Binomial,
                MaxCoordinatesToTrivalize => infinity,
                ProjectionAttempts => 3,
                IntersectionAttempts => 4*n1
            }
    );
    if (#pointsList >= n1) then return pointsList;
    
    --now do a intersection with linear spaces involving fewer coordinates
    if (opts.Verbose) or (debugLevel > 0) then print "randomPointViaDefaultStrategy(step 6): trying a quick linear intersection, coordinates and two binomials only";
    pointsList = pointsList | randomPointsBranching(n1 - #pointsList, I1, 
        opts++{ Strategy=>LinearIntersection,
                MaxCoordinatesToReplace => 2,
                Replacement => Binomial,
                MaxCoordinatesToTrivalize => 4,
                IntersectionAttempts => 4*n1
            }
    );
    if (#pointsList >= n1) then return pointsList;
    
    --first do a slower intersection with linear spaces involving fewer coordinates
    if (opts.Verbose) or (debugLevel > 0) then print "randomPointViaDefaultStrategy(step 7): trying a quick linear intersection, coordinates and two linear terms only";
    pointsList = pointsList | randomPointsBranching(n1 - #pointsList, I1, 
        opts++{ Strategy=>LinearIntersection,
                MaxCoordinatesToReplace => 2,
                Replacement => Full,
                MaxCoordinatesToTrivalize => 2,
                IntersectionAttempts => 4*n1
            }
    );
    if (#pointsList >= n1) then return pointsList;
    
    --lets try another projection
    if (opts.Verbose) or (debugLevel > 0) then print "randomPointViaDefaultStrategy(step 8): giving projection another shot, coordinates and two binomials only";
    pointsList = pointsList | randomPointsBranching(n1 - #pointsList, I1, 
        opts++{ Strategy=>HybridProjectionIntersection,
                MaxCoordinatesToReplace => 2,
                Replacement => Binomial,
                MaxCoordinatesToTrivalize => 2,
                ProjectionAttempts => 3*n1,
                IntersectionAttempts => 4*n1
            }
    );
    if (#pointsList >= n1) then return pointsList;
    
    --this one is probably quite slow
    if (opts.Verbose) or (debugLevel > 0) then print "randomPointViaDefaultStrategy(step 9): trying a linear intersection, binomials only";
    pointsList = pointsList | randomPointsBranching(n1 - #pointsList, I1, 
        opts++{ Strategy=>LinearIntersection,
                MaxCoordinatesToReplace => infinity,
                Replacement => Binomial,
                MaxCoordinatesToTrivalize => 1,
                IntersectionAttempts => 4*n1
            }
    );
    if (#pointsList >= n1) then return pointsList;
    
    --this one can be extremely slow
    if (opts.Verbose) or (debugLevel > 0) then print "randomPointViaDefaultStrategy(step 10): trying a linear intersection, full random";
    pointsList = pointsList | randomPointsBranching(n1 - #pointsList, I1, 
        opts++{ Strategy=>LinearIntersection,
                MaxCoordinatesToReplace => infinity,
                Replacement => Full,
                MaxCoordinatesToTrivalize => 1,
                IntersectionAttempts => 4*n1
            }
    );
    return pointsList;
);

randomPoints = method(TypicalValue => List, Options => optRandomPoints);

randomPoints(ZZ, Ideal) := List => opts -> (n1, I1) ->(
    randomPointsBranching(n1, I1, opts)
);
randomPoints(Ideal) := List => opts -> (I1) ->(
    randomPointsBranching(1, I1, opts)
);


randomPointsBranching = method(TypicalValue => List, Options => optRandomPoints);

randomPointsBranching(ZZ, Ideal) := List => opts -> (n1, I) -> (
    if (opts.Verbose) or (debugLevel > 0) then print concatenate("randomPointsBranching: starting with Strategy => ", toString(opts.Strategy));
    --if they give us an ideal of a quotient ring, then 
    if (class ring I === QuotientRing) 
    then return randomPointsBranching(n1, sub(I, ambient ring I) + ideal ring I, opts);
    
    --if it is not a quotient of polynomial ring, nor a polynomial ring, then we error
    if (not class ring I === PolynomialRing) 
    then error "randomPoints: must be an ideal in a polynomial ring or a quotient thereof";
    
    genList := first entries gens I;
    R := ring I;
    if (opts.Strategy == Default) then (
        return randomPointViaDefaultStrategy(n1, I, opts)
    )
    else if (opts.Strategy == BruteForce) 
    then (
        if (opts.NumThreadsToUse > 1) then return randomPointViaMultiThreads(n1, I, opts)
        else return searchPoints(n1, R, genList, opts);
    )	
    else if (opts.Strategy == GenericProjection) 
    then return randomPointViaGenericProjection(n1, I, opts)
	
    else if (opts.Strategy == LinearIntersection) 
    then return randomPointViaLinearIntersection(n1, I, opts)

    else if (opts.Strategy == HybridProjectionIntersection) 
    then return randomPointViaGenericProjection(n1, I, opts)
    
--    else if (opts.Strategy == LinearProjection) 
--    then return randomPointViaLinearProjection(I, opts)
    --else if (opts.Strategy == MultiThreads)
    --then return randomPointViaMultiThreads(I, opts)
    
    else error "randomPoints:  Not a valid Strategy";
);


randomPointViaMultiThreads = method(TypicalValue => List, Options => optRandomPoints);
randomPointViaMultiThreads(ZZ, Ideal) := List => opts -> (n1, I) -> (
    genList := first entries gens I;
    R := ring I;
    K := coefficientRing R;
    n := #gens R;
    
    local found;
    local resultList;
    
    local numPointsToCheck;
    numPointsToCheck = floor(opts.PointCheckAttempts / opts.NumThreadsToUse); 
    
--    if opts.NumThreadsToUse > allowableThreads
--    then error "mtSearch: Not enough allowed threads to use";
    
    local flag;
    flag = new MutableList from apply(opts.NumThreadsToUse, i->false);
    
    taskList := apply(opts.NumThreadsToUse, (i)->(return createTask(mtSearchPoints, (i, numPointsToCheck, R, genList, flag));));
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

evalAtPoint = (kk, myMatrix, curPoint) -> (
    sourceRing := ring myMatrix;
    newPhi := map(kk, sourceRing, apply(curPoint, t -> sub(t, kk)));
    return newPhi(myMatrix)
);


evalAtPointIsZero = (R, genList, point) -> (
    K := coefficientRing R;
    n := #gens R;
    eval := map(K, R, point);
    for f in genList do ( 
    	if not eval(f) == 0 
	    then return false;
	);
    return true;
);

--a function for multithreads
mtSearchPoints = (thNum, nn, R, genList, flag) -> (
    local point;
    K := coefficientRing R;
    n := #gens R;
    for i from 1 to nn do (
	point = getAPoint(n, K);
	if evalAtPointIsZero(R, genList, point)
	then (
	    flag#thNum = true;
	    return point;
	    );
	if any(flag, x->x)
	then return {};
	);
    return {};
    );

--a brute force point search tool
searchPoints = method(Options => optRandomPoints);
searchPoints(ZZ, Ring, List) := opts -> (nn, R, genList) -> (
    local point;
    K := coefficientRing R;
    n := #gens R;
    pointList := {};
    i := 0;
    while (i < opts.PointCheckAttempts) and (#pointList < nn) do (
	    point = getAPoint(n, K);
	    if evalAtPointIsZero(R, genList, point) then (
            if not ((opts.Homogeneous) and (matrix{point} == 0)) then pointList = append(pointList, point);
        );
        i = i+1;
	);
    return pointList;
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
    if (#P == 0) then  error "Couldn't find a point. Try Changing Strategy.";
    P = P#0;
    phi =  map(kk,R,sub(matrix{P},kk));
    N = mutableMatrix phi(M);
    rk := rank(N);
    if (rk < n) then return ("All minors of given size vanish at the randomly chosen point. Please try again.");
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
    if (rank(M3)<n) then return (P,N1,N2,"Using the the second and third outputs failed to generate a random matrix of the given size, that has full rank when evaluated at the first output.");
    N2rand := random(rowRankProfile(M3));
    N2new = {};
    for i from 0 to n-1 do(
        N2new = join(N2new, {N2rand#i});
    );
    Mspecificrowextract := (M_N1new)^N2new;
    return (P, N1, N2, Mspecificrowextract);	
);

extendingIdealByNonVanishingMinor = method(Options=>optRandomPoints);
extendingIdealByNonVanishingMinor(ZZ,Matrix,Ideal):= opts -> (n, M, I) -> (
    local O;  local Ifin;
    O = findANonZeroMinor(n,M,I,opts); 
    L1 := ideal (det(O#3));
    Ifin = I + L1;
    return Ifin;
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
        (genericProjection, Ring)
        (genericProjection, ZZ, Ideal)
        (genericProjection, ZZ, Ring)
        [genericProjection, Homogeneous]
    Headline
       finds a random (somewhat) generic projection of the ring or ideal
    Usage
        genericProjection(n, I)
        genericProjection(n, R)
        genericProjection(I)
        genericProjection(R)
    Inputs
        I:Ideal 
            in a polynomial ring
        R:Ring
            a quotient of a polynomial ring
        n:ZZ
            an integer specifying how many dimensions to drop
        MaxCoordinatesToReplace => ZZ
            to be passed to randomCoordinateChange
        Replacement => Symbol
            to be passed to randomCoordinateChange
        Homogeneous => Boolean
            to be passed to randomCoordinateChange
    Outputs
        :List
            a list with two entries, the generic projection map, and the ideal if I was provided, or the ring if R was provided
    Description
        Text
            This gives the projection map from $\mathbb{A}^N \mapsto\mathbb{A}^{N-n}$ and the defining ideal of the projection of $V(I)$
        Example
            R=ZZ/5[x,y,z,w];
            I = ideal(x,y^2,w^3+x^2);
            genericProjection(2,I)
        Text
            If no integer $n$ is provided, then drops one dimension, in other words it treats $n = 1$.
        Example
            R=ZZ/5[x,y,z,w];
            I = ideal(x,y^2);
            genericProjection(I)
        Text
            Alternately, instead of {\tt I}, you may pass it a quotient ring.  It will then return the inclusion of the generic projection ring into the given ring, followed by the source of that inclusion.  It is essentially the same functionality as calling {\tt genericProjection(n, ideal R)} although the format of the output is slightly different.
        Example
            R = ZZ/13[x,y,z];
            I = ideal(y^2*z-x*(x-z)*(x+z));
            genericProjection(R/I)
        Text
            This method works by calling {\tt randomCoordinateChange} before dropping some variables.  It passes the options {\tt Replacement}, {\tt MaxCoordinatesToReplace}, {\tt Homogeneous} to that function.
        Text
            This function makes no attempt to verify that the projection is actually generic with respect to the ideal.  
    SeeAlso
        randomCoordinateChange
///

doc ///
    Key
        randomCoordinateChange
        (randomCoordinateChange, Ring)
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
            whether coordinate replacements should be binomial (Binomial) or fully random (Full) 
        Homogeneous => Boolean
            whether coordinate replacements should be Homogeneous
        Verbose => Boolean
            set to true for verbose output
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
            In some applications, a full change of coordinates is not desired, as it might cause code to run slowly, and so a Binomialr change of coordinates might be preferred.  
            These Binomial changes of coordinates can be accomplished with the options {\tt Replacement} and {\tt MaxCoordinatesToReplace}.
            {\tt Replacement} can take either {\tt Binomial} or {\tt Full}.  If {\tt Binomial} is specified, then only binomial changes of coordinates will be produced. 
        Example
            S = ZZ/11[a..e]
            randomCoordinateChange(S, Replacement=>Binomial)
        Text
            Finally, if {\tt Homogeneous} is set to {\tt false}, then our change of coordinates is not homogeneous (although it is still linear).
        Example 
            randomCoordinateChange(R, Homogeneous=>false)
        Text
            Note, this function already checks whether the function is an isomorphism by computing the Jacobian.
///

doc ///
    Key
        [genericProjection, Verbose]
        [randomCoordinateChange, Verbose]
        [randomPoints, Verbose]
        [projectionToHypersurface, Verbose]
    Headline
        turns out Verbose (debugging) output
    Description
        Text
            Set the option {\tt Verbose => true} to turn on verbose output.  This may be useful in debugging or in determining why an computation is running slowly. 
///

doc ///
    Key
        projectionToHypersurface
        (projectionToHypersurface, Ideal)
        (projectionToHypersurface, Ring)
        [projectionToHypersurface, Codimension]
    Headline
        Generic projection to a hypersurface
    Usage
        projectionToHypersurface I
        projectionToHypersurface R 
    Inputs
        I:Ideal
            an ideal in a polynomial ring
        R:Ring
            a quotient of a polynomial ring
        Codimension => ZZ
            specified if you already know the codimension of your Ideal (or QuotientRing) in your ambient ring
        MaxCoordinatesToReplace => ZZ
            to be passed to randomCoordinateChange
        Replacement => Symbol
            to be passed to randomCoordinateChange
        Homogeneous => Boolean
            to be passed to randomCoordinateChange
        Verbose => Boolean
            set to true for verbose output
    Outputs
        :RingMap
            a list with two entries, the generic projection map, and the ideal if I was provided, or the ring if R was provided
    Description
        Text
            This creates a projection to a hypersurface.  It essentially calls {\tt genericProjection(codim I - 1, I)}.  
        Example
            R=ZZ/5[x,y,z];
            I = ideal(random(3,R)-2, random(2,R));
            projectionToHypersurface(I)
            projectionToHypersurface(R/I)
        Text
            If you already know the codimension is {\tt c}, you can set {\tt Codimension=>c} so the function does not compute it.
    SeeAlso
        genericProjection
///
doc///
    Key
        ProjectionAttempts
        [randomPoints, ProjectionAttempts]
    Headline
         Number of projection trials using in the Strategy GenericProjection
    Description
        Text
            When calling the Strategy {\tt GenericProjection} or {\tt HybridProjectionIntersection} from {\tt randomPoints}, this option denotes the number of trials before giving up.
    SeeAlso
        randomPoints
///

doc///
    Key
        IntersectionAttempts
        [randomPoints, IntersectionAttempts]
    Headline
        Number of intersection trials using in the Strategy LinearIntersection
    Description
        Text
            When calling the Strategy {\tt LinearIntersection}  it denotes the number of trials whose default value is 20.
    SeeAlso
        randomPoints
///

doc///
    Key
        MaxCoordinatesToReplace
        [randomCoordinateChange, MaxCoordinatesToReplace]
        [randomPoints, MaxCoordinatesToReplace]
        [genericProjection, MaxCoordinatesToReplace]
    Headline
        The maximum number of coordinates to turn into non-monomial functions when calling {\tt randomCoordinateChange}
    Description
        Text
            When calling {\tt randomCoordinateChange}, the user can specify that only a specified number of coordinates should be non-monomial.  Sometimes, generic coordinate changes where all coordinates are modified, can be very slow.  This is a way to mitigate for that.
            This option is passed to {\tt randomCoordinateChange} by other functions that call it.
        Example
            S = ZZ/11[a..e]
            randomCoordinateChange(S, MaxCoordinatesToReplace=>2)
    SeeAlso
        randomCoordinateChange
///

doc ///
    Key
        Replacement
        [randomCoordinateChange, Replacement]
        [genericProjection, Replacement]
        [projectionToHypersurface, Replacement]
        Full
    Headline
        When changing coordinates, whether to replace variables by general degre 1 forms or binomials
    Usage
        Replacement => Full
        Replacement => Binomial
    Description
        Text
            When calling {\tt randomCoordinateChange}, or functions that call it, setting {\tt Replacement => Full} will mean that coordinates are changed to a general degree 1 form.  If {\tt Replacement => Binomial}, the coordiates are only changed to bionomials, which can be much faster for certain applications.
        Example
            R = ZZ/11[a,b,c];
            randomCoordinateChange(R, Replacement=>Full)
            randomCoordinateChange(R, Replacement=>Binomial)
        Text
            If {\tt Homogeneous => false}, then there will be constant terms, and we view $mx + b$ as a binomial.
        Example
            S = ZZ/11[x,y];
            randomCoordinateChange(S, Replacement => Full, Homogeneous => false)
            randomCoordinateChange(S, Replacement => Binomial, Homogeneous => false)
    SeeAlso
        randomCoordinateChange
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

-*doc///
    Key
        Codimension
        [randomPoints, Codimension]
        [projectionToHypersurface, Codimension]
    Headline
        Checks the 
    Description 
        Text
            
    SeeAlso
        randomPoints
        projectionToHypersurface
///
*-
doc///
    Key 
        NumThreadsToUse
        [randomPoints, NumThreadsToUse]
    Headline
        Number of threads the the function will use to search for a point 
    Description
        Text
            When calling {\tt randomPoints}, and functions that call it, with a {\tt BruteForce} strategy, this denotes the number of threads for brute force point checking.
        Example
            R = ZZ/11[x,y,z];
            I = ideal(x,y);
	    allowableThreads = 8;
            randomPoints(I, NumThreadsToUse=>4)
    SeeAlso
        randomPoints
///

doc///
    Key 
        PointCheckAttempts
        [randomPoints, PointCheckAttempts]
        [extendingIdealByNonVanishingMinor,PointCheckAttempts ]
        [findANonZeroMinor, PointCheckAttempts]
    Headline
        Number of times the the function will search for a point 
    Description
        Text
            When calling {\tt randomPoints}, and functions that call it, with a {\tt BruteForce} strategy or {\tt GenericProjection} strategy, this denotes the number of trials for brute force point checking.
        Example
            R = ZZ/11[x,y,z];
            I = ideal(x,y);
            randomPoints(I, PointCheckAttempts=>1)
            randomPoints(I, PointCheckAttempts=>1000)
    SeeAlso
        randomPoints
        extendingIdealByNonVanishingMinor
        findANonZeroMinor
///

doc ///
    Key
        randomPoints
	(randomPoints, Ideal)
        (randomPoints, ZZ, Ideal)
        [randomPoints, Homogeneous]
        [randomPoints, ExtendField]
        [randomPoints, Codimension]
    Headline
        a function to find random points  in a variety. 
    Usage
        randomPoints(I) 
        randomPoints(n, I)
        randomPoints(n, I, Strategy => GenericProjection)
        randomPoints(n, I, Strategy => LinearIntersection)
        randomPoints(n, I, Strategy => HybridProjectionIntersection)
    Inputs
        n: ZZ
            an integer denoting the number of desired points.
        I:Ideal
            inside a polynomial ring.
        R:Ring
            a polynomial ring
        Strategy => String
            to specify which strategy to use, BruteForce, LinearIntersection, GenericProjection, HybridProjectionIntersection
        ProjectionAttempts => ZZ
            see @TO ProjectionAttempts@
        MaxCoordinatesToReplace => ZZ
            see @TO MaxCoordinatesToReplace@
        Codimension => ZZ
            see @TO Codimension@
        ExtendField => Boolean
        IntersectionAttempts => ZZ
            see @TO IntersectionAttempts@
	PointCheckAttempts => ZZ
	    points to search in total, see @TO PointCheckAttempts@
        NumThreadsToUse => ZZ
	    number of threads to use, see @TO NumThreadsToUse@
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

 ----- TESTS -----

--this test tests ....
TEST/// 
R=ZZ/5[x,y,z,w];
I = ideal(x,y^2,w^3+x^2);
genericProjection(2,I);
--assert(map)
///

--testing randomCoordinateChange with Homogeneous => true
TEST///
R = QQ[x,y,z,w];
phi = randomCoordinateChange(R, Homogeneous=>true);
m = ideal(x,y,z,w);
S = source phi;
n = sub(m, S);
assert(preimage(phi, m) == n);  --if we are homogeneous, this should be true
assert(phi(n) == m);
///

--testing randomCoordinateChange with Homogeneous => false
TEST ///
R = ZZ/1031[x,y,z,u,v,w];
phi = randomCoordinateChange(R, Homogeneous => false);
m = ideal(x,y,z);
S = source phi;
n = sub(m, S);
assert(dim phi(n) == dim m);
assert(dim preimage(phi, m) == dim n);
assert(preimage(phi, m) != n); --there is a theoretical chance this could happen, about 1 in 10^18.
assert(phi(n) != m);
///

--testing randomCoordinateChange with MaxCoordinatesToReplace => 0
TEST ///
R = ZZ/11[x,y,z];
phi = randomCoordinateChange(R, MaxCoordinatesToReplace => 0);
M = matrix phi;
S1 = set first entries M;
S2 = set gens R;
assert(isSubset(S1, S2) and isSubset(S2, S1));
///

--verifying Binomial vs Full replacement
TEST ///
R = ZZ/1031[a..h];
phi = randomCoordinateChange(R, Replacement=>Binomial);
psi = randomCoordinateChange(R, Replacement=>Full);
assert(all(apply(first entries matrix phi, v -> terms v), t -> #t <= 2));
assert(any(apply(first entries matrix psi, v -> terms v), t -> #t >= 3)); --this could be false, and an asteroid could destroy Earth.
///

--testing genericProjection, on an ideal
TEST///
R = ZZ/101[a,b,c];
I = ideal(a,b,c);
L = genericProjection(2, I, Homogeneous => true);
assert(dim source (L#0) == 1);
assert(dim (L#1) == 0);  
L2 = genericProjection(I, Homogeneous => true);
assert(dim source (L2#0) == 2);
assert(dim (L2#1) == 0);  
L3 = genericProjection(2, I, Homogeneous => false)
assert(dim (L3#1) == 0)
///

--testing genericProjection, on a ring
TEST///
R = ZZ/101[x,y,z]/ideal(y^2*z-x*(x-z)*(x+z));
L = genericProjection(1, R, Homogeneous => true); --we are already a hypersurface, so this should turn into a polynomial ring
assert(dim source (L#0) == 2);
assert(ker (L#0) == 0)
L2 = genericProjection(1, R, Homogeneous => false);
assert(dim source (L#0) == 2);
assert(ker (L2#0) == 0)
///

--testing projectionToHypersurface, for an ideal and a ring
TEST///
R = ZZ/11[x,y,z];
I = ideal(random(2, R), random(3, R));
L = projectionToHypersurface(I);
assert(dim source(L#0) == 2); --we should drop one dimension
assert(codim(L#1) == 1);
L2 = projectionToHypersurface(R/I);
assert(dim source(L2#0) == 1)
assert(codim(L2#1) == 1)
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
