
randomPointViaLinearProjection = method(Options => optRandomPoints);
randomPointViaLinearProjection(Ideal) := opts -> (I1) -> (
    if (opts.Verbose or debugLevel > 0) then print "randomPointViaLinearProjection: starting";
    flag := true;
    local phi;
    local psi;
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
        if (opts.Codimension === null) then (
            c1 := codim I1;
            if (c1 == 0) then ( --don't project, if we are already a space
                phi = map(ring I1, ring I1);
                I0 = I1;
            )
            else(
                (phi, I0) = genericProjection(c1, ideal(0_(ring I1)), Homogeneous=>opts.Homogeneous, MaxCoordinatesToReplace => opts.MaxCoordinatesToReplace, Replacement => opts.Replacement, Verbose=>opts.Verbose);
            );
        )
        else if (opts.Codimension == 0) then (
            phi = map(ring I1, ring I1);
            I0 = I1;
        )
        else(
            (phi, I0) = genericProjection(opts.Codimension, ideal(0_(ring I1)), Homogeneous=>opts.Homogeneous, MaxCoordinatesToReplace => opts.MaxCoordinatesToReplace, Replacement => opts.Replacement, Verbose=>opts.Verbose);
        );
        I0 = sub(I1, ring I0);
        pt = searchPoints(1, source phi, {});
        if (not pt === {}) then (
            J0 = I1 + sub(ideal apply(dim source phi, i -> ((first entries matrix phi)#i) - sub(pt#i, target phi)), target phi); --lift the point to the original locus
            print sub(ideal apply(dim source phi, i -> ((first entries matrix phi)#i) - sub(pt#i, target phi)), target phi);
            if dim(J0) == 0 then( --hopefully the preimage is made of points
                ptList = random decompose(J0);
                j = 0;
                while (j < #ptList) do (
                    myDeg = degree (ptList#j);
                    --print myDeg;
                    if (myDeg == 1) then (
                        finalPoint = apply(idealToPoint(ptList#j), s -> sub(s, coefficientRing ring I1));
                        if (verifyPoint(finalPoint, I1, opts)) then return finalPoint;
                    )                        
                    else if (opts.ExtendField == true) then (
                        if (debugLevel > 0) or (opts.Verbose) then print "randomPointViaLinearProjection:  extending the field.";
                        psi = (extendFieldByDegree(myDeg, R1))#1;
                        m2 = psi(ptList#j);
                        newPtList = random decompose(m2);
                        if (#newPtList > 0) then ( 
                            finalPoint = apply(idealToPoint(newPtList#0), s -> sub(s, target psi));
                            if (verifyPoint(finalPoint, I1, opts)) then return finalPoint;
                        ); 
                    );
                    j = j+1;
                );
            )
            else if (debugLevel > 0) or (opts.Verbose == true) then print "randomPointViaLinearProjection: dimension is wrong.";
        );
    
        if (debugLevel > 0) or (opts.Verbose) then print "randomPointViaLinearProjection: That didn't work, trying again...";
        i = i+1;
    );
    return {};
);




randomPointViaLinearIntersectionOld = method(Options => optRandomPoints);

randomPointViaLinearIntersectionOld(Ideal) := opts -> (I1) -> (
    c1 := opts.Codimension;
    if (c1 === null) then (c1 = codim I1); --don't compute it if we already know it.
    R1 := ring I1;
    d1 := dim R1 - c1;
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
    while(i < opts.IntersectionAttempts) do (
        targetSpace = kk[varList];
        phiMatrix = apply(#(gens R1)-c1, l -> random(1, targetSpace) + random(0, targetSpace) );
        apply(c1, t -> phiMatrix = insert(random(#phiMatrix + 1), (gens targetSpace)#t, phiMatrix)); --this trick was stolen from Cremona.
        --phiMatrix = insert(random(c1), (gens targetSpace)#(random(c1)), apply(#(gens R1)-1, l -> random(1, targetSpace) + random(0, targetSpace) )); --random linear maps, plus one random variable
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
            while (j < #ptList) do (
                myDeg = degree(ptList#j);
                myDim = dim(ptList#j);
                if (myDim == 0) and (myDeg == 1) then (
                    finalPoint = first entries evalAtPoint(R1, matrix{phiMatrix}, idealToPoint(ptList#j));
                    --finalPoint = apply(idealToPoint(ptList#j), s -> sub(s, R1));
                    if (verifyPoint(finalPoint, I1, opts)) then return finalPoint;
                )
                else if (myDim == 0) and (opts.ExtendField == true) then (
                    if (debugLevel > 0) or (opts.Verbose) then print "randomPointViaLinearIntersection:  extending the field.";
                    psi = (extendFieldByDegree(myDeg, targetSpace))#1;
                    newR1 := target psi;
                    m2 = psi(ptList#j);
                    newPtList = random decompose(m2); --make sure we are picking points randomly from this decomposition
                    if (#newPtList > 0) then ( 
                        finalPoint = first entries evalAtPoint(newR1, matrix{phiMatrix}, idealToPoint(newPtList#j));
                        --finalPoint =  apply(idealToPoint(newPtList#0), s -> sub(s, target phi));
                        if (verifyPoint(finalPoint, I1, opts)) then return finalPoint;
                    ); 
                );
                j = j+1;
            );
        );
        if (debugLevel > 0) or (opts.Verbose) then print "randomPointViaLinearIntersection:  failed, looping and trying a new linear space.";
        i = i+1;
    );
    return {};
);




randomPointViaLinearIntersectionOlder = method(Options => optRandomPoints);

randomPointViaLinearIntersectionOlder(Ideal) := opts -> (I1) -> (
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
                    if (debugLevel > 0) or (opts.Verbose) then print "randomPointViaLinearIntersection:  extending the field.";
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
        if (debugLevel > 0) or (opts.Verbose) then print "randomPointViaLinearIntersection:  failed, looping and trying a new linear space.";
        i = i+1;
    );
    return {};
);


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

randomPoints(ZZ, Ideal) := opts -> (n1, I1) -> (
    --todo:  The generic projection in particular, would be able to do this much better, without a loop.
    -*local apoint;
    local L;
    L = new MutableList;
    for i from 1 to n1 do (
        apoint = randomPoints(I1, opts);
        L = append(L, apoint);
	);  
    return new List from L;*-

);

--used to be in extendIdealByNonzeroMinor
-*   local P;
    local kk; 
    local R;
    local phi;
    local N; local N1; local N2; local N1new; local N2new;
    local J; local Mcolumnextract; local Mrowextract;
    R = ring I;
    local kk;
    P = randomPoints(I, opts);
    if (#P == 0) 
    then error "No Point Found"
    else (
        kk = ring {P#0};
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