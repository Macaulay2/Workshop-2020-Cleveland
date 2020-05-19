-- -*- coding: utf-8 -*-
newPackage(
        "RandomRationalPointscopy",
    	Version => "1.0",
    	Date => "May 13, 2020",
    	Authors => {
	     {Name => "Sankhaneel Bisui", Email => "sbisu@tulane.edu", HomePage=>"https://sites.google.com/view/sankhaneelbisui/home"},
	     {Name=> "Thai Nguyen", Email =>"tnguyen11@tulane.edu", HomePage=>"https://sites.google.com/view/thainguyenmath "},
	     {Name=>"Karl Schwede", Email=>"schwede@math.utah.edu", HomePage=>"https://www.math.utah.edu/~schwede/" },
	     {Name => "Sarasij Maitra", Email => "sm3vg@virginia.edu", HomePage => "https://people.virginia.edu~sm3vg"}
	     }
	     {Name
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
	"MyOption", 
	"NumPointsToCheck", 
	"Codimension",
	"MaxChange",
	"BruteForce", --a valid value for [RandomPoints, Strategy]
    "GenericProjection",  --a valid value for [RandomPoints, Strategy]
    "LinearIntersection",  --a valid value for [RandomPoints, Strategy]
    "ModifiedBruteForce",  --a valid value for [RandomPoints, Strategy]
	"ProjectionAttempts", --used in the GenericProjection strategy
    "IntersectionAttempts", --used in the LinearIntersection strategy
    "ExtendField", --used in GenericProjection and LinearIntersection strategy
    "checkRandomPoint",
    "PointCheckAttempts",
    "extendingIdealByNonVanishingMinor"
    }
exportMutable {}

needsPackage "SwitchingFields";
needsPackage "MinimalPrimes";
installMinprimes();

optRandomPoints := {
    Strategy=>BruteForce, 
    Homogeneous => true, 
    MaxChange => 0, 
    Codimension => null,
    IntersectionAttempts => 20,
    ProjectionAttempts => 20,
    ExtendField => false,
    PointCheckAttempts => 100
}

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


randomCoordinateChange = method(Options=>{Homogeneous=>true, MaxChange => infinity});

randomCoordinateChange(Ring) := opts -> (R1) -> (
        local phi;
        if not class R1 === PolynomialRing then error "randomCoordinateChange: expected an ideal in a polynomial ring";
        myMon := monoid R1;
        S1 := (coefficientRing R1)(myMon);
        if (opts.MaxChange == infinity) then (
        if (opts.Homogeneous) then (
        phi = map(R1, S1, apply(gens R1, t -> random(1, R1)));
        )
        else(
        phi = map(R1, S1, apply(gens R1, t -> random(1, R1)+random(0, R1)));
        );
        )
        else( --if we only want to really change some (MaxChange) of the variables, and randomize the others
        genList := random gens R1;
        if (opts.Homogeneous) then (
--			genList = random apply(#(genList), t -> (if (t < opts.MaxChange) then random(1, R1) else genList#t) );
        genList = random apply(#(genList), t -> (if (t < opts.MaxChange) then ((random(0, R1))*(genList#t) + (random(0, R1))*(genList#(random(#genList)))) else genList#t) );

        )
        else(
        genList = random apply(#(genList), t -> (if (t < opts.MaxChange) then random(1, R1)+random(0, R1) else genList#t	) );
        );
        phi = map(R1, S1, genList);
        );
        return phi;
);

genericProjection = method(Options =>{Homogeneous => true, MaxChange => infinity});

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

projectionToHypersurface = method(Options =>{Homogeneous => true, MaxChange => infinity, Codimension => null});

projectionToHypersurface(Ideal) := opts -> (I1) -> (
        local c1;
        if (opts.Codimension === null) then (
        c1 = codim I1;
        ) else (c1 = opts.Codimension);
        local curMap;
        return genericProjection(c1-1, I1, Homogeneous => opts.Homogeneous, MaxChange => opts.MaxChange);
);

-*
projectionToHypersurface(Ideal) := opts -> (I1) -> (
	local c1;
	if (opts.Codimension === null) then (
		c1 = codim I1;
	) else (c1 = opts.Codimension);
	local curMap;
	tempList := genericProjection(I1, Homogeneous => opts.Homogeneous, MaxChange => opts.MaxChange);
	assert(target (tempList#0) === ring I1);
	if (c1 == 2) then (
		return tempList; --if we are done, stop
	);
	assert(source (tempList#0) === ring (tempList#1));
	--otherwise recurse
	tempList2 := projectionToHypersurface(tempList#1, Hoxmogeneous => opts.Homogeneous, MaxChange => opts.MaxChange, Codimension=>c1-1);
	assert(target(tempList2#0) === ring (tempList#1));
	return ((tempList#0)*(tempList2#0), tempList2#1);
);
*-




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
                    newPtList = random decompose(m2);
--                    1/0;
                    if (#newPtList > 0) then ( 
                        finalPoint =  apply(idealToPoint(newPtList#0), s -> sub(s, target phi));
                        return finalPoint
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
        (phi, I0) = projectionToHypersurface(I1, Homogeneous=>opts.Homogeneous, MaxChange => opts.MaxChange, Codimension => opts.Codimension);
        if (codim I0 == 1) then (
            pt = randomPoints(I0, Strategy=>BruteForce); --find a point on the generic projection
            if (not pt === {}) then (
                J0 = I1 + sub(ideal apply(dim source phi, i -> (first entries matrix phi)#i - pt#i), target phi); --lift the point to the original locus
                if dim(J0) == 0 then( --hopefully the preimage is made of points
                    ptList = random decompose(J0);
                    j = 0;
                    while (j < #ptList) do (
                        myDeg = degree (ptList#j);
                        print myDeg;
                        if (myDeg == 1) then (
                            finalPoint = apply(idealToPoint(ptList#j), s -> sub(s, coefficientRing ring I1));
                            return finalPoint;
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
    noVar := #generators R1;
    K:=coefficientRing R1;
    L:=toList apply(noVar, i ->random(K));
    if (opts.Homogeneous == true) then if (all(L, i->i==0)) then return randomPoints(R1);
    return L
);  



randomPoints(Ideal):=opts->(I1)->(
    local apoint;
    local outpt;
    local eval;
    K:=coefficientRing ring I1;
    local j;
    local i;
    local flag;
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
                apoint=randomPoints(ring I1);
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
        --1/0;
        return randomPointViaLinearIntersection(I1, opts)
    )
    else (
        error "randomPoints:  Not a valid Strategy"
    )
);

randomPoints(ZZ,Ideal):=opts->(n1,I1)->(
        i:=0;
        local apoint;
        local L;
        L= {};
        while(i < n1 ) do ( 
            apoint=randomPoints(I1);
            L = join(L,{apoint});
            i=i+1;
    );  
          return L;
);

extendingIdealByNonVanishingMinor = method(Options=>{})
extendingIdealByNonVanishingMinor(Ideal,Matrix, ZZ):= opts -> (I, M, n) -> (
    local P;
    local kk; 
    local R;
    local phi;
    local N; local N1; local N2; local N1new; local N2new;
    local J; local M2;
    R = ring I;
    kk = coefficientRing R;
    P = randomPointViaLinearIntersection(I);
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




-- A function with an optional argument


beginDocumentation()
document {
        Key => RandomRationalPointscopy,
        Headline => "Give a random point in a variety",
        EM "RandomRationalPoints", "Give a random point inside a affine space that lies inside a variety ."
}
doc ///
    Key
        genericProjection
        (genericProjection, Ideal)
        (genericProjection,ZZ,Ideal)
    Headline
       Finds a random generic projections of the ideal.
    Usage
        genericProjection(I)
    Inputs
        I:Ideal 
            in a polynomial Ring
        n:ZZ
            an integer specifying how many dimensions down to project
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
    Headline
        Changes the co-orinate randomly.
    Usage
        randomCoordinateChange R
    Inputs
        R:Ring
            a polynomial Ring
    Outputs
        :RingMap
            the coordinate change map.
    Description
       Text
         Gives a random coordinate change map.  
       	 
	   
       Example
         R=ZZ/5[x,y,z]
         randomCoordinateChange(R)
      
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
        randomPoints
        (randomPoints, Ideal)
    Headline
        a function to check if  a random point is  in a variety
    Usage
        randomPoints(I)
    Inputs
        I:Ideal
            inside a polynomial ring
    Outputs
        :List
            a point if it is in the variety otherwise false.
/// 
doc ///
    Key
	(randomPoints, Ring)
    Headline
        Gives a random point in the affine space.
    Usage
        randomPoints(R)
    Inputs
        R:Ring
	    a polynomial ring
    Outputs
        :List
	    a point in the affine space.
///  

doc ///
    Key
        (randomPoints,ZZ,Ideal)
    Headline
        a function to find random points  in a variety. 
    Usage
        randomPoints(n,I)
    Inputs
        n: ZZ
            an integer denoting the number of desired points.
        I:Ideal
            inside a polynomial ring.
    Outputs
        :List
    Description
        Text  
           Gives at most $n$ many point in a variety $V(I)$.  
        Example
            R=ZZ/5[t_1..t_3];
            I = ideal(t_1,t_2+t_3);
            randomPoints(3,I)
///

doc ///
    Key 
    	randomPointViaGenericProjection
	(randomPointViaGenericProjection, Ideal)	
///

doc ///
    Key
    	extendingIdealByNonVanishingMinor
	(extendingIdealByNonVanishingMinor, Ideal, Matrix, ZZ)
    Headline
    	extends the ideal to aid finding singular locus
    Usage
    	extendingIdealByNonVanishingMinor(I,M,n)
    Inputs
    	I: Ideal
	M: Matrix
	n: ZZ
	    the size of the minors to look at to find
	    one non-vanishing minor 
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
            extendingIdealByNonVanishingMinor(I,M,2)
      
///	

 ----- TESTS -----

TEST///
R=ZZ/5[x,y,z,w];
I = ideal(x,y^2,w^3+x^2);
genericProjection(2,I);
assert(map)
///

TEST///
 
///

TEST///


///

end

-- Here place M2 code that you find useful while developing this
-- package.  None of it will be executed when the file is loaded,
-- because loading stops when the symbol "end" is encountered.

installPackage "RandomRationalPointscopy"
installPackage("RandomRationalPointscopy", RemakeAllDocumentation=>true)
check RandomRationalPointscopy

-- Local Variables:
-- compile-command: "make -C $M2BUILDDIR/Macaulay2/packages PACKAGES=RandomRationalPoints pre-install"
-- End:
