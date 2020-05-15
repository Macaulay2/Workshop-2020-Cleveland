-- -*- coding: utf-8 -*-
newPackage(
        "RandomRationalPoints",
    	Version => "1.0",
    	Date => "May 13, 2020",
    	Authors => {
	     {Name => "Sankhaneel Bisui", Email => "sbisu@tulane.edu", HomePage=>"https://sites.google.com/view/sankhaneelbisui/home"},
	     {Name=> "Thai Nguyen", Email =>"tnguyen11@tulane.edu", HomePage=>"https://sites.google.com/view/thainguyenmath "},
	     {Name=>"Karl Schwede", Email=>"schwede@math.utah.edu", HomePage=>"https://www.math.utah.edu/~schwede/" }
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
	"randomPoint", 
	"createRandomPoints",
        "MyOption", 
	"GenericProjection", 
	"NumPointsToCheck", 
	"Codimension",
	"MaxChange",
	"BruteForce",
	"ProjectionAttempts"}
exportMutable {}

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

randomRatPt = method(Options=>{Homogeneous=>true, Codimension => null});

randomRatPt(Ideal) := opts -> (I1) -> (
        local c1;
        if (opts.Codimension === null) then (
        c1 = codim I1;
        ) else (c1 = opts.Codimension);

);

randomRatPtInhomog := (I1) -> (

);

randomRatPt(Ideal, Boolean) := opts -> (I,b) -> ( --this is temporary, it's just a copy of randomKRationalPoint from M2, so we can explore it
        R:=ring I;
        if char R == 0 then error "randomRatPt: expected a finite ground field";
        if not class R === PolynomialRing then error "randomRatPt: expected an ideal in a polynomial ring";
        if (not opts.Homogeneous) then return randomRatPtInhomog(I);
        if not isHomogeneous I then error "randomRatPt: expected a homogeneous ideal with Homogeneous => true";

        n:=dim I;
        if n<=1 then error "expected a positive dimensional scheme";
        c:=codim I;
        Rs:=R;
        Re:=R;
        f:=I;
        phi := null;
        if not c==1 then (
        -- projection onto a hypersurface
        parametersystem:=ideal apply(n,i->R_(i+c));
        while not dim(I+parametersystem)== 0 do (
        phi = randomCoordinateChange(I, Homogeneous=>opts.Homogeneous);
        );
        kk:=coefficientRing R;
        Re=kk(monoid[apply(dim R,i->R_i),MonomialOrder => Eliminate (c-1)]);
        rs:=(entries selectInSubring(1,vars Re))_0;
        Rs=kk(monoid[rs]);
        f=ideal substitute(selectInSubring(1, generators gb substitute(I,Re)),Rs);
        if not degree I == degree f then return print "make coordinate change"
        );
        H:=0;pts:=0;pts1:=0;trial:=1;pt:=0;ok:=false;
        while (
        H=ideal random(Rs^1,Rs^{dim Rs-2:-1});
        pts=decompose (f+H);
        pts1=select(pts,pt-> degree pt==1 and dim pt ==1);
        ok=( #pts1>0);
        if ok then (pt=saturate(substitute(pts1_0,R)+I);ok==(degree pt==1 and dim pt==0));
        not ok) do (trial=trial+1);
        pt
);




--Function to check if random point is in the variety
randomPoint = method( Options=>{Strategy=>BruteForce, Homogeneous => true, MaxChange => 0, Codimension => null});

randomPointViaGenericProjection = method(Options => {Strategy=>null, Homogeneous => true, MaxChange => 0, Codimension => null, ProjectionAttempts => 20});
randomPointViaGenericProjection(ZZ, Ideal) := opts -> (n1, I1) -> (
        flag := true;
        local phi;
        local I0;
        local J0;
        local pt;
        local ptList;
        local j;
        i := 0;
        while(flag) and (i < opts.ProjectionAttempts) do (
        (phi, I0) = projectionToHypersurface(I1, Homogeneous=>opts.Homogeneous, MaxChange => opts.MaxChange, Codimension => null);
        if (codim I0 == 1) then (
        pt = randomPoint(n1, I0, Strategy=>BruteForce); --find a point on the generic projection
        if (not pt === false) then (
        J0 = I1 + sub(ideal apply(dim source phi, i -> (first entries matrix phi)#i - pt#i), target phi); --lift the point to the original locus
        if dim(J0) == 0 then( --hopefully the preimage is made of points
        ptList = decompose(J0);
        j = 0;
        while (j < #ptList) do (
        if (degree (ptList#j) == 1) then (
        return apply(gens ring I1, x -> x%(ptList#j));
        );
        j = j+1;
        )
        )
        );
        );
        if (debugLevel >0) then print "That didn't work, trying again...";
        i = i+1;
        );
);

randomPoint(Ideal) := List => opts->(I1)->(
        genList:= first entries gens I1;
	K:=coefficientRing ring I1;point:=createRandomPoints(I1);
	eval:= map(K,ring I1,point);
	j:=0;
	while(j< #genList) do (
        tempEval:=eval(genList_j);
        if not (tempEval==0) then return false;
        j=j+1
        );
        if (tempEval ==0) then return point else return "Failed to  find";
)

randomPoint(ZZ,Ideal):=opts->(n1,I1)->(
        if (opts.Strategy == BruteForce) then (
    	j:=0;
    	local apoint;
		while( j<n1) do (
			apoint=randomPoint(I1);
			if not (apoint===false ) then return apoint; 
			j=j+1;
		);
		return "Failed to find";
	)
	else if (opts.Strategy == GenericProjection) then (
		return randomPointViaGenericProjection(n1, I1, opts)
	);
);


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
    Headline
       Finds a random generic projections of the ideal.
    Usage
        genericProjection(I)
    Inputs
        I:Ideal 
	    in a polynomial Ring
    Outputs
        :RingMap
           a Projection map.
        :Ideal
           defining ideal of the projection of V(I)     
    Description
       Text
         Gives the projection map from $\mathbb{A}^N \mapsto\mathbb{A}^{N-1}$ and the defining ideal of the projection of $V(I)$.  
       	 
	   
       Example
         R=ZZ/5[x,y,z]
	 I = ideal(x,y^2)
	 genericProjection(I)
       
///
doc ///
    Key
        genericProjection
        (genericProjection,ZZ,Ideal)
    Headline
       Finds a random generic projections of the ideal.
    Usage
        genericProjection(n,I)
    Inputs
        I:Ideal 
	    in a polynomial Ring
        n:ZZ
            an integer    
    Outputs
        :RingMap
           a Projection map.
        :Ideal
           defining ideal of the projection of V(I)     
    Description
       Text
         Gives the projection map from $\mathbb{A}^N \mapsto\mathbb{A}^{N-n}$ and the defining ideal of the projection of $V(I)$.  
       	 
	   
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
        createRandomPoints
        (createRandomPoints, Ideal)
    Headline
        Finds a Random Point in the affine space.
    Usage
        createRandomPoints(I)
    Inputs
        I:Ideal 
	    inside a polynomial Ring
    Outputs
        :List
            a point in affine space.
    Description
       Text
         Gives a random point in the ambient space of $V(I)$.  
       	 
	   
       Example
         R=ZZ/5[x,y,z]
	 I = ideal(x,y^2)
	 createRandomPoints(I)
      
///
doc ///
    Key
        randomPoint
        (randomPoint, Ideal)
    Headline
        a function to check if  a random point is  in a variety
    Usage
        randomPoint(I)
    Inputs
	I:Ideal
	    inside a polynomial ring
    Outputs
        :List
	  a point if it is in the variety otherwise false.
///  

doc ///
    Key
        (randomPoint,ZZ,Ideal)
    Headline
        a function to find  a random point  in a variety upto a given number of trials
    Usage
        randomPoint(n,I)
    Inputs
        n: ZZ
            an integer denoting the number of desired trials.
        I:Ideal
            inside a polynomial ring
    Outputs
        :List
    Description
        Text  
       	   Gives a point in a variety $V(I)$, by $n$ trials. 
        Example
            R=ZZ/5[t_1..t_3];
            I = ideal(t_1,t_2+t_3);
            randomPoint(1000,I)
///
 ----- TESTS -----

TEST///
 R=QQ[t_1..t_3];
 I = ideal(t_1,t_2+t_3);
 assert(#(createRandomPoints(I))===3)
///

TEST///
 R=QQ[t_1..t_3];
 I = ideal(t_1,t_2+t_3, t_1-1);
 assert(evaluate(I)===false);
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
