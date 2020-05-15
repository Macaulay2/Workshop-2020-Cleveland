-- -*- coding: utf-8 -*-
------------------------------------------------------------------------------
-- Copyright 2017-2020 Gregory G. Smith
--
-- This program is free software: you can redistribute it and/or modify it
-- under the terms of the GNU General Public License as published by the Free
-- Software Foundation, either version 3 of the License, or (at your option)
-- any later version.
--
-- This program is distributed in the hope that it will be useful, but WITHOUT
-- ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
-- FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
-- more details.
--
-- You should have received a copy of the GNU General Public License along
-- with this program.  If not, see <http://www.gnu.org/licenses/>.
------------------------------------------------------------------------------
newPackage(
  "ToricMaps",
  AuxiliaryFiles => false,
  Version => "0.3",
  Date => "14 May 2020",
  Authors => {
      {
      Name => "Chris Eur", 
      Email => "chrisweur@gmail.com", 
      HomePage => "https://math.berkeley.edu/~ceur"},
      {
      Name => "Justin Chen", 
      Email => "jchen@math.berkeley.edu", 
      HomePage => "https://math.berkeley.edu/~jchen"},
      {
      Name => "Matthew Faust",
      Email => "mfaust@math.tamu.edu",
      HomePage => "https://www.math.tamu.edu/~mfaust/"},
      {
      Name => "Michael Loper",
      Email => "loper012@umn.edu",
      HomePage => "https://www.math.umn.edu/~loper012"},  
      {
      Name => "Diane Maclagan",
      Email => "D.Maclagan@warwick.ac.uk",
      HomePage => "http://homepages.warwick.ac.uk/staff/D.Maclagan/"},
      {
      Name => "Maryam Nowroozi",
      Email => "nowroozm@mcmaster.ca"},
      {
      Name => "Ritvik Ramkumar",
      Email => "ritvik@berkeley.edu",
      HomePage => "https://math.berkeley.edu/~ritvik/index.html"}, 
      {
      Name => "Julie Rana",
      Email => "ranaj@lawrence.edu",
      HomePage => "https://sites.google.com/site/jranamath"},
      {
      Name => "Mahrud Sayrafi",
      Email => "mahrud@umn.edu",
      HomePage => "https://math.umn.edu/~mahrud/"},
      {
      Name => "Gregory G. Smith", 
      Email => "ggsmith@mast.queensu.ca", 
      HomePage => "https://www.mast.queensu.ca/~ggsmith"},
      {
      Name => "Elise Walker",
      Email => "walkere@math.tamu.edu",
      HomePage => "https://www.math.tamu.edu/~walkere"},
      {
      Name => "Weikun Wang",
      Email => "wwang888@math.umd.edu",
      HomePage => "https://wangweikun.com"},
      {
      Name => "Rachel Webb",
      Email => "webbra@umich.edu",
      HomePage => "sites.google.com/view/rachel-webb"},  
      {
      Name => "Thomas Yahl",
      Email => "thomasjyahl@tamu.edu",
      HomePage => "https://www.math.tamu.edu/~thomasjyahl"},
      {
      Name => "Jay Yang",
      Email => "jkyang@umn.edu",
      HomePage => "https://www-users.math.umn.edu/~jkyang/"}
  },
  Headline => "routines for working with toric morphisms",
  PackageExports => {
      "NormalToricVarieties"
  },
  PackageImports => {
      "NormalToricVarieties",
      "LLLBases",
      "FourierMotzkin"
  },
  DebuggingMode => true,
  Reload => true
)

export {
    "ToricMap",
    "isFibration",
    "isProper",
    "pullback",
    "isDominant"
}


------------------------------------------------------------------------------
-- toric morphisms

ToricMap = new Type of HashTable
ToricMap.synonym = "toric map"
source ToricMap := NormalToricVariety => f -> f.source
target ToricMap := NormalToricVariety => f -> f.target
matrix ToricMap := Matrix => opts -> f -> f.matrix

net ToricMap := f -> net matrix f
ToricMap#{Standard,AfterPrint} = ToricMap#{Standard,AfterNoPrint} = f -> (
    << endl;	-- double space
    << concatenate(interpreterDepth:"o") << lineNumber << " : ToricMap ";
    << net target f << " <--- " << net source f << endl;
    )

map(NormalToricVariety, NormalToricVariety, Matrix) := ToricMap => opts -> (Y, X, A) -> (
    if ring A =!= ZZ then error "-- expected an integer matrix";
    if rank source A != dim X then 
        error("-- expected source to be the lattice of rank " | dim X);
    if rank target A != dim Y then 
        error("-- expected target to be the lattice of rank " | dim Y);  
    new ToricMap from {
    	symbol source => X,
    	symbol target => Y,
    	symbol matrix => A,
    	symbol cache => new CacheTable}
    )

map(NormalToricVariety, NormalToricVariety, ZZ) := ToricMap => opts -> (Y, X, i) -> (
    m := dim Y;
    n := dim X;
    if i === 0 then return map(Y, X, map(ZZ^m, ZZ^n, 0))
    else if m === n then return map(Y, X, map(ZZ^m, ZZ^n, i))
    else error "expect zero map, or the source and target to have same dimension"
    )
NormalToricVariety#id = X -> map(X,X,1)

ToricMap * ToricMap := ToricMap => (g, f) -> (
    if target f =!= source g then error "-- expected composable maps";
    new ToricMap from {
    	symbol source => source f,
    	symbol target => target g,
    	symbol matrix => (matrix g) * (matrix f),
    	symbol cache => new CacheTable
	}
    )

-- local method; produces the outer normal vectors for each max cone
-- at the moment exported for debugging purposes
outerNormals = method()
outerNormals (NormalToricVariety,List) := Matrix => (X, sigma) -> (
    if not X.cache.?outerNormals then (
    	X.cache.outerNormals = new MutableHashTable);
    if not X.cache.outerNormals#?sigma then (
    	V := transpose matrix rays X;
    	D := fourierMotzkin V_sigma;
    	if D#1 == 0 then X.cache.outerNormals#sigma = transpose D#0 
	else X.cache.outerNormals#sigma = transpose (D#0 | D#1 | -D#1));
    X.cache.outerNormals#sigma
    )



isWellDefined ToricMap := Boolean => f -> (
    -- CHECK DATA STRUCTURE
    -- check keys
    K := keys f;
    expectedKeys := set{symbol source, symbol target, symbol matrix, symbol cache};
    if set K =!= expectedKeys then (
	if debugLevel > 0 then (
	    added := toList(K - expectedKeys);
	    missing := toList(expectedKeys - K);
	    if #added > 0 then 
	        << "-- unexpected key(s): " << toString added << endl;
	    if #missing > 0 then 
	        << "-- missing keys(s): " << toString missing << endl);
    	return false
	);
    --Check types
    if not instance(f.source, NormalToricVariety) then (
	if debugLevel > 0 then (
	    << "-- expected `source' to be a NormalToricVariety" << endl);
	return false	);
    if not instance(f.target, NormalToricVariety) then (
	if debugLevel > 0 then (
	    << "-- expected `target' to be a NormalToricVariety" << endl);
	return false
	);
    if not instance(f.matrix, Matrix) then (
	if debugLevel > 0 then (
	    << "-- expected `matrix' to be a Matrix" << endl);
	return false
	);
    if ring matrix f =!= ZZ then (
    	if debugLevel > 0 then (
	    << "-- expected `matrix' over the integers" << endl);
	return false
	);	 
    if not instance(f.cache, CacheTable) then (
    	if debugLevel > 0 then (
	    << "-- expected `f.cache' to be a CacheTable" << endl);
    	return false
	);
    --Check mathematical structure
    X := source f;
    Y := target f;
    A := matrix f;
    if rank source A =!= dim X then (
    	if debugLevel > 0 then (
	    << "-- expected number of columns of the matrix to equal the dimension of the source variety"
	    );
	return false
	);
    if rank target A =!= dim Y then (
    	if debugLevel > 0 then (
	    << "-- expected number of rows of the matrix to equal the dimension of the target variety"
	    );
	return false
	);
    V := transpose matrix rays X;
    if not all(max X, sigma -> any(max Y, 
      	tau -> all(flatten entries ( outerNormals(Y, tau) * A * V_sigma), 
	i -> i <= 0))) then (
    	if debugLevel > 0 then (
	    << "-- expected image of each maximal cone to be contained in some maximal cone");
	return false
	);
    true
    )

isProper = method()
isProper ToricMap := Boolean => (cacheValue symbol isProper) (
    f -> (
    	if not isWellDefined f then error "-- The map is not well defined!";
    	X := source f;
    	Y := target f;
    	if isComplete X then return true;
    	if (isComplete Y and not isComplete X) then return false;
    	rayMatrixX := transpose matrix rays X;
    	rayMatrixY := transpose matrix rays Y;
    	A := matrix f;
    	-- based on the idea that the map should be proper if and only if all
    	-- torus invariant curves in X are PP^1 or are contained in the torus
    	-- invariant curves of Y.	    
    	for tau in max Y do (
	    -- dimension of tau cap image A and computing potential cones over tau
	    d := dim Y - rank (gens ker transpose A | gens ker transpose rayMatrixY_tau);
	    maxConesWithRightDimension := select(max X, 
	    	sigma -> member(sigma, orbits(X, rank A - d))
	    	);
	    -- compute the cones over tau
	    conesOverTau := select(maxConesWithRightDimension, 
	    	sigma -> all(flatten entries (outerNormals(Y,tau)*A*rayMatrixX_sigma),
		    i -> i <= 0)
	    	);
    	    -- if no cones over tau, not proper
	    if (#conesOverTau === 0) then return false;
    	    -- compute facets of the cones over tau
            facesOverTau := select(orbits(X, rank A - d + 1), 
	    	alpha-> any(conesOverTau, sigma -> isSubset(alpha, sigma))
	    	);
    	    -- pick which faces appear only once
	    facesCount := hashTable apply(facesOverTau,
	    	alpha -> {alpha, #select(conesOverTau, sigma -> isSubset(alpha, sigma))}
	    	);
	    uniqueFaces := select(facesOverTau, i -> facesCount#i < 2);
    	    -- faces of tau
    	    facesOfTau := select(orbits(Y, dim Y - d + 1), beta -> isSubset(beta,tau));
	    -- check if the faces appearing only once are contained in faces of tau
	    if not all(uniqueFaces, alpha -> any(facesOfTau,
		    beta -> coker (A*rayMatrixX_alpha) == coker rayMatrixY_beta)
	    	) then return false;
	    );
    	true
    	)
    )

isFibration = method()
isFibration ToricMap := Boolean => (cacheValue symbol isFibration) (f -> (
    isProper f and gens gb matrix f == id_(ZZ^(dim target f))))

isDominant = method()
isDominant ToricMap := Boolean => (cacheValue symbol isDominant) (f -> (
    rank matrix f == dim target f))

outerNorm = method()
outerNorm (NormalToricVariety,List) := Sequence => (X,sigma) -> (
  if not X.cache.?outerNorm then (
    X.cache.outerNorm = new MutableHashTable);
  if not X.cache.outerNorm#?sigma then (
    V := transpose matrix rays X;
    D := fourierMotzkin V_sigma;
    X.cache.outerNorm#sigma = {transpose D#0, transpose D#1});
    return X.cache.outerNorm#sigma)



isInterior = method()
isInterior (NormalToricVariety,List,Matrix) := Boolean => (X,sigma,rho) -> (
   if dim X =!= rank target rho then error "the dimension of the ray is not correct";
    N :=  outerNorm(X,sigma);
    NN0 := N#0;
    NN1 := N#1;  -- hyperplane vectors
   if (all (flatten entries (NN0 * rho), i -> i < 0) and all (flatten entries(NN1 * rho), i -> i === 0)) then 
   return true;
   false)


isSurjective ToricMap := Boolean => (f) -> (
    if not isWellDefined(f) then return "the map is not well defined";
    if not isDominant(f) then return false;
    targetCones := reverse flatten drop(values orbits target f, -1);
    sourceCones := flatten drop(values orbits source f, -1);
    interiorSourceCones := {};
    for sigma in sourceCones do(
  	interiorSourceCones = append(interiorSourceCones, sum((rays source f)_sigma));
    	);
    imageSourceCones := {};
    for sigma in interiorSourceCones do (
   	imageSourceCones = append(imageSourceCones, ((matrix f) * (transpose matrix{sigma})) );
	);
    if targetCones == {} then return true;
    for rho in imageSourceCones do(
    	for sigma in targetCones do(
            if isInterior(target f, sigma, rho) then targetCones = delete(sigma,targetCones));
    	);
    return targetCones == {}
   )


-- THIS IS AN UNEXPORTED METHOD FROM "NormalToricVarieties"
-- In the notation of Theorem 4.2.8 in Cox-Little-Schenck, this function returns
-- the characters $m_\sigma$ for each maximal cone $\sigma$ in the fan of a
-- Cartier divisor, which in M2 are ordered as in `max X`.
cartierCoefficients = value NormalToricVarieties#"private dictionary"#"cartierCoefficients";

-- Unexported helper function for pullback that caches the index of the maximal
-- cone in the target which contains the image of each ray of the source.
rayTargets = (cacheValue symbol rayTargets) (f -> (
    m := matrix f;
    X := source f;
    Y := target f;
    maxCones := max Y;
    -- find a maximal cone containing the image of each ray
    for ray in rays X list (
	imageRho := m * transpose matrix {ray};
	position(maxCones,
	    sigma -> all(flatten entries(outerNormals(Y, sigma) * imageRho),
		b -> b <= 0)))
    ))

-- Given ToricMap f: X -> Y and a Cartier ToricDivisor D on Y, returns a ToricDivisor on X
pullback = method()
pullback (ToricMap, ToricDivisor) := ToricDivisor => (f, D) -> (
    if not isCartier D then error "-- expected a Cartier divisor";
    cartierData := cartierCoefficients D;
    m := matrix f;
    X := source f;
    rayList := rays X;
    maxConeIndices := rayTargets f;
    sum for i to #rayList - 1 list (
	imageRho := m * transpose matrix {rayList_i};
	-- see Thm 4.2.12.b and Prop 6.2.7 in Cox-Little-Schenck (Prop 6.1.20 in the preprint)
	-- note: in CLS they use inner normals, whereas we use outer normals, hence the different sign
	(transpose cartierData_(maxConeIndices_i) * imageRho)_(0,0) * X_i)
    )

-- Given ToricMap f: X -> Y and a Module on Cox Y, with simplicial Y, returns a Module on Cox X
-- TODO: something is wrong here, a test fails
pullback (ToricMap, Module) := Module => (f, M) -> (
    if ring target f =!= ring M then error "-- expected module over the Cox ring of the target";
    (inducedMap f) ** M)

-- Given ToricMap f: X -> Y and a CoherentSheaf on Y, with simplicial Y, returns the CoherentSheaf on X
pullback (ToricMap, CoherentSheaf) := CoherentSheaf => (f, F) -> sheaf(source f, pullback(f, module F))

-- Given ToricMap f: X -> Y, with simplicial X and Y, returns the RingMap Cox Y -> Cox X
-- FIXME: correct degreeMaps
inducedMap ToricMap := RingMap => opts -> (cacheValue symbol inducedMap) (f -> (
    Y := target f;
    S := ring Y;
    R := ring source f;
    m := cartierDivisorGroup f; -- degree map
    map(R, S, apply(numgens S, i -> (
		exps := entries pullback(f, Y_i);
		product(numgens R, j -> R_j^(exps#j)))),
	DegreeMap => (deg -> first entries (matrix{deg} * transpose m))))
    )

ideal ToricMap := Ideal => f -> (
    -- First find the ideal in K[T_Y] of image of the map from T_X to T_Y The
    -- map K[T_Y] -> K[T_X] is given by t_i mapsto prod_j t_j^{a_ij}, where 
    -- A = matrix(f), and the ideal is the kernel of this, which is generated
    -- by t^u - t^v where u-v lies in ker(A^T) (We just list the vectors u-v
    -- generating this ideal)
    R := ring target f;
    kernelGenerators := kernelLLL transpose matrix f;
    if rank source kernelGenerators === 0 then return ideal (0_R);
    -- Then map this to the Cox ring, using the isomorphism K[T] cong
    -- (Cox_prod x_i)_0. We have to make the substitutions, and clear
    -- denominators, and then saturate by the product of the variables. The
    -- map sends t_i to prod_j x_j^{(v_j)_i}, where v_i is the first lattice
    -- point on the ray of Sigma.
    raysY := matrix rays target f;
    binomialExps := entries transpose (raysY * kernelGenerators);
    I := ideal apply(binomialExps, u -> (
	    posMonomial := 1_R;
	    negMonomial := 1_R;
	    apply(#u, i -> if u_i > 0 then posMonomial = posMonomial * R_i^(u_i) 
		else if u_i < 0 then negMonomial = negMonomial * R_i^(-u_i)
		);    
    	    posMonomial - negMonomial
    	    )
	);
    scan(gens R, r -> I = saturate(I, r));
    I
    )

weilDivisorGroup ToricMap := Matrix => (cacheValue symbol weilDivisorGroup) (f -> (
    X := source f;
    Y := target f;
    map(weilDivisorGroup X, weilDivisorGroup Y,
	transpose matrix apply(# rays Y, i -> entries pullback (f, Y_i)))))

classGroup ToricMap := Matrix => (cacheValue symbol classGroup) (f -> (
    X := source f;
    Y := target f;
    divisorMap := weilDivisorGroup f;
    map(classGroup X, classGroup Y,
	transpose ((transpose (fromWDivToCl(X) * divisorMap)) // transpose fromWDivToCl(Y)))))

-- Given ToricMap f: X -> Y, with smooth Y, returns a map Cl Y -> Cl X
cartierDivisorGroup ToricMap := Matrix => (cacheValue symbol cartierDivisorGroup) (f -> (
    X := source f;
    Y := target f;
    CDX := cartierDivisorGroup X;
    CDY := cartierDivisorGroup Y;
    map(CDX, CDY,
        transpose matrix apply(numgens CDY, i ->
            entries pullback (f, toricDivisor(flatten entries (fromCDivToWDiv(Y)*CDY_i),Y))))))

-- Given ToricMap f: X -> Y, with smooth Y, returns a map Pic Y -> Pic X
picardGroup ToricMap := Matrix => (cacheValue symbol picardGroup) (f -> (
    X := source f;
    Y := target f;
    divisorMap := cartierDivisorGroup f;
    map(classGroup X, classGroup Y,
	transpose ((transpose (fromCDivToPic(X) * divisorMap)) // transpose fromCDivToPic(Y)))))

------------------------------------------------------------------------------
------------------------------------------------------------------------------
-- DOCUMENTATION
------------------------------------------------------------------------------
------------------------------------------------------------------------------
beginDocumentation()

doc ///
    Key
        ToricMaps
    Headline
        routines for working with torus-equivariant maps between normal toric varieties
    Description
        Text
            Let $X$ and $Y$ be normal toric varieties whose underlying lattices
	    are $N_X$ and $N_Y$ respectively.  A toric map is a morphism $f :
	    X \to Y$ that induces a morphism of algebraic groups $g : T_X \to
	    T_Y$ such that $f$ is $T_X$-equivariant with respect to the
	    $T_X$-action on $Y$ induced by $g$.  Every toric map $f : X \to Y$
	    corresponds to a unique linear map from the rational vector space
	    containing the fan of $X$ to the rational vector space containing
	    the fan of $Y$.  Moreover, this linear map induces a map $f_N :
	    N_X \to N_Y$ between the underlying lattices such that, for every
	    cone $\sigma$ in the fan of $X$, there is a cone in the fan of $Y$
	    that contains the image $f_N(\sigma)$. For details see Theorem 3.3.4
	    in Cox-Little-Schenck.

    	    This {\em Macaulay2} package is designed to introduce and develop
    	    toric maps.  When it stablizes, we expect it to be merged into the
    	    larger {\em NormalToricVarieties} package.
    SeeAlso
        NormalToricVariety
///

doc ///
    Key
        ToricMap
    Headline
        the class of all torus-equivariant maps between normal toric varieties
    Description
        Text
            Let $X$ and $Y$ be normal toric varieties whose underlying lattices
	    are $N_X$ and $N_Y$ respectively.  A toric map is a morphism $f :
	    X \to Y$ that induces a morphism of algebraic groups $g : T_X \to
	    T_Y$ such that $f$ is $T_X$-equivariant with respect to the
	    $T_X$-action on $Y$ induced by $g$.  Every toric map $f : X \to Y$
	    corresponds to a unique linear map from the rational vector space
	    containing the fan of $X$ to the rational vector space containing
	    the fan of $Y$.  Moreover, this linear map induces a map $f_N :
	    N_X \to N_Y$ between the underlying lattices such that, for every
	    cone $\sigma$ in the fan of $X$, there is a cone in the fan of $Y$
	    that contains the image $f_N(\sigma)$. For details see Theorem 3.3.4
	    in Cox-Little-Schenck.
	    
	    To specify a map of normal toric varieties, the target and source
	    normal toric varieties need to be specificied as well as a matrix
	    which maps $N_X$ into $N_Y$.
	Text
	    The basic constructor of a toric map is
	    @TO (map, NormalToricVariety, NormalToricVariety, Matrix)@.
    SeeAlso
        NormalToricVariety
	(id, NormalToricVariety)
	(isWellDefined, ToricMap)
///

doc ///
    Key
        (source, ToricMap)
    Headline
        gets the source of the map
    Usage
    	X = source f
    Inputs
    	f : ToricMap
    Outputs
    	X : NormalToricVariety
    	    that is the source of the map f
    Description
        Text
	    Given a toric map $f : X \to Y$, this method returns $X$.  Since
	    this is a defining attribute of a toric map, no computation is
	    required.
       	Text
	    We illustrate how to access this basic feature of a toric map with
	    the projection from the second Hirzebruch surface to the
	    projective line.
    	Example  
	    X = hirzebruchSurface 2;
            Y = toricProjectiveSpace 1;
            f = map(Y, X, matrix {{1, 0}})
	    assert isWellDefined f
     	    source f
	    assert (source f === X)   
	Text
	    In a well-defined toric map, the number of columns in the
	    underlying matrix equals the dimension of the source.	    
	Example
	    assert (numColumns matrix f == dim X)
    SeeAlso
        (target, ToricMap)    
	(isWellDefined, ToricMap)
        (matrix, ToricMap)    	
        (map, NormalToricVariety, NormalToricVariety, Matrix)    		
///

doc ///
    Key
	(target, ToricMap)
    Headline 
    	gets the target of the map
    Usage
    	Y = target f
    Inputs
    	f : ToricMap
    Outputs
    	Y : NormalToricVariety
    	    that is the target of the map f	
    Description	    
        Text
	    Given a toric map $f : X \to Y$, this method returns $Y$.  Since
	    this is a defining attribute of a toric map, no computation is
	    required.    
       	Text
	    We illustrate how to access this basic feature of a toric map with
	    the projection from the second Hirzebruch surface to the
	    projective line.
    	Example  
	    X = hirzebruchSurface 2;
            Y = toricProjectiveSpace 1;
            f = map(Y, X, matrix {{1, 0}})
	    assert isWellDefined f
     	    target f
	    assert (target f === Y)   
	Text
	    In a well-defined toric map, the number of rows in the
	    underlying matrix equals the dimension of the target.	    
	Example
	    assert (numRows matrix f == dim Y)
    SeeAlso
        (source, ToricMap)    
	(isWellDefined, ToricMap)
        (matrix, ToricMap)    	
        (map, NormalToricVariety, NormalToricVariety, Matrix)    		    
///	  

doc ///
    Key
	(matrix, ToricMap)
    Headline 
    	gets the underlying map of lattices for a toric map
    Usage
    	g = matrix f
    Inputs
    	f : ToricMap
	Degree =>
	    unused
    Outputs
    	g : Matrix
    	    over the @TO2 (ZZ, "integers")@
    Description	    
        Text
	    Every toric map $f : X \to Y$ corresponds to a unique map of
	    lattices $g : N_X \to N_Y$ such that, for every cone $\sigma$ in
	    the fan of $X$, there is a cone in the fan of $Y$ that contains
	    the image $g(\sigma)$.  This method returns an integer matrix
	    representing $g$.	    
       	Text
	    We illustrate how to access this basic feature of a toric map with
	    the projection from the second Hirzebruch surface to the
	    projective line.
    	Example  
	    X = hirzebruchSurface 2;
            Y = toricProjectiveSpace 1;
            f = map(Y, X, matrix {{1, 0}})
	    assert isWellDefined f
     	    g = matrix f
	    assert (ring g === ZZ)
	Text
	    In a well-defined toric map, the number of rows in the underlying
	    matrix must equal the dimension of the target and the number of
	    columns must equal the dimension of the source.	    
	Example
	    assert (numColumns g == dim X)
	    assert (numRows g == dim Y)	    
	Text
	    The output display for toric maps is inherited the underlying map
	    of lattices.
	Example
	    code (net, ToricMap)
    SeeAlso
        (source, ToricMap)    
        (target, ToricMap)    		
	(isWellDefined, ToricMap)
        (map, NormalToricVariety, NormalToricVariety, Matrix)    		    
///	         


undocumented { (net,ToricMap) }

doc ///
    Key
        (isWellDefined, ToricMap)
    Headline 
        whether a toric map is well defined 
    Usage 
        isWellDefined f
    Inputs 
        f : ToricMap
    Outputs 
        : Boolean 
	    that is true if the underlying linear map determines a toric map
    Description
        Text	
	    Let $X$ and $Y$ be normal toric varieties whose underlying
	    lattices are $N_X$ and $N_Y$ respectively.  Every toric map 
	    $f : X \to Y$ corresponds to a unique map $f_N : N_X \to N_Y$ of
	    lattices such that, for any cone $\sigma$ in the fan of $X$, there
	    is a cone in the fan of $Y$ that contains the image $f_N(\sigma)$.	
	    This method determines whether the underlying map of lattices
	    defines a toric map by checking that the image of each maximal
	    cone from the source fan is contained in a maximal cone of the
	    target fan. For details see Theorem 3.3.4 in Cox-Little-Schenck.
    	Text
            The first example illustrates the projection from the Hirzebruch
            surface to the projective line is well defined.
    	Example  
	    X = hirzebruchSurface 2;
            Y = toricProjectiveSpace 1;
            f = map (Y, X, matrix {{1, 0}})
	    source f
	    target f
	    matrix f
    	    assert isWellDefined f 
	    assert (source f === X)
	    assert (target f === Y)
	    assert (matrix f === matrix {{1, 0}})
	Text
	    The second example illustrates two attempts to define a toric map
	    from the projective plane to a weighted projective space. The
	    first, corresponding to the identity on the lattices, is not
	    well-defined.  The second, corresponding to a stretch in the
	    lattices, is well-defined.  By making the current debugging level
	    greater than one, one gets some addition information about the
	    nature of the failure.
	Example
	    debugLevel = 1;	
	    Z = toricProjectiveSpace 2;
	    W = weightedProjectiveSpace {1, 1, 2};
	    g = map (W, Z, 1)
	    assert not isWellDefined g 
	    h = map (W, Z, matrix {{1, 0}, {0, 2}})
            assert isWellDefined h
    	Text
            This method also checks the following aspects of the data
            structure:	    
	Text
    	    @UL {
	        {"the underlying ", TO HashTable, " has the expected keys,
	    	    namely ", TT "source", ", ", TT "target", ", ", 
		    TT "matrix", ", and ", TT "cache", ","},
       	        {"the value of the ", TT "source", " key is a ", 
		    TO NormalToricVariety, ","},
       	        {"the value of the ", TT "target", " key is a ", 
		    TO NormalToricVariety, ","},
       	        {"the value of the ", TT "matrix", " key is a ", 
		    TO Matrix, ","},
       	        {"the underling ring of the ", TT "matrix", " is ", 
		    TO ZZ, ","},
       	        {"the rank of the source of the ", TT "matrix", " equal
		    dimension of the ", TT "source", " variety,"},
       	        {"the rank of the target of the ", TT "matrix", " equal
		    dimension of the ", TT "target", " variety,"},		    
                {"the value of the ", TT "cache", " key is a ", 
		    TO CacheTable, "."}
	    }@	    
    SeeAlso
    	(map, NormalToricVariety, NormalToricVariety, Matrix)
    	(hirzebruchSurface, ZZ)
        (toricProjectiveSpace, ZZ)
        (weightedProjectiveSpace, List)
///
    
doc ///
    Key
        (map, NormalToricVariety, NormalToricVariety, Matrix)
    Headline 
    	make a torus-equivariant map between normal toric varieties
    Usage 
        f = map(Y, X, g)
    Inputs 
        Y : NormalToricVariety
	    the target of the map
	X : NormalToricVariety
	    the source of the map
	g : Matrix
	    over the integers
	Degree => 
	    used
	DegreeLift =>   
	    used
	DegreeMap =>
	    used
    Outputs 
        f : ToricMap
    Description
        Text
	    Let $X$ and $Y$ be normal toric varieties whose underlying
	    lattices are $N_X$ and $N_Y$ respectively.  Every toric map 
	    $f : X \to Y$ corresponds to a unique map $g : N_X \to N_Y$ of
	    lattices such that, for any cone $\sigma$ in the fan of $X$, there
	    is a cone in the fan of $Y$ that contains the image $g(\sigma)$.	
    	    Given the target, the source, and the matrix representing lattice
    	    map, this basic constructor creates the corresponding toric map.
	    For details see Theorem 3.3.4 in Cox-Little-Schenck.
    	Text
	    This first example constructs the projection from the second
	    Hirzebruch surface to the projective line.
    	Example  
	   X = hirzebruchSurface 2
           Y = toricProjectiveSpace 1
           f = map (Y, X, matrix {{1, 0}})
	   assert isWellDefined f
    	   assert (source f === X)
	   assert (target f === Y)
	   assert (matrix f === matrix {{1, 0}})
	Text
	    The second example illustrates that the map from the blow-up of
	    the origin of affine 2-space to affine 2-space is proper.
	Example
	   A = affineSpace 2;
	   max A
	   B = toricBlowup ({0, 1}, A);
	   g = map(A, B, matrix {{1, 0}, {0, 1}})
	   assert isWellDefined g
    	   assert (source g === B)
	   assert (target g === A)
	   assert (matrix g === id_(ZZ^2))	   
    Caveat
        This method does not check that the given matrix determines a map of
        toric varieties. In particular, it assumes that the image of each cone
	in the source is contained in a cone in the target. One can verify this
	by using @TO (isWellDefined, ToricMap)@.
    SeeAlso
    	(source, ToricMap)
	(target, ToricMap)
	(matrix, ToricMap)
        (map, NormalToricVariety, NormalToricVariety, ZZ)
/// 

doc ///
    Key
        (map, NormalToricVariety, NormalToricVariety, ZZ)
    Headline 
    	make a torus-equivariant map between normal toric varieties
    Usage 
        f = map(Y, X, m)
    Inputs 
        Y : NormalToricVariety
	    the target of the map
	X : NormalToricVariety
	    the source of the map
	m : ZZ
	Degree => 
	    used
	DegreeLift =>   
	    used
	DegreeMap =>
	    used
    Outputs 
        f : ToricMap
    Description
        Text
	    Every toric map $f : X \to Y$ corresponds to a unique map 
	    $g : N_X \to N_Y$ of lattices such that, for any cone $\sigma$ in
	    the fan of $X$, there is a cone in the fan of $Y$ that contains
	    the image $g(\sigma)$.  Given the target, the source, and an
	    integer, this basic constructor creates the corresponding toric
	    map.  The given integer determines the lattice map in two distinct
	    ways.	    
	Text	    
	    When the integer equals zero, the underlying map of lattices is
	    represented by the zero matrix.
	Example
	    X = hirzebruchSurface 2;
	    Y = toricProjectiveSpace 1;
	    f = map(Y, X, 0)
	    assert isWellDefined f
	    assert (source f === X)
	    assert (target f === Y)
	    assert (matrix f === map(ZZ^(dim Y), ZZ^(dim X), 0))
    	Text	    	
	    If the integer $m$ is nonzero, then the underlying map of lattices
	    is represented by multiplying the identity matrix by the given
	    integer $m$.  Hence, this second case requires that the dimension
	    of the source and target be equal.
	Example
	    Z = normalToricVariety ({{1,0},{-1,2},{0,-1}}, {{0,1},{0,2},{1,2}});
	    assert isWellDefined Z
	    g = map(Z, X, 2)
	    assert isWellDefined g
	    assert (source g === X)
	    assert (target g === Z)
	    assert (matrix g === 2*id_(ZZ^(dim X)))	    
    	Text
	    Setting the integer equal to $1$ yields a easy way to construct
	    the canoncal toric map associated to a blowup or the identity map.
	Example
	    A = affineSpace 2;
	    B = toricBlowup ({0, 1}, A);
	    h = map(A, B, 1)
	    assert isWellDefined h
    	    assert (source h === B)
	    assert (target h === A)
	    assert (matrix h === id_(ZZ^2))	 	    
	    id_A
	    assert isWellDefined id_A
	    assert (source id_A === A)
	    assert (target id_A === A)	    
	    assert (matrix id_A === id_(ZZ^(dim A)))	    	    
	    assert (id_A === map(A,A,1))
    Caveat
        This method does not check that the given matrix determines a map of
        toric varieties. In particular, it assumes that the image of each cone
	in the source is contained in a cone in the target. One can verify this
	by using @TO (isWellDefined, ToricMap)@.
    SeeAlso
    	(source, ToricMap)
	(target, ToricMap)
	(matrix, ToricMap)
        (map, NormalToricVariety, NormalToricVariety, ZZ)
/// 

doc ///
    Key
        (id, NormalToricVariety)
    Headline
    	makes the identity map from a NormalToricVariety to itself
    Usage 
        id_X
    Inputs 
        X : NormalToricVariety
    Outputs 
        : ToricMap
    Description
        Text	    
	    For the identity map on a normal toric variety, the underlying map
	    of lattices is given by the identity matrix. For details see Theorem 3.3.4
	    in Cox-Little-Schenck.
	Example
	    X = hirzebruchSurface 2;
	    f = id_X
	    assert isWellDefined f
	    assert (source f === X)
	    assert (target f === X)
	    assert (matrix f === id_(ZZ^(dim X)))	    
    SeeAlso
        (map, NormalToricVariety, NormalToricVariety, ZZ)
        (map, NormalToricVariety, NormalToricVariety, Matrix)	 
///    

doc ///
    Key
        (isDominant, ToricMap)
	isDominant
    Headline
        whether a toric map is dominant
    Usage
        isDominant f
    Inputs
        f:ToricMap
    Outputs
        :Boolean
	    that is true if the map is dominant
    Description
        Text
	    A morphism of varieties is dominant if the image is dense. For a
	    toric map, it suffices to check that the dimension of the image
	    is the dimension of the target.
	Text
	    This example illustrates that from affine 3-space to projective 3-space.
	Example
	    PP3 = toricProjectiveSpace 3
	    AA3 = affineSpace 3
	    f = map(PP3, AA3, id_(ZZ^3))
	    assert isWellDefined f
	    assert isDominant f
	    assert not isSurjective f
	Text
	    To improve computation speed, the package caches this test in the
	    @TO CacheTable@ of the toric map.
    SeeAlso
	(map, NormalToricVariety, NormalToricVariety, Matrix)
	(map, NormalToricVariety, NormalToricVariety, ZZ)
	(isComplete, NormalToricVariety)
///

doc ///
    Key
        (isProper, ToricMap)
    	isProper	
    Headline 
        whether a toric map is proper
    Usage 
        isProper f
    Inputs 
        f:ToricMap
    Outputs 
        :Boolean 
	    that is true if the map is proper
    Description
        Text
	    A morphism of varieties is proper if it is universally closed.
	    For a toric map $f : X \to Y$ corresponding to the map 
	    $f_N : N_X \to N_Y$ of lattices, this is equivalent to the
	    preimage of the support of the target fan under $f_N$ being equal
	    to the support of the source fan. For the details, see Theorem
	    3.4.11 in Cox-Little-Schenck.
    	Text
	    The first example illustrates that the projection from the second
	    Hirzebruch surface to the projective line is proper.
    	Example  
	    X = hirzebruchSurface 2;
            Y = toricProjectiveSpace 1
            f = map (Y, X, matrix {{1,0}})
	    assert isWellDefined f
    	    assert isProper f 
	Text
	    This example illustrates that the map from the blow-up of the origin of 
	    affine 2-space to affine 2-space is proper.
	Example
	    A = affineSpace 2;
	    B = toricBlowup({0,1}, A);
	    g = map(A, B, 1)
	    assert isWellDefined f
            assert isProper g
	Text
	    To improve computation speed, the package caches this test in the
	    @TO CacheTable@ of the toric map.
    SeeAlso
    	(map, NormalToricVariety, NormalToricVariety, Matrix)
    	(map, NormalToricVariety, NormalToricVariety, ZZ)	
        (isComplete, NormalToricVariety)
/// 


doc ///
    Key
        (isFibration, ToricMap)
	isFibration
    Headline 
        whether a toric map is a fibration
    Usage 
        isFibration f
    Inputs 
        f:ToricMap
    Outputs 
        :Boolean 
	    that is true if the map is a fibration
    Description
        Text
	    A proper morphism $f : X\to Y$ is a fibration if $f_*(OO_X) = OO_Y$.
	    A proper toric map is a fibration if and only if the underlying map
	    of lattices is a surjection. For the details, see Proposition 2.1 in
	    de Cataldo-Migliorini-Mustata, "The combinatorics and topology of proper toric maps"
	    @HREF("https://arxiv.org/abs/1407.3497", "arXiv:1407.3497")@.
	Text
	    The first example shows that the projection from the first
	    Hirzebruch surface to the projective line is a fibration.
	Example
	    X = hirzebruchSurface 1;
	    Y = toricProjectiveSpace 1;
	    f = map(Y,X,matrix{{1,0}})
	    assert isWellDefined f
	    isFibration f
	Text
	    Here is an example of a proper map which is not a fibration.
	Example
	    Z = weightedProjectiveSpace {1,1,2};
	    g = map(Z,X,matrix{{1,0},{0,-2}})
	    isWellDefined g
	    isFibration g
	    isProper g
    SeeAlso
        (isProper, ToricMap)
/// 

doc ///
    Key
        (pullback, ToricMap, Module)
        (pullback, ToricMap, CoherentSheaf)
    Headline
        compute the pullback of a module or coherent sheaf under a toric map
    Usage
        M' = pullback(f, M)
        F' = pullback(f, F)
    Inputs
        f : ToricMap
	    in which the target is assumed to be smooth
	M : Module
	    a module, or coherent sheaf, on the target of f
    Outputs
        M' : Module
	    the pullback of M under f, or {\tt F'} the associated @TO CoherentSheaf@
    Description
        Text
            If $Y$ is a normal toric variety and $R$ is its Cox ring, then any 
	    finitely-generated $R$-module $M$ determines a coherent sheaf $F_M$
	    on $Y$. If $f: X \to Y$ is a toric morphism with $Y$ smooth, then 
	    $f$ induces a map of Cox rings and the pullback $f^*F_M$ is represented
	    by the pullback of $M$ to the Cox ring of $X$. See "Cox Rings and
	    Algebraic Maps" by Mandziuk, Thm 3.2.
	Text
	    We compute the pullback of the structure sheaf of the projective plane
	    twisted by a divisor to the Hirzebruch surface.
	Example
	    X = hirzebruchSurface 1
	    PP2 = toricProjectiveSpace 2
	    f = map(PP2, X, matrix{{1,0},{0,-1}})
	    assert isWellDefined f
	    OD = OO toricDivisor({1,2,3}, PP2)
	    pullback(f, OD)
	Text
	    We can also pull back modules on the Cox ring.
	Example
	    S = ring PP2
	    R = ring X
	    M = module OD
	    pullback(f, M)
    Caveat
    	This function assumes that the target of f is smooth. This can be
	checked with the command @TO (isSmooth, NormalToricVariety)@.
    SeeAlso
	(symbol SPACE, OO, ToricDivisor)
        (pullback, ToricMap, ToricDivisor)
        "Total coordinate rings and coherent sheaves"
///

doc ///
    Key
	pullback
        (pullback, ToricMap, ToricDivisor)
    Headline
        compute the pullback of a Cartier divisor under a toric map
    Usage
        pullback(f, D)
    Inputs
        f : ToricMap
	D : ToricDivisor
	    a Cartier divisor on the target of f
    Outputs
        : ToricDivisor
	    the pullback of D under f
    Description
        Text
            Torus-invariant Cartier divisors pull back under a toric map by
	    composing the toric map with the support function of the divisor.
    	Text
	    In the first example, we consider the projection from a product of
	    two projective lines onto the first factor. The pullback of a point
	    is just a fibre in the product.
	Example
            PP1 = toricProjectiveSpace 1;
            X = PP1 ** PP1
            f = map(PP1, X, matrix{{1,0}})
	    assert isWellDefined f
	    D = toricDivisor({1,1}, PP1)
	    pullback(f, D)
	Text
	    This example illustrates that the pullback of a line through the
	    origin in affine 2-space under the blowup map is a line together
	    with the exceptional divisor.
	Example
	    AA2 = affineSpace 2;
	    max AA2
	    BlO = toricBlowup({0,1}, AA2)
	    f = map(AA2, BlO, 1)
	    assert isWellDefined f
	    rays AA2
	    DAA2=toricDivisor({1,0},AA2)
            pullback(f, DAA2)
       Text
           See Theorem 4.2.12.b and Proposition 6.2.7 in Cox-Little-Schenck for
           more information.
    SeeAlso
        (isCartier, ToricDivisor)
	(toricBlowup, List, NormalToricVariety)
        (pullback, ToricMap, Module)
        (pullback, ToricMap, CoherentSheaf)
///

doc ///
    Key
    	(ideal, ToricMap)
    Headline
    	make the ideal defining the closure of the image 
    Usage
    	ideal f
    Inputs
    	f : ToricMap
    Outputs
    	: Ideal
	    in the homogeneous coordinate ring (a.k.a. Cox ring) of the target
    Description
    	Text
	    The closure of image of the map $f$ lies in the target of $f$. This
	    closed subvariety defined by a saturated homogeneous ideal in the
	    total coordinate ring (a.k.a. Cox ring) of the target of f (see
	    "The homogeneous coordinate ring of a toric variety, revised version"
	    by Cox, Proposition 2.4).  This function returns that ideal.
	Text
	    The closure of the image of a distinguished affine open set
	    in the projective plane is the entire plane.
	Example
	    AA2 = affineSpace 2;
	    PP2 = toricProjectiveSpace 2;
	    f = map(PP2, AA2, 1)
	    assert isWellDefined f
	    R = ring PP2;
	    I = ideal f
	    assert isHomogeneous I
	Text
	    The twisted cubic curve is the image of a map from the projective
	    line to the projective $3$-space.
	Example
	    PP1 = toricProjectiveSpace 1;
	    PP3 = toricProjectiveSpace 3;
	    f = map(PP3, PP1, matrix{{1}, {2}, {3}})
	    assert isWellDefined f
	    S = ring PP3;
	    I = ideal f
	    assert isHomogeneous I
    	    assert (I == ker inducedMap f)
	    assert (I == minors(2, matrix{{S_0,S_1,S_2},{S_1,S_2,S_3}}))
    SeeAlso
    	(inducedMap, ToricMap)
        (ring, NormalToricVariety)
///

doc ///
    Key
        (inducedMap, ToricMap)
    Headline
        make the induced map between the Cox rings of the source and target
    Usage
        inducedMap f
    Inputs
        f : ToricMap
	    in which the target is assumed to be smooth
	Degree =>
	    unused
	Verify =>
	    unused
    Outputs
        : RingMap
	    between the total homogeneous coordinate rings (aka Cox rings)
    Description
        Text
	    Given a toric map, there is an induced map between the Cox rings
	    as in "Cox Rings and Algebraic Maps" by Mandziuk, Thm 2.10; see
	    @HREF("https://arxiv.org/abs/1703.04794",
	    "arXiv:1703.04794")@. This function returns that map.
	Text
	    In the first example we compute the map on the coordinate rings
	    induced by the map from $\mathbb A^2\to\mathbb P^2$. The map sends
	    one generator of $S$ to 1 and the other two to the generators of $R$.
	Example
	    AA2 = affineSpace 2;
	    PP2 = toricProjectiveSpace 2;
	    f = map(PP2, AA2, 1)
	    assert isWellDefined f
	    R = ring AA2;
	    S = ring PP2;
	    f' = inducedMap f
	    f' vars S
	Text
	    In the second example we consider the map from a Hirzebruch surface
	    to $\mathbb P^1$.
	Example
	    H = hirzebruchSurface 3;
	    PP1 = toricProjectiveSpace 1;
	    g = map(PP1, H, matrix {{1,0}})
    	    assert isWellDefined g
	    R = ring H;
	    S = ring PP1;
	    g' = inducedMap g
	    g' vars S
	Text
	    Note that the induced map on Cox rings preserves the grading on the
	    generators. This is done by computing the induced map on the class
	    group of the source and target of the toric map and setting the
	    appropriate DegreeMap on the induced map on Cox rings.
    Caveat
    	This method implicitly assumes that the target is smooth. One may
	verify this with the command @TO (isSmooth, NormalToricVariety)@.
    SeeAlso
	(ring, NormalToricVariety)
        (classGroup, ToricMap)
	(pullback, ToricMap, ToricDivisor)
        "Total coordinate rings and coherent sheaves"
///

doc ///
    Key
    	(symbol *, ToricMap, ToricMap)
    Headline
    	make the composition of two toric maps
    Usage
    	g * f
    Inputs
    	f : ToricMap
	    a toric map between toric varieties
	g : ToricMap
	    a toric map between toric varieties
    Outputs
    	: ToricMap
	    the composition g*f from source f to target g
    Description
    	Text
	    Given two toric maps with the target of f equal to the source of
	    g, this function returns the toric map from source f to
	    target g that is the composition of g and f.
	Example
	    PP1 = toricProjectiveSpace 1
	    X = PP1**PP1
	    Y = toricBlowup({0,2}, X)
	    f = map(X,Y,1)
	    assert isWellDefined f
	    g = map(PP1,X,matrix{{1,0}})
	    assert isWellDefined g
	    h = g*f
	    source h
	    target h
///	

doc ///
    Key
        (isSurjective, ToricMap)
    Headline 
        whether a toric map is surjective
    Usage 
        isSurjective f
    Inputs 
        f : ToricMap
    Outputs 
        : Boolean 
	    that is true if the map is surjective
    Description
        Text
	    A morphism $f : X\to Y$ is surjective if $f(X) = Y$ as sets. 
	    A toric morphism is surjective if the induced map of fans is 
	    surjective.
	Text
	    Projections are surjective.
	Example
	    X = toricProjectiveSpace 2
	    Y = hirzebruchSurface 2
	    XY = X ** Y
	    p1 = map(X,XY, matrix{{1,0,0,0},{0,1,0,0}})
	    assert isWellDefined p1
	    p2 = map(Y,XY, matrix{{0,0,1,0},{0,0,0,1}})
	    assert isWellDefined p2
	    isSurjective p1
	    isSurjective p2
	Text
	    Blowdowns are surjective.
	Example	
    	    X = affineSpace 2
	    Y = toricBlowup({0,1},X)
	    f = map(X,Y,matrix{{1,0},{0,1}})
	    assert isWellDefined f
	    isSurjective f
	Text
	    Inclusion of an affine open into a blowup is not surjective.
	Example
	    X = affineSpace 2
	    Y = toricBlowup({0,1},X) 
	    f = map(Y,X,matrix{{1,0},{1,1}})
	    assert isWellDefined f
	    isSurjective f
    SeeAlso
        (ToricMap)
/// 

doc ///
    Key
        (weilDivisorGroup, ToricMap)
    Headline
        make the induced map between the corresponding groups of torus-invariant Weil divisors.
    Usage
        weilDivisorGroup f
    Inputs
        f : ToricMap
	    in which the target is assumed to be smooth
    Outputs
        : Matrix
	    representing the map of abelian groups between the corresponding
	    groups of torus-invariant Weil divisors
    Description
        Text
	    Given a toric map $f : X \to Y$ with Y a smooth toric variety,
            this method returns the induced map of abelian groups from
            the group of torus-invariant Weil divisors on $Y$ to
            the group of torus-invariant Weil divisors on $X$.
            For general (toric) varieties, {\tt weilDivisorGroup} is not a functor.
            However, {\tt weilDivisorGroup} gives a contravariant functor on the
            category of smooth normal toric varieties.
	Text
	    Our first example produces the induced map from the group of
            torus-invariant Weil divisors on the projective line to the group of
            torus-invariant Weil divisors on the first Hirzebruch surface.
	Example
	    X = hirzebruchSurface 1;
	    Y = toricProjectiveSpace 1;
	    f = map(Y, X, matrix {{1, 0}})
	    assert isWellDefined f
	    f' = weilDivisorGroup f
	    assert (source f' == weilDivisorGroup Y)
	    assert (target f' == weilDivisorGroup X)
	Text
	    The next example gives the induced map from the group of
            torus-invariant Weil divisors on the projective plane to the group
            of torus-invariant Weil divisors on the first Hirzebruch surface.
	Example
	    nefGenerators X
	    Z = toricProjectiveSpace 2;
	    g = map(Z, X, matrix {{1, 0}, {0,-1}})
	    assert isWellDefined g
	    g' = weilDivisorGroup g
	    assert (source g' == weilDivisorGroup Z)
	    assert (target g' == weilDivisorGroup X)
        Text
            The next example demonstrates that the induced map on the group of
            torus-invariant Weil divisors is compatible with the induced map
            on the class group.
        Example
            gPic = classGroup g
            assert(gPic * fromWDivToCl(Z) == fromWDivToCl(X) * g')
    SeeAlso
        (weilDivisorGroup, NormalToricVariety)
        (classGroup, ToricMap)
        (pullback, ToricMap, ToricDivisor)
///
   
doc ///
    Key
        (classGroup, ToricMap)
    Headline 
        make the induced map between the corresponding class groups
    Usage 
        classGroup f
    Inputs 
        f : ToricMap
	    in which the target is assumed to be smooth
    Outputs 
        : Matrix 
	    representing the map of abelian groups between the corresponding
	    class groups
    Description
        Text
	    Given a toric map $f : X \to Y$ with Y a smooth toric variety,
            this method returns the induced
            map of abelian groups from the class group of $Y$ to the class
	    group of $X$.  For general (toric) varieties, {\tt classGroup}
            is not a functor. However, {\tt classGroup} gives a contravariant
            functor on the category of smooth normal toric varieties.
	Text
	    Our first example produces the induced map from the class group of
	    the projective line to the class group of the first Hirzebruch
	    surface.
	Example
	    X = hirzebruchSurface 1;
	    Y = toricProjectiveSpace 1;
	    f = map(Y, X, matrix {{1, 0}})
	    assert isWellDefined f
	    f' = classGroup f
	    assert (source f' == classGroup Y)
	    assert (target f' == classGroup X) 
	Text
	    The next example gives the induced map from the class group of the
	    projective plane to the class group of the first Hirzebruch surface.
	Example
	    nefGenerators X
	    Z = toricProjectiveSpace 2;
	    g = map(Z, X, matrix {{1, 0}, {0,-1}})
	    assert isWellDefined g
	    g' = classGroup g
	    assert (source g' == classGroup Z)
	    assert (target g' == classGroup X) 	    
    SeeAlso
        (classGroup, NormalToricVariety)
        (weilDivisorGroup, ToricMap)
        (picardGroup, ToricMap)
        (pullback, ToricMap, ToricDivisor)
///

doc ///
    Key
        (picardGroup, ToricMap)
    Headline
        make the induced map between the corresponding Picard groups
    Usage
        picardGroup f
    Inputs
        f : ToricMap
    Outputs
        : Matrix
	    representing the map of abelian groups between the corresponding
	    Picard groups
    Description
        Text
	    Given a toric map $f : X \to Y$, this method returns the induced
	    map of abelian groups from the Picard group of $Y$ to the Picard
	    group of $X$.  In other words, {\tt picardGroup} is a contravariant
	    functor on the category of normal toric varieties.
	Text
	    Our first example produces the induced map from the Picard group of
	    the projective line to the Picard group of the first Hirzebruch
            surface.
	Example
	    X = hirzebruchSurface 1;
	    Y = toricProjectiveSpace 1;
	    f = map(Y, X, matrix {{1, 0}})
	    assert isWellDefined f
	    f' = picardGroup f
	    assert (source f' == picardGroup Y)
	    assert (target f' == picardGroup X)
	Text
	    The next example gives the induced map from the Picard group of the
	    projective plane to the Picard group of the first Hirzebruch
	    surface.
	Example
	    nefGenerators X
	    Z = toricProjectiveSpace 2;
	    g = map(Z, X, matrix {{1, 0}, {0,-1}})
	    assert isWellDefined g
	    g' = picardGroup g
	    assert (source g' == picardGroup Z)
	    assert (target g' == picardGroup X)
    SeeAlso
        (picardGroup, NormalToricVariety)
        (cartierDivisorGroup, ToricMap)
        (classGroup, ToricMap)
        (pullback, ToricMap, ToricDivisor)
///

doc ///
    Key
        (cartierDivisorGroup, ToricMap)
    Headline
        make the induced map between the corresponding groups of torus-invariant Cartier divisors.
    Usage
        cartierDivisorGroup f
    Inputs
        f : ToricMap
    Outputs
        : Matrix
	    representing the map of abelian groups between the corresponding
	    groups of torus-invariant Cartier divisors
    Description
        Text
	    Given a toric map $f : X \to Y$, this method returns the induced
	    map of abelian groups from the group of torus-invariant Cartier
            divisors on $Y$ to the group of torus-invariant Cartier divisors
            on $X$. In other words, {\tt cartierDivisorGroup} is a contravariant
	    functor on the category of normal toric varieties.
	Text
	    Our first example produces the induced map from the group of
            torus-invariant Cartier divisors on the projective line to the group
            of torus-invariant Cartier divisors on the first Hirzebruch surface.
	Example
	    X = hirzebruchSurface 1;
	    Y = toricProjectiveSpace 1;
	    f = map(Y, X, matrix {{1, 0}})
	    assert isWellDefined f
	    f' = cartierDivisorGroup f
	    assert (source f' == cartierDivisorGroup Y)
	    assert (target f' == cartierDivisorGroup X)
	Text
	    The next example gives the induced map from the group of
            torus-invariant Cartier divisors on the projective plane to the group
            of torus-invariantCartier divisors on the first Hirzebruch surface.
	Example
	    nefGenerators X
	    Z = toricProjectiveSpace 2;
	    g = map(Z, X, matrix {{1, 0}, {0,-1}})
	    assert isWellDefined g
	    g' = cartierDivisorGroup g
	    assert (source g' == cartierDivisorGroup Z)
	    assert (target g' == cartierDivisorGroup X)
        Text
            The next example demonstrates that the induced map on the group of
            torus-invariant Cartier divisors is compatible with the induced map
            on the Picard group
        Example
            gPic = picardGroup g
            assert(gPic * fromCDivToPic(Z) == fromCDivToPic(X) * g')
    SeeAlso
        (cartierDivisorGroup, NormalToricVariety)
        (picardGroup, ToricMap)
        (pullback, ToricMap, ToricDivisor)
///

    	

------------------------------------------------------------------------------
------------------------------------------------------------------------------
-- TESTS
------------------------------------------------------------------------------
------------------------------------------------------------------------------

-- test 0
TEST ///
--Tests for isWellDefined
--TODO: needs more tests
X = normalToricVariety({{1,0,0},{0,0,1},{0,0,-1}}, {{0,1},{0,2}});
Y = normalToricVariety({{0,-1}}, {{0}});
f = map(Y, X, matrix{{1,0,0}, {0,1,0}})
assert not isWellDefined f
///

TEST ///
--< Tests for isProper (see isProperPics.pdf) >--
--The source and target are proper then the map is proper
FF2 = hirzebruchSurface 2
PP1 = toricProjectiveSpace 1
f = map(PP1, FF2, matrix{{1,0}})
assert isWellDefined f
assert isProper f
assert isProper(f,1)
///

TEST ///
--The source not proper but the target is so the map is not proper
FF2 = hirzebruchSurface 2
PP1 = toricProjectiveSpace 1
Y = normalToricVariety(rays FF2, drop(max FF2, -1))
f = map(PP1, Y, matrix{{1,0}})
assert isWellDefined f
assert not isProper f
assert not isProper(f,2)
g = map(Y, PP1, matrix{{0},{1}})
assert isWellDefined g
assert isProper g
assert isProper(g,3)
///

TEST ///
--Test A: The source and target are both not proper but the map is proper
P1A1 = (affineSpace 1) ** (toricProjectiveSpace 1)
A1 = affineSpace 1
h = map(A1, P1A1, matrix{{1,0}})
assert isWellDefined h
assert isProper h
assert isProper(h,4)
///

TEST ///
--Test B
X = normalToricVariety({{1,0,0},{0,1,0},{0,0,1},{-1,0,0},{0,0,-1}},{{0,1},{1,2,3},{1,3,4}})
Y = (toricProjectiveSpace 1) ** (affineSpace 1)
f = map(Y,X,matrix{{1,0,0},{0,1,0}})
assert isWellDefined f
assert not isProper f
assert not isProper(f,5)
///

TEST ///
--Test C
X = normalToricVariety({{1,0,0},{0,1,0},{-1,0,0},{0,0,1},{0,0,-1}},{{0},{1,2,3},{1,2,4}})
Y = (toricProjectiveSpace 1) ** (affineSpace 1)
A = matrix{{1,0,0},{0,1,0}}
f = map(Y,X,A)
assert isWellDefined f
assert not isProper f
assert not isProper(f,6)
///

TEST ///
--Test D
X = normalToricVariety({{0,1},{1,0},{0,-1}},{{0,1},{1,2}})
Y = normalToricVariety({{-1,-1},{1,0},{0,1}},{{0,1},{1,2}})
A = id_(ZZ^2)
f = map(Y,X,A)
assert isWellDefined f
assert not isProper f
assert not isProper(f,7)
///

TEST ///
--Test D'
X = normalToricVariety({{0,1},{1,0},{0,-1},{-1,-1}},{{0,1},{1,2},{2,3}})
Y = normalToricVariety({{-1,-1},{1,0},{0,1}},{{0,1},{1,2}})
A = id_(ZZ^2)
f = map(Y,X,A)
assert isWellDefined f
assert isProper f
assert isProper(f,8)
///

TEST ///
--Test E
X = normalToricVariety({{1,0,0},{0,1,0},{-1,0,0},{0,0,1},{0,0,-1}},{{0,3},{1,2,3},{1,2,4}})
Y = normalToricVariety({{1,0},{0,1},{-1,0}},{{0},{1,2}})
A = matrix{{1,0,0},{0,1,0}}
f = map(Y,X,A)
assert isWellDefined f
assert not isProper f
assert not isProper(f,9)
///

TEST ///
--Test E'
X = normalToricVariety({{0,-1,0},{1,0,0},{0,1,0},{-1,0,0},{0,0,1},{0,0,-1}},{{0},{1,4},{1,5},{2,3,4},{2,3,5}})
Y = normalToricVariety({{0,-1},{1,0},{0,1},{-1,0}},{{0},{1},{2,3}})
A = matrix{{1,0,0},{0,1,0}}
f = map(Y,X,A)
assert isWellDefined f
assert not isProper f
assert not isProper(f,10)
///

TEST ///
--Test F
X'' = normalToricVariety({{1,0,0},{0,1,0},{-1,0,0},{0,0,1},{0,0,-1}},{{0,3},{0,4},{1,2,3},{1,2,4}})
Y' = normalToricVariety({{1,0},{0,1},{-1,0}},{{0},{1,2}})
A = matrix{{1,0,0},{0,1,0}}
f = map(Y',X'',A)
assert isWellDefined f
assert isProper f
assert isProper(f,11)
///

TEST ///
--Test G
X = normalToricVariety({{-1,1,0},{0,0,1},{0,0,-1}},{{0,1},{0,2}})
Y = normalToricVariety({{0,1},{1,0}},{{0,1}})
A = matrix{{1,1,0},{1,1,0}}
f = map(Y,X,A)
assert isWellDefined f
assert not isProper f
assert not isProper(f,12)
///

TEST ///
--Test H
X = normalToricVariety({{1,-1,0},{1,1,0},{-1,1,0},{0,0,1}},{{0,1,3},{1,2,3}})
Y = normalToricVariety({{0,1},{1,0}},{{0,1}})
A = matrix{{1,1,0},{1,1,0}}
f = map(Y,X,A)
assert isWellDefined f
assert not isProper f
assert not isProper(f,13)
///

TEST ///
--Test H'
X = normalToricVariety({{1,-1,0},{1,1,0},{-1,1,0},{0,0,1},{0,0,-1}},{{0,1,3},{1,2,3},{0,1,4},{1,2,4}})
Y = normalToricVariety({{0,1},{1,0}},{{0,1}})
A = matrix{{1,1,0},{1,1,0}}
f = map(Y,X,A)
assert isWellDefined f
assert isProper f
assert isProper(f,14)
///

TEST ///
--< Tests for pullback  >--
--Test PA
X = normalToricVariety({{1,0}, {0,1}, {-1,-1}}, {{0,1}})
Y = toricProjectiveSpace 1
f = map(Y,X, matrix{{1,0}})
D = toricDivisor({-2,3}, Y)
assert (pullback(f,D) == toricDivisor({3,0,-2},X))
assert (pairs pullback(f,OO D) === pairs OO toricDivisor({3,0,-2},X))
assert (module pullback(f,OO D) === module OO toricDivisor({3,0,-2},X))
///

TEST ///
--Test PB projection of PP^1xPP^1 onto PP^1
PP1 = toricProjectiveSpace 1
X = PP1**PP1
f = map(PP1,X,matrix{{1,0}})
DPP1=toricDivisor({1,1},PP1)
assert (pullback(f, DPP1) == toricDivisor({1,1,0,0}, X))
///

TEST ///
--Test PC Blowup up affine 2-space
AA2 = affineSpace 2;
BlO = toricBlowup({0,1}, AA2)
f  = map(AA2, BlO, 1)
DAA2=toricDivisor({1,0},AA2)
assert (pullback(f, DAA2)==toricDivisor({1,0,1},BlO))
assert (pairs pullback(f,OO DAA2) === pairs OO toricDivisor({1,0,1},BlO))
assert (module pullback(f,OO DAA2) === module OO toricDivisor({1,0,1},BlO))
///

TEST ///
--Test PD testing isCartier
Y = weightedProjectiveSpace({1,1,2})
X = normalToricVariety({{1,0},{0,-1},{-1,-2},{-1,0},{0,1}}, {{0,1},{1,2},{2,3},{3,4},{4,0}})
f = map(Y,X, 1)
assert try (pullback(f,Y_1);false) else true
///

TEST ///
--Test PE1 target f has higher dimension than source f
Y = toricProjectiveSpace 2
X = toricProjectiveSpace 1
f = map(Y, X, matrix{{1},{1}})
DY=toricDivisor({1,0,0},Y)
assert (pullback(f,DY)==toricDivisor({1,0},X))
///

TEST ///
--Test PE2 target f has higher dimension than source f
Y = toricProjectiveSpace 2
X = toricProjectiveSpace 1
f = map(Y, X, matrix{{2},{1}})
DY=toricDivisor({1,0,1},Y)
pullback(f,DY)
assert (pullback(f,DY)==toricDivisor({3,1},X))
///

TEST ///
--Test PE3 target f has higher dimension than source f
Y = toricProjectiveSpace 2
X = toricProjectiveSpace 1
S = ring Y
R = ring X
f = map(Y, X, matrix{{-2},{3}})
assert isWellDefined f
DY = toricDivisor({1,0,1},Y)
pullback(f,DY)
assert (pullback(f,DY) == toricDivisor({3,7}, X))
--F = cotangentSheaf Y
--pullback(f, cotangentSheaf Y)
assert (pullback(f,OO DY) === OO toricDivisor({3,7},X))
assert (module pullback(f,OO DY) === module OO toricDivisor({3,7},X))
///

TEST ///
-- Test for pullback
X = hirzebruchSurface 1
R = ring X
PP2 = toricProjectiveSpace 2
S = ring PP2
f = map(PP2, X, matrix{{1,0},{0,-1}})
assert(isWellDefined f)
assert(matrix inducedMap f == matrix{{R_1*R_2, R_0*R_1, R_3}})
D = toricDivisor({1,2,3}, PP2)
assert(pullback(f, OO D) === OO pullback(f, D))
///

TEST ///
-- Test for pullback
AA2 = affineSpace 2
R = ring AA2
PP2 = toricProjectiveSpace 2
S = ring PP2
f = map(PP2, AA2, 1)
assert(isWellDefined f)
assert(matrix inducedMap f == matrix{{1,R_0,R_1}})
D = toricDivisor({1,2,3}, PP2)
-- there is only one line bundle on AA2, so there's only one place to go
assert(pullback(f, OO D) === OO pullback(f, D))
///

TEST ///
--Test for isDominant
Y = toricProjectiveSpace 2
X = hirzebruchSurface 1
f = map(Y, X, matrix{{1,0},{0,-1}})
assert isDominant (f)
assert isSurjective f
assert isWellDefined f
///

TEST ///
Y = toricProjectiveSpace 3
X = affineSpace 3
f = map(Y, X, matrix{{2,0,0},{1,1,0},{3,1,0}})
assert not isDominant f
assert isWellDefined f
assert not isSurjective f
///

TEST ///
--Erika's test
Y = toricProjectiveSpace 1
X = toricProjectiveSpace 1
f = map(Y, X, 1)
assert isWellDefined f
assert isDominant f
assert isSurjective f
///

-------------------------------------------------------
-- Tests for isSurjective
-------------------------------------------------------
TEST ///
-- Test 1: Projection from a Hizerbruch surface to P^1
X = hirzebruchSurface 4
Y = toricProjectiveSpace 1
f = map(Y,X,matrix{{1,0}})
assert isSurjective f
///

-- Test 2:
TEST ///
X = affineSpace 2
Y = normalToricVariety({{1,0,0},{0,1,0}},{{0,1}})
f1 = map(X,Y,matrix{{1,0,0},{0,1,0}})
f2 = map(Y,X,matrix{{1,0},{0,1},{0,0}})
assert isSurjective f1
assert not isSurjective f2
///

-- Test 3: Embedding open subsets I
TEST ///
X = affineSpace 2
Y = toricProjectiveSpace 2 
f = map(Y,X,matrix{{1,0},{0,1}})
assert (not isSurjective f)
///

-- Test 4: Embedding open subsets II
TEST ///
X = affineSpace 2
Y = toricBlowup({0,1},X) 
f = map(Y,X,matrix{{1,0},{1,1}})
assert (not isSurjective f)
///

-- Test 5: Blowdown
TEST ///
X = affineSpace 2
Y = toricBlowup({0,1},X) 
f = map(X,Y,matrix{{1,0},{0,1}})
assert isSurjective f
///


--Tests for ideal
TEST ///
--Embedding of P^1 into P^2
X = toricProjectiveSpace 1;
Y = toricProjectiveSpace 2;
f = map(Y,X,matrix{{1},{1}});
g = map(Y,X,matrix{{2},{1}});
R=ring Y;
assert(ideal f == ideal(R_1-R_2))
assert(ideal g == ideal(R_0*R_1-R_2^2))
///

--Open embedding of an affine chart
--Currently this test fails
TEST ///
AA2 = affineSpace 2;
PP2 = toricProjectiveSpace 2;
f = map(PP2, AA2, 1)
R = ring PP2;
ideal f
///

--Tests for induced maps on divisors
TEST ///
X = toricProjectiveSpace 1;
Y = hirzebruchSurface 2;
f = map(X,Y,matrix{{1,0}});
fCD = cartierDivisorGroup f;
fPic = picardGroup f;
assert(source fPic == picardGroup target f);
assert(target fPic == picardGroup source f);
assert(source fCD == cartierDivisorGroup target f);
assert(target fCD == cartierDivisorGroup source f);
assert(fPic * fromCDivToPic(X) == fromCDivToPic(Y) * fCD)
///

TEST ///
X = toricProjectiveSpace 2;
Y = hirzebruchSurface (-1);
code (hirzebruchSurface, ZZ)
-- Y is a blowup of X
E = Y_3;
f = map(X,Y,1);
fCD = cartierDivisorGroup f;
assert(fCD*(vector X_0) == vector (Y_2+E))
assert(fCD*(vector X_1) == vector (Y_0+E))
///

TEST ///
PP2 = toricProjectiveSpace 2
S = ring PP2
n = dim PP2
X = PP2 ** PP2
R = ring X
-- the diagonal map P2 -> P2xP2
f = map(X, PP2, id_(ZZ^n) || id_(ZZ^n))
isWellDefined f
assert(codim ideal f == n)
res ideal f -- resolution of the diagonal
///

end---------------------------------------------------------------------------     

------------------------------------------------------------------------------
-- SCRATCH SPACE
------------------------------------------------------------------------------

-- XXX
uninstallPackage "ToricMaps"
restart
installPackage "ToricMaps"
check ToricMaps

viewHelp ToricMaps

------------------------------------------------------------------------------
needsPackage "ToricMaps";
PP1 = toricProjectiveSpace 1;
PP3 = toricProjectiveSpace 3;
tally flatten flatten flatten for i from 1 to 5 list (
    for j from -5 to 5 list (
    	for k from -5 to 5 list (	
    	    f := map(PP3, PP1, matrix{{i}, {j}, {k}});
    	    I := ideal f;
    	    betti res I
    	    )
	)
    )

PP1 = toricProjectiveSpace 1;
X = kleinschmidt(3, {2,2}) 
f = map(X, PP1, transpose matrix{{1,2,3}})
g = inducedMap f
S = ring X
flatten entries matrix g / degree
transpose matrix degrees ring X

(ideal f)_*
degrees S

pullback(f, X_0)
pullback(f, X_1)

betti res ideal f
isHomogeneous ideal f
inducedMap f


X = hirzebruchSurface 1;
drop(rays X, {1,1})
Y = normalToricVariety(drop(rays X, {1,1}), subsets(3,2));
isWellDefined Y
f = map(Y, X, 1)
pullback(f, Y_0)
pullback(f, Y_1)
pullback(f, Y_2)


PP1 = toricProjectiveSpace 1;
rays PP1
FF1 = hirzebruchSurface 1;
S = ring FF1
R = ring PP1
f = map(FF1, PP1, matrix{{1},{1}})
pullback(f, FF1_0)
pullback(f, FF1_1)
pullback(f, FF1_2)
pullback(f, FF1_3)
r = rank picardGroup FF1
kk = coefficientRing R
T = (kk(monoid [z_0..z_(2*r-2)])) 
T =  R ** (T / ideal apply(r, i -> T_i * T_(i+r) -1))
R ** T
T_0
T_3
presentation T
R_0 * T_0
g  = map(T, S, {T_0 * T_2, T_0 *T_4*T_3, T_1 * T_2, T_1^2 * T_3})
I = ker g
isHomogeneous I 

g  = map(R, S, {R_0, R_0, R_1, R_1^2})
ker g

