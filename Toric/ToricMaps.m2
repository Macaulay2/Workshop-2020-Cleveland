-- -*- coding: utf-8 -*-
------------------------------------------------------------------------------
-- Copyright 2017-2019 Gregory G. Smith
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
  Date => "9 May 2020",
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
      Name => "Gregory G. Smith", 
      Email => "ggsmith@mast.queensu.ca", 
      HomePage => "https://www.mast.queensu.ca/~ggsmith"},
      {
      Name => "Michael Loper",
      Email => "loper012@umn.edu",
      HomePage => "https://www.math.umn.edu/~loper012"},
      {
      Name => "Elise Walker",
      Email => "walkere@math.tamu.edu",
      HomePage => "https://www.math.tamu.edu/~walkere"},
      {
      Name => "Weikun Wang",
      Email => "wwang888@math.umd.edu",
      HomePage => "https://wangweikun.com"},
      {
      Name => "Julie Rana",
      Email => "ranaj@lawrence.edu",
      HomePage => "https://sites.google.com/site/jranamath"},
      {
      Name => "Thomas Yahl",
      Email => "thomasjyahl@tamu.edu",
      HomePage => "https://www.math.tamu.edu/~thomasjyahl"}
      },
  Headline => "routines for working with toric morphisms",
  PackageExports => {
      "NormalToricVarieties"
  },
  PackageImports => {
      "NormalToricVarieties",
      "FourierMotzkin"
  },
  DebuggingMode => true,
  Reload => true
)

export {
    "ToricMap",
    "isFibration",
    "outerNormals",
    "isProper",
    "pullback"
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

- ToricMap := ToricMap => f -> new ToricMap from {
    symbol source => source f,
    symbol target => target f,
    symbol matrix => - matrix f,
    symbol cache => new CacheTable}

ZZ * ToricMap := ToricMap => (r, f) -> new ToricMap from {
    symbol source => source f,
    symbol target => target f,
    symbol matrix => r * matrix f,
    symbol cache => new CacheTable
    }

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
-- at the moment exported for dubugging purposes
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
	return false
	);
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
isProper ToricMap := Boolean => f -> (
    if not isWellDefined f then << "The map is not well defined!" << return false;
    X := source f;
    Y := target f;
    if isComplete X then return true;
    if (isComplete Y and not isComplete X) then return false;
    rayMatrixX := transpose matrix rays X;
    rayMatrixY := transpose matrix rays Y;
    A := matrix f;
    --based on the idea that the map should be proper if and only if all torus invariant curves in X are                              
    --PP^1 or are contained in the torus invariant curves of Y.
    for tau in max Y do (
	--dimension of tau cap image A and computing potential cones over tau
	d := dim Y - rank (gens ker transpose A | gens ker transpose rayMatrixY_tau);
	maxConesWithRightDimension := select(max X, 
	    sigma -> member(sigma, orbits(X, rank A - d))
	    );
	--compute the cones over tau
	conesOverTau := select(maxConesWithRightDimension, 
	    sigma -> all(flatten entries (outerNormals(Y,tau)*A*rayMatrixX_sigma),
		i -> i <= 0)
	    );
    	--if no cones over tau, not proper
	if (#conesOverTau === 0) then return false;
    	--compute facets of the cones over tau
        facesOverTau := select(orbits(X, rank A - d + 1), 
	    alpha-> any(conesOverTau, sigma -> isSubset(alpha, sigma))
	    );
    	--pick which faces appear only once
	facesCount := hashTable apply(facesOverTau,
	    alpha -> {alpha, #select(conesOverTau, sigma -> isSubset(alpha, sigma))}
	    );
	uniqueFaces := select(facesOverTau, i -> facesCount#i < 2);
    	--faces of tau
    	facesOfTau := select(orbits(Y, dim Y - d + 1), beta -> isSubset(beta,tau));
	--check if the faces appearing only once are contained in faces of tau
	if not all(uniqueFaces, alpha -> any(facesOfTau,
		beta -> coker (A*rayMatrixX_alpha) == coker rayMatrixY_beta)
	    ) then return false;
	);
    true
    )


-- older slower deprecated method
isProper (ToricMap,ZZ) := Boolean => (f, flag) -> (
    if not isWellDefined f then << "the map is not well-defined!" << return false; -- check that f is well-defined first
    X := source f;
    Y := target f;
    if isComplete X then return true;
    if (isComplete Y and not isComplete X) then return false;
    A := matrix f;
    rayMatrixX := transpose matrix rays X; -- rays of X in columns
    rayMatrixY := transpose matrix rays Y; -- rays of Y in columns
    -- make a hash table whose keys are max cones in Y and values are max cones in X mapping into them
    coneTable := new MutableHashTable;
    for sigma in max X do (
	for tau in max Y do ( 
      	if all(flatten entries (outerNormals(Y, tau) * A * rayMatrixX_sigma), i -> i <= 0) then (
	    if not coneTable#?tau then coneTable#tau = {sigma}
	    else coneTable#tau = coneTable#tau|{sigma}
	    )
	)
    );
    K := mingens ker A;
    volA := max flatten entries mingens minors(rank A, A);
    for tau in max Y do (
    	indicesOverTau := unique flatten coneTable#tau; -- indices of rays in X over tau in Y
	raysOverTau := entries transpose rayMatrixX_indicesOverTau; -- rays in X over tau in Y
	conesOverTau := apply(coneTable#tau, sigma -> apply(sigma, i -> position(indicesOverTau, j -> j===i)));
	varietyOverTau := normalToricVariety(raysOverTau, conesOverTau); 
 	-- compute the rays of image(A) intersect tau
	raysTauCapImA := first fourierMotzkin ( (transpose outerNormals(Y,tau)) , last fourierMotzkin (A | -A) );
	liftTau := (volA*raysTauCapImA)//A | K | -K; -- volA is multiplied since over ZZ not QQ
	--first test whether if any of max cones in X over tau are of dimension less than liftTau
	if #orbits(varietyOverTau, dim X - rank liftTau) =!= #conesOverTau then return false;
	--the codimension in dim X of boundaries of liftTau is dim X - rank liftTau +1
	boundaries := select(orbits(varietyOverTau,dim X - rank liftTau + 1), C ->  #select(max varietyOverTau, sig -> isSubset(C,sig))<2);	
	for C in boundaries do (
		supportHyperplanes := first fourierMotzkin liftTau;
		if all(numcols supportHyperplanes, i -> #delete(0, flatten entries ((matrix rays varietyOverTau)^C * supportHyperplanes_i)) > 0) then return false;
	);
    );
    true
)


isFibration = method()
-- We're not convinced this work. It seems to be based on:
-- 1) Page 133 of Cox, Little, Schenck, which says that if a map of integer lattices is surjective, then it's *locally* a fibration
-- https://www.mimuw.edu.pl/~jarekw/pragmatic2010/CoxLittleSchenckJan2010.pdf
-- 2) Stackexchange discussion which gives a characterization of surjective maps of integer lattices
-- https://math.stackexchange.com/questions/132689/elementary-proof-that-if-a-is-a-matrix-map-from-mathbbzm-to-mathbb-zn
--There may be a way to fix this, based on Cox, Little, Schenck chapter 7, but it needs work.
isFibration ToricMap := Boolean => f -> 1 == minors(dim target f, matrix f)

isDominant = method()
isDominant ToricMap := Boolean => f -> (rank matrix f == dim target f)

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



--isSurjective is running, needs tested
isSurjective ToricMap := Boolean => (f) -> (
targetCones := reverse flatten drop(values orbits target f, -1);
sourceCones := flatten drop(values orbits source f, -1);
interiorSourceCones := {};
for sigma in sourceCones do(
  interiorSourceCones = append(interiorSourceCones, sum( (rays source f)_sigma));
);
imageSourceCones := {};
for sigma in interiorSourceCones do (
   imageSourceCones = append(imageSourceCones, ((matrix f) * (transpose matrix{sigma})) );
);
--test which cones imageSourceCones land in; deleted cone if hit
for rho in imageSourceCones do(
    if (targetCones =={}) then return true;
    for sigma in targetCones do(
        if isInterior(target f, sigma, rho)
	then (hitConeIndex := position(targetCones, i->i==sigma ); targetCones = drop(targetCones, hitConeIndex););
	);
    );
false
)




-- THIS LOCAL METHOD ALREADY APPEARS IN "NormalToricVarieties"
cartierCoefficients = method ()
cartierCoefficients ToricDivisor := List => D -> (
    X := variety D;
    rayMatrix := matrix rays X;
    coeffs := transpose (matrix {entries D});
    apply (max X, sigma -> coeffs^sigma // rayMatrix^sigma)
    )


pullback = method()
pullback (ToricMap, ToricDivisor) := ToricDivisor => (f, D) -> (
    if not isCartier D then error "-- expected a Cartier divisor";
    cartierData := cartierCoefficients D;
    X := source f;
    rayList := rays X;
    n := # rayList;
    Y := target f;
    maxCones := max Y;
    sum for i to n-1 list (
	imageRho := (matrix f) * (transpose matrix {rayList_i});
	-- find a maximal cone containing the image of each ray
	maxConeIndex := position(maxCones, 
	    sigma -> all(flatten entries(outerNormals(Y, sigma) * imageRho), b -> b <= 0));
	-- see Proposition 6.1.20 in Cox-Little-Schenck
	((transpose imageRho * cartierData_(maxConeIndex))_(0,0)) * X_i
	)
    )


pullback (ToricMap, Module) := Module => (f, M) -> (
    R := ring source f;
    S := ring target f;
    if R =!= ring M then error "-- expected module over the Cox ring of the source";
    f ** M    
    )

pullback (ToricMap, CoherentSheaf) := CoherentSheaf => (f, F) -> sheaf pullback(f, module F)


inducedMap ToricMap := RingMap => opts -> f -> (
    R := ring source f;
    Y := target f;
    if not isSmooth Y then error "-- expected the target variety to be smooth";
    S := ring Y;
    map(R, S, apply(numgens S, i -> (
		exps := entries pullback(f, Y_i);
		product(numgens R, j -> R_j^(exps#j))
	    )))
    )
ideal ToricMap := Ideal => f -> (
    B := ideal ring target f;
    saturate (kernel inducedMap f, B)
    )

classGroup ToricMap := Matrix => f -> (
    X := source f;
    Y := target f;
    if not isSmooth Y then error "-- expected the target variety to be smooth";
    divisorMap := map(weilDivisorGroup X, weilDivisorGroup Y,
	transpose matrix apply(# rays Y, i -> entries pullback (f, Y_i))
	);
    map(classGroup X, classGroup Y,
	transpose ((transpose (fromWDivToCl(X) * divisorMap)) // transpose fromWDivToCl(Y))
	)
    )




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
        the class of torus-equivariant maps between normal toric varieties
    Description
        Text
	    A morphism of normal toric varieties $X \to X'$ corresponds to a map 
	    of lattices $N \to N'$ where the fans of $X$ and $X'$ are contained in
	    $N$ and $N'$ respectively. To specify a map of normal toric varieties,
	    the target and source normal toric varieties need to be specificied
	    as well as a matrix which maps $N$ into $N'$.
    SeeAlso
        NormalToricVariety
///

doc ///
    Key
        (isWellDefined, ToricMap)
    Headline 
        checks if a toric map is well defined 
    Usage 
        isWellDefined f
    Inputs 
        f : ToricMap
	    a map between toric varieties
    Outputs 
        : Boolean 
	    returns true if the map is well defined; false if not
    Description
        Text
	    This function checks that a toric map $f$ of varieties is well
	    defined by checking that the dimensions of the matrix match the
	    dimension of the lattices and checking that the image of each
	    maximal cone is contained in a maximal cone of the target fan.
    	Text
            The first example illustrates the projection from the Hirzebruch
            surface to the projective line is well defined.
    	Example  
	    FF2 = hirzebruchSurface 2;
            PP1 = toricProjectiveSpace 1;
            f = map(PP1, FF2, matrix{{1,0}})
    	    isWellDefined f 
	Text
	    The second example illustrates two attempts to define a toric map
	    from the projective plane to a weighted projective space. The
	    first, corresponding to the identity on the lattices, is not
	    well-defined.  The second, corresponding to a stretch in the
	    lattices, is well-defined.
	Example
	    PP2 = toricProjectiveSpace 2
	    WP112 = weightedProjectiveSpace {1,1,2}
	    g = map(WP112, PP2, 1)
	    isWellDefined g 
	    f = map(WP112, PP2, matrix{{1,0},{0,2}})
            isWellDefined f	   
    SeeAlso
    	(hirzebruchSurface, ZZ)
        (toricProjectiveSpace, ZZ)
        (weightedProjectiveSpace, List)
///

doc ///
    Key
        (isProper, ToricMap)
    Headline 
        checks if a toric map is proper
    Usage 
        isProper f
    Inputs 
        f:ToricMap
	    a map between toric varieties
    Outputs 
        :Boolean 
	    returns true if the map is proper; false if not
    Description
        Text
            A map f of varieties is proper if it is universally closed. 
	    Letting f be a map of toric varieties and f' the corresponding map of lattices, the map f is
	    proper if and only if the preimage of the support of the target fan under f' is the support 
	    of the source fan. 
    	Text
            This example illustrates that the projection from the Hirzebruch surface H2 to P^1 is proper.
    	Example  
	   H2 = hirzebruchSurface 2
           PP1 = toricProjectiveSpace 1
           f = map(PP1,H2,matrix{{1,0}})
    	   isProper(f)
	Text
	    This example illustrates that the map from the  blow-up of the origin of 
	    affine 2-space to affine 2-space is proper.
	Example
	   AA2 = affineSpace 2;
	   max AA2
	   BlO = toricBlowup({0,1}, AA2)
	   f  = map(AA2, BlO, 1)
           isProper(f)
    SeeAlso
        (isComplete, NormalToricVariety)
/// 

doc ///
    Key
        (pullback, ToricMap, ToricDivisor)
    Headline 
        compute the pullback of a Cartier divisor under a toric map
    Usage 
        pullback(f, D)
    Inputs 
        f : ToricMap
	    a map between toric varieties
	D : ToricDivisor
	    a toric divisor on the target of f
    Outputs 
        : ToricDivisor 
	    the pullback of D under f
    Description
        Text
            Torus-invariant Cartier divisors pull back under a toric map by
	    composing the toric map with the support function of the divisor.	    
    	Text
	    In the first example, we consider the projection from a product of
	    two projective lines onto the first factor.  The pullback of a
	    point is just a fibre in the product.
    	Example  
            PP1 = toricProjectiveSpace 1;
	    X = PP1 ** PP1;
            f = map(PP1, X, matrix{{1,0}})
	    assert isWellDefined f
    	    D = toricDivisor({1,1}, PP1)
	    pullback(f, D)
	Text
	    This example illustrates that the pullback of a line through the origin in 
	    affine 2-space under the blowup map is a line together with the exceptional divisor.
	Example
	   AA2 = affineSpace 2;
	   max AA2
	   BlO = toricBlowup({0,1}, AA2)
	   f  = map(AA2, BlO, 1)
	   rays AA2
	   DAA2=toricDivisor({1,0},AA2)
           pullback(f, DAA2)
    SeeAlso
        (entries, ToricDivisor)
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
f = map(Y, X, matrix{{-2},{3}})
DY=toricDivisor({1,0,1},Y)
pullback(f,DY)
assert (pullback(f,DY)==toricDivisor({3,7},X))
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
