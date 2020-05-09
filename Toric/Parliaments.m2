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
  "Parliaments",
  AuxiliaryFiles => false,
  Version => "0.3",
  Date => "9 May 2020",
  Authors => {{
      Name => "Gregory G. Smith", 
      Email => "ggsmith@mast.queensu.ca", 
      HomePage => "http://www.mast.queensu.ca/~ggsmith"}},
  Headline => "routines for working with toric reflexive sheaves",
  PackageExports => {"NormalToricVarieties", "HyperplaneArrangements"},
  PackageImports => {"NormalToricVarieties", "HyperplaneArrangements"},
  DebuggingMode => true
  )


export {
  "ToricReflexiveSheaf",
  "toricReflexiveSheaf",
  "subspace",     
  "mukaiLazarsfeldBundle",
  "groundSet",
  "isArithmeticallyFree", 
  "isLocallyFree", 
  "associatedCharacters",
  "isGloballyGenerated",
  "subspacePoset",  -- is this necessary
  "ToricReflexiveSheafMap",
  "toricTangentBundle",
  "toricCotangentBundle"
  }


------------------------------------------------------------------------------
-- CODE THAT SHOULD BELONG TO ANOTHER PACKAGE
------------------------------------------------------------------------------

CoherentSheaf.directSum = args -> (
  assert(#args > 0);
  X := variety args#0;
  if not all(args, F -> variety F === X) then (
    error "expected all sheaves to be over the same ring");
  sheaf(X, directSum apply(args, F -> F.module)))

ToricDivisor == ToricDivisor := Boolean => (D1, D2) -> (
  variety D1 === variety D2 and vector D1 == vector D2)
  

------------------------------------------------------------------------------
-- CODE
------------------------------------------------------------------------------
ToricReflexiveSheaf = new Type of HashTable; 
ToricReflexiveSheaf.synonym = "toric reflexive sheaf"
ToricReflexiveSheaf.GlobalAssignHook = globalAssignFunction
ToricReflexiveSheaf.GlobalReleaseHook = globalReleaseFunction
expression ToricReflexiveSheaf := E -> (
  local klyachkoData;
  if rank E === 0 then return expression 0
  else (
    n := # rays variety E;
    for i to n-1 do (
      flag := {{toString(i) | ": "},{null}};
      P := sort apply(pairs E#i, p -> {p#1,p#0});
      for p in P do (
      	flag = {flag#0 | {p#1}, flag#1 | {p#0}});
      if i === 0 then klyachkoData = flag
      else klyachkoData = klyachkoData | flag);
    Table klyachkoData))
debug Core --- kludge to access "hasAttribute" and getAttribute
net ToricReflexiveSheaf := E -> ( 
  if hasAttribute(E,ReverseDictionary) then toString getAttribute(E,ReverseDictionary) 
  else new FunctionApplication from { 
    toricReflexiveSheaf, Adjacent{ "(...", Adjacent{",", Adjacent{variety E, ")"}}}})
describe ToricReflexiveSheaf := E -> net expression E
ToricReflexiveSheaf#{Standard,AfterPrint} = 
ToricReflexiveSheaf#{Standard,AfterNoPrint} = E -> (
  << endl;
  << concatenate(interpreterDepth:"o") << lineNumber << " : ToricReflexiveSheaf on ";
  << variety E << endl;)  

ambient ToricReflexiveSheaf := Sequence => E -> E.ambient
variety ToricReflexiveSheaf := NormalToricVariety => E -> E.variety
rank ToricReflexiveSheaf := ZZ => E -> E.rank

isWellDefined ToricReflexiveSheaf := Boolean => E -> (
  n := # rays variety E;  
  -- check keys
  K := keys E;
  expectedKeys := set (toList(0..n-1) | {
      symbol ambient, symbol rank, symbol variety, symbol cache });
  if set K =!= expectedKeys then (
    if debugLevel > 0 then (
      added := toList(K - expectedKeys);
      missing := toList(expectedKeys - K);
      if #added > 0 then << "-- unexpected key(s): " << toString added << endl;
      if #missing > 0 then << "-- missing key(s): " << toString missing << endl;);
    return false;);
  -- check types
  for i from 0 to n-1 do (
    if not instance(E#i, HashTable) then (
      if debugLevel > 0 then (
      	<< "-- expected 'E#" << i << "' to be a HashTable" << endl);
      return false);
    if not all(keys E#i, k -> instance(k, RingElement)) then (
	if debugLevel > 0 then (
	  << "-- expected the keys of 'E#" << i << "' to be ring elements" << endl);
	return false);
    if not all(values E#i, v -> instance(v, ZZ)) then (
	if debugLevel > 0 then (
	  << "-- expected the values of 'E#" << i << "' to be integers" << endl);
	return false)); 
  if not instance(E.ambient, Sequence) or length E.ambient =!= 2 then (
    if debugLevel > 0 then << "-- expected 'E.ambient' to be a Sequence with two entries" << endl;
    return false);
  if not instance(E.ambient#0, PolynomialRing) then (
    if debugLevel > 0 then (
      << "-- expected 'E.ambient#0' to be a PolynomialRing" << endl);
    return false);
  if not instance(E.ambient#1, List) then (
    if debugLevel > 0 then << "--- expected 'E.ambient#1' to be a List" << endl;  
    return false);
  if not all(length E.ambient#1, j -> instance(j, ZZ)) then (
      if debugLevel > 0 then << "--- expected 'E.ambient#1' to be a list of integers" << endl;  
    return false);
  if length E.ambient#1 =!= degreeLength E.ambient#0 then (
      if debugLevel > 0 then << "--- expected 'E.ambient#1' to be a degree in the ambient ring" << endl;  
    return false);
  if not instance(E.rank, ZZ) then (
    if debugLevel > 0 then (
      << "-- expected 'E.rank' to be a ZZ" << endl);
    return false);  
  if not instance(E.variety, NormalToricVariety) then (
    if debugLevel > 0 then (
      << "-- expected 'E.variety' to be a NormalToricVariety" << endl);
    return false);
  if not instance(E.cache, CacheTable) then (
    if debugLevel > 0 then << "-- expected `E.cache' to be a CacheTable" << endl;
    return false);
  -- check flags
  (R,d) := ambient E;
  for i from 0 to n-1 do (
    if not all(keys E#i, k -> ring k === R) then (
      if debugLevel > 0 then (
	<< "-- expected the keys of 'E#" << i << "' to be elements in the ambient ring" << endl);
      return false);    
    if not all(keys E#i, k -> isHomogeneous k) then (
      if debugLevel > 0 then (
	<< "-- expected the keys of 'E#" << i << "' to be homogeneous" << endl);
      return false);
    if not all(keys E#i, k -> degree k === d) then (
      if debugLevel > 0 then (
	<< "-- expected the keys of 'E#" << i << "' have degree equal to the ambient degree" << endl);
      return false);    
    if rank E =!= rank source mingens ideal keys E#i then (
      if debugLevel > 0 then (
	<< "-- expected the keys of 'E#" << i;
	<< "' to form a basis for a vector space of dimension " << rank E << endl);
      return false));
  I := ideal keys E#0;
  if not all(n, i -> I == ideal keys E#i) then (
    if debugLevel > 0 then (
      << "-- expected the ring elements on each ray to generate the same ideal" << endl);
    return false);    
  true)

ToricReflexiveSheaf == ZZ := Boolean => (E,m) -> (
  if m =!= 0 then error "attempted to compare a sheaf to a nonzero integer";
  rank E === 0)
ZZ == ToricReflexiveSheaf := Boolean => (m,E) -> E == m

toricReflexiveSheaf = method()
toricReflexiveSheaf (List, NormalToricVariety) := ToricReflexiveSheaf => 
  (L,X) -> (
    n := #L;
    if n =!= # rays X then 
      error "expected a filtration for each torus-invariant divisor";
    r := #L#0;
    if r === 0 then error "expected a nonempty filtration";
    R := ring L#0#0#0;
    d := degree L#0#0#0;
    new ToricReflexiveSheaf from hashTable (
      apply(n, i -> i => hashTable L#i) | {
      	symbol ambient => (R,d),
      	symbol rank => r,
      	symbol variety => X,
      	symbol cache => new CacheTable}))
-- constructor for the zero sheaf
toricReflexiveSheaf(Ring, List, NormalToricVariety) := ToricReflexiveSheaf => 
  (R,d,X) -> (
    n := # rays X;
    new ToricReflexiveSheaf from hashTable (
      apply(n, i -> i => hashTable {}) | {
      	symbol ambient => (R,d),
      	symbol rank => 0,
      	symbol variety => X,
      	symbol cache => new CacheTable}))

toricReflexiveSheaf ToricDivisor := ToricReflexiveSheaf => (
  cacheValue symbol ToricReflexiveSheaf)(
  D -> (
    c := entries vector D;
    e := symbol e;
    R := QQ(monoid[e]);
    n := # rays variety D;
    W := for i to n-1 list {{R_0,c#i}};
    X := variety D;  
    toricReflexiveSheaf(W,X)))

toricDivisor ToricReflexiveSheaf := ToricDivisor => opts -> (
  (cacheValue (symbol toricDivisor => opts))(
  E -> (
    r := rank E;
    if r =!= 1 then error "expect a rank-one sheaf";
    X := variety E;
    n := # rays X;
    g := first groundSet E;
    D := sum for i from 0 to n-1 list (
      weights := reverse sort unique values E#i;
      j := 0;
      while g % subspace(i,weights#j, E) != 0 do j = j + 1;
      weights#j * X_i);
    D )))

toricTangentBundle = method();
toricTangentBundle NormalToricVariety := ToricReflexiveSheaf => X -> (
  d := dim X;
  e := symbol e;
  R := QQ(monoid[e_1..e_d]);
  raysX := rays X;
  n := # rays X;
  W := for i from 0 to n-1 list (
    f := (vars R * transpose matrix {raysX#i})_(0,0);
    basisSet := {(f,1)};
    for g in select(gens R, h -> h // f == 0) do basisSet = basisSet|{(g,0)};
    basisSet);
  toricReflexiveSheaf(W,X))

toricCotangentBundle = method();
toricCotangentBundle NormalToricVariety := ToricReflexiveSheaf => X -> (
  d := dim X;
  e := symbol e;
  R := QQ(monoid[e_1..e_d]);
  raysX := rays X;
  n := # rays X;
  W := for i from 0 to n-1 list (
    M := matrix { raysX#i };
    basisSet := { ( (vars R * transpose M)_(0,0), -1 ) };
    for g in first entries (vars R * gens ker M) do (
      basisSet = basisSet | { (g,0) } );
    basisSet);
  toricReflexiveSheaf(W,X))

-*
weights are correct but vectors are not; need to construct complements
dual ToricReflexiveSheaf := ToricReflexiveSheaf => {} >> o -> E -> (
  X := variety E;
  n := # rays X;
  W := {};
  for i from 0 to n-1 do W = W | {apply(pairs E#i, p -> (p#0, - p#1))};
  toricReflexiveSheaf(W,X))
*-

trim ToricReflexiveSheaf := ToricReflexiveSheaf => opts -> E -> (
  if rank E === 0 then return E;
  chosenBasis := gens gb subspace(0, -infinity, E);
  r := rank E;
  KK := coefficientRing (ambient E)#0;
  e := symbol e;
  newR := KK(monoid[e_1..e_r]);
  X := variety E;
  n := # rays X;
  W := for i from 0 to n-1 list (
    apply(pairs E#i, 
      p -> ( (vars newR * sub(p#0 // chosenBasis, KK))_(0,0), p#1 ) ));
  F := toricReflexiveSheaf(W,X);
  (R,d) := ambient E;
  BE := basis(d,R);
  F.cache.trim = map(E, F, 
    sub( (coefficients( chosenBasis, Monomials => BE) )#1, KK));
  F)

ToricReflexiveSheaf.directSum = args -> (
  sheaves := args;
  sheaves = select(sheaves, E -> rank E =!= 0);
  m := #sheaves;
  if m === 0 then return args#0;
  X := variety sheaves#0;  
  if not all(sheaves, G -> variety G === X) then 
    error "expected all sheaves to be over the same variety";
  -- need to fix this: handle ambient degree other that {1}
  p := apply(toList sheaves, G -> numgens (ambient G)#0);
  s := apply(m, k -> sum(k, j -> p#j));
  e := symbol e;
  R := QQ(monoid[e_0..e_(sum(p)-1)]);
  phi := new HashTable from apply(m, k -> (
      k => map(R, (ambient sheaves#k)#0, apply(toList(s#k .. s#k+p#k-1), j -> R_j)) ));
  n := # rays X;
  W := for i from 0 to n-1 list flatten apply(m, 
    k -> apply(pairs sheaves#k#i, (r,w) -> (phi#k(r),w)));
  E := toricReflexiveSheaf(W,X);
  E.cache.components = toList sheaves;
  E)
ToricReflexiveSheaf ++ ToricReflexiveSheaf := ToricReflexiveSheaf => (E,F) -> directSum(E,F)
directSum ToricReflexiveSheaf := E -> directSum(1 : E)
components ToricReflexiveSheaf := E -> if E.cache.?components then 
  E.cache.components else {E}

ToricReflexiveSheaf ** ToricDivisor := ToricReflexiveSheaf => (E,D) -> (
  c := entries vector D;
  X := variety D;
  n := # rays X;
  W := for i from 0 to n-1 list for p in pairs E#i list (p#0,p#1+c#i);
  toricReflexiveSheaf(W,X))
ToricDivisor ** ToricReflexiveSheaf := ToricReflexiveSheaf => (D,E) -> E ** D

exteriorPower (ZZ, ToricReflexiveSheaf) := ToricReflexiveSheaf => opts -> 
  (p, E') -> (  
    E := trim E';
    X := variety E;
    r := rank E;
    (R,d) := ambient E;
    if p < 0 or p > r then toricReflexiveSheaf(R, p*d, X)
    else if p === 0 then toricReflexiveSheaf(0 * X_0)
    else if p === 1 then E'
    else (  
      KK := coefficientRing (ambient E)#0;
      e := symbol e;
      newR := KK(monoid[e_1..e_r, SkewCommutative => true]);
      t := symbol t;
      degRing := KK(monoid[t]);
      n := # rays X;
      W := {};
      for i to n-1 do (
	psi := sub( 
	  (coefficients(matrix{keys E#i}, Monomials => vars R))#1, degRing);
	psi = exteriorPower(p, map(degRing^(-values E#i), degRing^r, psi));
      	weights := degrees target psi;
	psi = basis(p, newR) * sub(psi,KK);
      	W = W | { 
	  for k to binomial(r,p) -1 list ( psi_(0,k), weights#k#0)} );
    toricReflexiveSheaf(W,X) ) );
determinant ToricReflexiveSheaf := ToricReflexiveSheaf => opts -> E -> (
  exteriorPower(rank E, E))

symmetricPower (ZZ, ToricReflexiveSheaf) := ToricReflexiveSheaf => (p, E') -> (
    -- should think harder about the matroid labels in the general case
    if (ambient E')#1 =!= {1} then E := trim E' else E = E';
    X := variety E;
    r := rank E;
    (R,d) := ambient E;
    if p < 0 then return toricReflexiveSheaf(R, p*d, X);
    if p === 0 then return toricReflexiveSheaf(0 * X_0);
    if p === 1 then return E';
    if rank E === 0 then return toricReflexiveSheaf(R, p*d, X);
    W := join for i to # rays X - 1 list (
	psi := map(R^1, R^(-values E#i), matrix{apply(keys E#i, 
		    g -> matrix{{g}})});
	psi = symmetricPower(p, psi);
	weights := degrees source psi;
	apply(binomial(r+p-1,p), k -> (psi_(0,k), weights#k#0)));
    toricReflexiveSheaf(W,X) )

subspace = method();
subspace (ZZ, ZZ, ToricReflexiveSheaf) := 
subspace (ZZ, InfiniteNumber, ToricReflexiveSheaf) := Ideal => (i,j,E) -> (
  subspaceGens := select(keys E#i, f -> E#i#f >= j);
  (R,d) := ambient E;  
  if #subspaceGens === 0 then ideal(0_R)
  else ideal subspaceGens)

-- local routine; the input L is expected to be a list of lists
boxProduct = L -> (
  m := #L;
  if m === 0 then {}
  else if m === 1 then apply(L#0, l -> {l})
  else if m === 2 then flatten table(L#0, L#1, (k,l) -> {k} | {l})
  else flatten table(first L, boxProduct drop(L,1),  (k,l) -> {k} | l))

subspacePoset = method();
subspacePoset ToricReflexiveSheaf := HashTable => E -> (  
  n := #rays variety E;
  (R,d) := ambient E;
  L := boxProduct apply(n, i -> sort unique values E#i);
  KK := coefficientRing R;
  BE := basis(d,R);
  V := keys set for l in L list gens intersect apply(n, i -> image sub( 
      (coefficients(gens subspace(i,l#i,E),  Monomials => BE))#1, KK));
  H := new MutableHashTable;
  for v in V do (
    m := rank source v;
    if H#?m then H#m = H#m | {v}
    else if m === 0 then continue
    else H#m = {v});
  hashTable apply(keys H, k -> k => H#k));

-- old method: returns ideals rather than matrices
subspacePoset (ToricReflexiveSheaf,ZZ) := HashTable => (E,j) -> (
  n := #rays variety E;
  (R,d) := ambient E;
  L := boxProduct apply(n, i -> unique values E#i);
  KK := coefficientRing R;
  BE := basis(d,R);
  V := unique for l in L list intersect apply(n, i -> image sub(
      (coefficients(gens subspace(i,l#i,E),  Monomials => BE))#1, KK));
  V = apply(V, v -> first entries (BE * sub(gens v,R)) );
  H := new MutableHashTable;
  for v in V do (
    m := rank source mingens ideal v;
    if H#?m then H#m = H#m | {ideal v}
    else if m === 0 then H#m = {ideal 0_R}
    else H#m = {ideal v});
  hashTable apply(keys H, k -> k => H#k))


groundSet = method();
groundSet ToricReflexiveSheaf := List => (cacheValue symbol groundSet)(E -> (  
  if rank E === 0 then return {};
  P := subspacePoset E;
  if P#?1 then gSet := P#1
  else (
    k := 2;
    while not P#?k do k = k + 1;
    gSet = {(first P#k)_{0}});
  for k from 2 to rank E do (
    if P#?k then for V in P#k do (
      spots := positions(gSet, f -> f % V == 0);
      for j from 0 to rank source V - 1 do (
	if spots === {} then M := 0 * V_{j}
	else M = matrix{gSet_spots};
      	g := V_{j} % M;
      	if g != 0 then (
    	  gSet = gSet | {g};
    	  spots = spots | {#gSet-1} ) )));
  (R,d) := ambient E;
  BE := basis(d,R);
  gSet = apply(gSet, g -> (basis(d,R) * g)_(0,0) );
  reverse sort gSet));

-- old method: incorrectly? does calculations in the ambient ring
-*
groundSet (ToricReflexiveSheaf,ZZ) := List => (E,j) -> (
    if rank E === 0 then return {};
    P := subspacePoset E;
    if not P#?1 then gSet := {first (first P#(rank E))_* }
    else gSet = flatten apply(P#1, I -> I_*);
    for k from 2 to rank E do (
      if not P#?k then continue
      else for V in P#k do (
      	spots := positions(gSet, f -> f % V == 0);
      	C := unique flatten entries (gens V % (matrix{gSet_spots} ** ring V));
      	C = select(C, r -> r != 0);
      	if C == {} then continue else gSet = gSet | C));
    reverse sort gSet)
*-

isArithmeticallyFree = method();
isArithmeticallyFree ToricReflexiveSheaf := Boolean => E -> (
  rank E == # groundSet E)

isLocallyFree = method();
isLocallyFree ToricReflexiveSheaf := Boolean => E -> (
  if E == 0 then return true;
  X := variety E;
  all(max X, sigma -> (
      U := normalToricVariety( (rays X)_sigma, {sigma});
      EU := toricReflexiveSheaf( apply(sigma, i -> pairs E#i), U);
      isArithmeticallyFree EU)));

associatedCharacters = method();
associatedCharacters ToricReflexiveSheaf := List => E -> (
  X := variety E;
  if E == 0 then return apply(max X, sigma -> {});
  for sigma in max X list (
    U := normalToricVariety((rays X)_sigma, {toList(0..#sigma-1)});
    EU := toricReflexiveSheaf(for i in sigma list pairs E#i,U);
    G := groundSet EU;
    C := transpose matrix for g in G list (
      for i to # rays U - 1 list (
	weights := reverse sort unique values EU#i;
	j := 0;
	while g % subspace(i, weights#j, EU) != 0 do j = j+1;
	weights#j));
    if rank source C =!= rank EU then error "expected sheaf to be locally free";
    if not isSmooth U then error "expected sheaf on a smooth toric variety";    
    entries transpose ((inverse matrix rays U) * C)));

isGloballyGenerated = method()
isGloballyGenerated ToricReflexiveSheaf := Boolean => E -> (
  if E == 0 then return true;
  X := variety E;
  n := # rays X;  
  outerNormals := matrix rays X;
  assChar := associatedCharacters E;
  G := groundSet E;
  (R,d) := ambient E;
  (M,C) := coefficients( matrix {G}, Monomials => basis(d,R));
  divisors := apply(components cover E, L -> toricDivisor L);
  all(#assChar, i -> (
      potentialBases := for u in assChar#i list (
      	charVector := transpose matrix {u};
      	select(#G, j -> (
	    coordinates := outerNormals*charVector - matrix vector divisors#j;
	    all(n, k -> if member(k, (max X)#i) then coordinates_(k,0) == 0 
	      else coordinates_(k,0) <= 0))));
      any(boxProduct potentialBases, s -> det C_s =!= 0))));  

cover ToricReflexiveSheaf := ToricReflexiveSheaf => (
  cacheValue symbol cover)(E -> (
    X := variety E;
    n := # rays X;
    (RE,dE) := ambient E;    
    gSet := groundSet E;
    if gSet === {} then (
      Z := toricReflexiveSheaf(RE,dE,X);
      E.cache.generators = map(E, Z, 0);
      return Z);
    divisors := for g in gSet list (
      sum for i from 0 to n-1 list (
    	weights := reverse sort unique values E#i;
    	j := 0;
    	while g % subspace(i,weights#j, E) != 0 do j = j + 1;
    	weights#j *X_i));
    F := directSum apply(divisors, D -> toricReflexiveSheaf D);
    (M,C) := coefficients(matrix{gSet}, Monomials => basis(dE, RE));
    KK := coefficientRing RE;
    E.cache.generators = map(E, F, entries sub(C,KK));
    F))

generators ToricReflexiveSheaf := ToricReflexiveSheafMap => opts -> E -> (
  if not E.cache.?generators then cover E;
  E.cache.generators)

------------------------------------------------------------------------------
ToricReflexiveSheafMap = new Type of HashTable
ToricReflexiveSheafMap.synonym = "equivariant map of toric reflexive sheaves"
source ToricReflexiveSheafMap := ToricReflexiveSheaf => f -> f.source
target ToricReflexiveSheafMap := ToricReflexiveSheaf =>  f -> f.target
matrix ToricReflexiveSheafMap := Matrix => opts -> f -> f.matrix
variety ToricReflexiveSheafMap := NormalToricVariety => f -> variety source f

net ToricReflexiveSheafMap := f -> net matrix f
ToricReflexiveSheafMap#{Standard,AfterPrint} = 
ToricReflexiveSheafMap#{Standard,AfterNoPrint} = f -> (
  << endl;				  -- double space
  << concatenate(interpreterDepth:"o") << lineNumber << " : ToricReflexiveSheafMap ";
  << net target f << " <--- " << net source f << endl;)

map(ToricReflexiveSheaf, ToricReflexiveSheaf, List) := 
  ToricReflexiveSheafMap => opts -> (E,F,L) -> (
    (RF, dF) := ambient F;  
    (RE, dE) := ambient E;  
    rF := rank source basis(dF, RF);
    rE := rank source basis(dE, RE);    
    KK := coefficientRing RF;
    phi := map(KK^rE, KK^rF, L);
    new ToricReflexiveSheafMap from {
      symbol source => F,
      symbol target => E,
      symbol matrix => phi,
      symbol cache => new CacheTable})
map(ToricReflexiveSheaf, ToricReflexiveSheaf, Matrix) := 
  ToricReflexiveSheafMap => opts -> (E, F, f) -> map(E, F, entries f)
map(ToricReflexiveSheaf, ToricReflexiveSheaf, Function) := 
  ToricReflexiveSheafMap => opts -> (E, F, f) -> (
    (RF, dF) := ambient F;  
    (RE, dE) := ambient E;  
    rF := rank source basis(dF, RF);
    rE := rank source basis(dE, RE);    
    map(E, F, table(rE, rF, f)))
map(ToricReflexiveSheaf, ToricReflexiveSheaf, Number) :=
map(ToricReflexiveSheaf, ToricReflexiveSheaf, RingElement) := 
  ToricReflexiveSheafMap => opts -> (E, F, g) -> (
    (RF, dF) := ambient F;  
    (RE, dE) := ambient E;  
    rF := rank source basis(dF, RF);
    rE := rank source basis(dE, RE);  
    KK := coefficientRing RF; 
    if g == 0 then map(E, F, table(rE, rF, (i,j) -> 0_KK))
    else if rF === rE then map(E, F, g * id_(KK^rE))
    else error "expected 0, or ambient vector spaces of the same dimension")
  
ToricReflexiveSheafMap * ToricReflexiveSheafMap := ToricReflexiveSheafMap =>
  (g,f) -> (
    if source g =!= target f then error "maps are not composable";
    map(target g, source f, matrix g * matrix f))
  
ToricReflexiveSheafMap == ZZ := Boolean => (f,m) -> matrix f == m
ZZ == ToricReflexiveSheafMap := Boolean => (m,f) -> f == m
    
isWellDefined ToricReflexiveSheafMap := Boolean => f -> (
  -- check keys
  K := keys f;
  expectedKeys := set{ symbol source, symbol target, symbol matrix, 
    symbol cache};
  if set K =!= expectedKeys then (
    if debugLevel > 0 then (
      added := toList(K - expectedKeys);
      missing := toList(expectedKeys - K);
      if #added > 0 then 
        << "-- unexpected key(s): " << toString added << endl;
      if #missing > 0 then 
        << "-- missing keys(): " << toString missing << endl);
    return false);
  -- check types
  if not instance(f.source, ToricReflexiveSheaf) then (
    if debugLevel > 0 then 
      << "-- expect 'f.source' to be a ToricReflexiveSheaf" << endl;
    return false);
  if not instance(f.target, ToricReflexiveSheaf) then (
    if debugLevel > 0 then 
      << "-- expect 'f.target' to be a ToricReflexiveSheaf" << endl;
    return false);
  if not instance(f.matrix, Matrix) then (
    if debugLevel > 0 then 
      << "-- expect 'f.matrix' to be a Matrix " << endl;
    return false); 
  F := source f;
  E := target f;
  (RF, dF) := ambient F;  
  (RE, dE) := ambient E;
  KK := coefficientRing RF; 
  if KK =!= coefficientRing RE then (
    if debugLevel > 0 then (
      << "-- expected the coefficient rings of the ambient rings to be equal";
      << endl);
    return false);      
  if not all(flatten entries matrix f, r -> instance(r, KK)) then (
    if debugLevel > 0 then (
      << "-- expected entries belong to coefficient ring of the ambient ring";
      << endl);
    return false);
  if not instance(E.cache, CacheTable) then (
    if debugLevel > 0 then 
      << "-- expected `E.cache' to be a CacheTable" << endl;
    return false);    
  -- check underlying varieties
  if variety F =!= variety E then (
    if debugLevel > 0 then 
      << "-- expected sheaves over the same variety" << endl;
    return false);
  -- check compatiblity of flags
  n := # rays variety F;
  BF := basis(dF, RF);  
  BE := basis(dE, RE);
  for i from 0 to n-1 do (
    weights := sort unique (values F#i | values E#i);
    for w in weights do (
      IF := subspace(i,w,F);
      (M,C) := coefficients(mingens IF, Monomials => BF);
      IE := ideal (BE * (matrix f) * sub(C, KK));
      if not isSubset(IE, subspace(i,w,E)) then (
    	if debugLevel > 0 then (
      	  << "-- expected " << toString w << "-th part of the filtrations";
      	  << " on the " << toString i << "-th ray to be compatible" << endl);
    	return false)));    
  true)

kernel ToricReflexiveSheafMap := ToricReflexiveSheaf => opts -> (
  cacheValue symbol kernel)(
  f -> (
    E := source f;
    (R,d) := ambient E;
    I := ideal( basis(d,R) * gens ker matrix f );
    X := variety E;    
    if I == 0 then return toricReflexiveSheaf(R,d,X);
    n := # rays X;
    W := for i from 0 to n-1 list (
      basisSet := {};
      weights := reverse sort unique values E#i;
      for w in weights do (
	V := ideal select( (ideal mingens intersect(I, subspace(i,w,E)))_*, 
	  g -> degree g === d);
	if V === ideal() then continue 
	else (
	  spots := positions(basisSet, f -> f#0 % V == 0);
	  C := unique flatten entries (gens V % (matrix{apply(basisSet_spots, 
		  p -> p#0)} ** ring V));
	  C = for c in C list if c == 0 then continue else (c,w); 
	  if C == {} then continue 
	  else basisSet = basisSet | C));
      basisSet);
    toricReflexiveSheaf(W,X)))

mukaiLazarsfeldBundle = method();
mukaiLazarsfeldBundle ToricDivisor := ToricReflexiveSheaf => D -> (
  coeffs := entries vector D;
  X := variety D;
  n := # rays X;
  S := ring X;
  monos := first entries basis(sum apply(n, i -> coeffs#i * degree S_i), S);
  E := directSum apply(monos, g -> (  
      coeffs = first exponents g;
      toricReflexiveSheaf sum apply(n, i -> - coeffs#i * X_i)));
  f := map(toricReflexiveSheaf D, E, matrix{toList(rank E : 1_QQ)});
  ker f)


------------------------------------------------------------------------------
Complex = new Type of List;
Complex.synonym = "chain complex of toric reflexive sheaves"  
net Complex := C ->  (
  D := netList( transpose {{ -1, rank target C#0}}, 
    Boxes => false, Alignment => Center, VerticalSpace => 1);
  for i to #C - 1 do (
    D = D | "  " | (netList ( {i, rank source C#i} | apply(components source C#i, L -> toricDivisor L), 
  	Boxes => false, Alignment => Center, VerticalSpace => 1)));
  D);
Complex#{Standard,AfterPrint} = 
Complex#{Standard,AfterNoPrint} = C -> (
  << endl;
  << concatenate(interpreterDepth:"o") << lineNumber << " : Chain complex of toric reflexive sheaves over ";
  << variety C#0 << endl;)  

resolution ToricReflexiveSheaf := Complex => opts -> E -> (
  (R,d) := ambient E;
  nabla := map(toricReflexiveSheaf(R,d, variety E), E, 0);
  maps := {};
  while true do (
    F := source nabla;
    K := ker nabla;
    if K == 0 then break;
    G := cover K;
    nabla = map(F,K,1) * gens K;
    maps = maps | {nabla});
  new Complex from maps);

------------------------------------------------------------------------------
-- DOCUMENTATION
------------------------------------------------------------------------------
beginDocumentation()

undocumented {
  subspacePoset,
  (subspacePoset, ToricReflexiveSheaf),
  (net, ToricReflexiveSheaf),
  (net, ToricReflexiveSheafMap),  
  (expression, ToricReflexiveSheaf),
  (components, ToricReflexiveSheaf)
  }

doc ///
   Key
     Parliaments
   Headline
     data types and routines for working with toric reflexive sheaves
   Description
     Text
       This package is designed for experimenting with toric reflexive
       sheaves on a normal toric variety.
///

doc ///
   Key
     ToricReflexiveSheaf
   Headline
     the class of all toric reflexive sheaves
   Description
     Text
       A reflexive sheaf is a coherent sheaf that is isomorphic to its second
       dual (as a sheaf of modules) via the canonical map.  For example, any
       locally-free sheaf is reflexive.  On the other hand, a reflexive sheaf
       is torsion-free.  Hence, reflexive sheaves form a wider class than the
       locally-free sheaves, but are not as general as all torsion-free
       sheaves.
       
       A toric reflexive sheaf on a normal toric variety is a 
       torus-equivariant reflexive sheaf.  In other words, it is a reflexive
       sheaf equipped with a torus-action that is compatible with the natural
       torus-action on the underlying toric variety.
       
       Theorem 1.3.2 in Klyachko's @HREF
       ("http://www.mpim-bonn.mpg.de/preblob/4712","Vector bundles and torsion
       free sheaves on the projective plane")@ establishes that the category of
       toric reflexive sheaves is equivalent to the category of vector spaces
       with a family of separated exhaustive decreasing filtrations indexed by
       the irreducible torus-invariant divisors.
 ///
 
 doc ///
   Key
     (toricReflexiveSheaf, List, NormalToricVariety)
     toricReflexiveSheaf
   Headline
     make a toric reflexive sheaf
   Usage
     toricReflexiveSheaf(W,X)
   Inputs
     W:List
       of lists of weighted bases.  For each irreducible torus-invariant
       divisor on the underlying toric variety, there is a list of pairs
       consisting of a homogeneous ring element in the ambient ring and its
       integer weight
     X:NormalToricVariety
   Outputs
     :ToricReflexiveSheaf
   Description
     Text
       Theorem 1.3.2 in Klyachko's @HREF
       ("http://www.mpim-bonn.mpg.de/preblob/4712","Vector bundles and torsion
       free sheaves on the projective plane")@ establishes that the category of
       toric reflexive sheaves is equivalent to the category of vector spaces
       with a family of separated exhaustive decreasing filtrations indexed by
       the irreducible torus-invariant divisors.  
       
       Since we assume that the irreducible torus-invariant divisors on the
       underlying toric variety (a.k.a. the rays in the fan) are ordered and
       indexed by nonnegative integers (see @TO
       "NormalToricVarieties::normalToricVariety"@), the $i$-th entry in the
       list {\tt W} naturally corresponds to the $i$-th irreducible
       torus-invariant divisor.  The vector space corresponding to the toric
       reflexive sheaf is realized as a linear subspace in a homogeneous
       component of a graded @TO2 ("PolynomialRing", "polynomial ring")@; see
       @TO (ambient, ToricReflexiveSheaf)@.  For a given irreducible
       torus-invariant divisor, the corresponding filtration is defined by a
       list of homogeneous @TO2("RingElement", "ring elements")@ of the
       appropriate degree in this ambient ring together with their associated
       integer weights.  The $j$-th linear subspace in the filtration is the
       homogeneous component of the ideal generated by all the ring elements
       with weight greater than or equal to $j$.
     
     Text
       Following Example 3.8 in @HREF ("https://arxiv.org/abs/1409.3109",
       "Toric vector bundles and parliaments of polytopes")@, the tangent
       bundle on projective $2$-space may be constructed such that the ambient
       vector space is the degree-one homogeneous component of a standard
       graded polynomial ring in two variables.       
     Example
       (X,R) = (toricProjectiveSpace(2), QQ[e_1,e_2]);
       rays X
       W = {{(-e_1-e_2,1),(e_1,0)},{(e_1,1),(e_2,0)},{(e_2,1),(e_1,0)}}
       TX = toricReflexiveSheaf(W,X)
       describe TX
       isWellDefined TX
       rank TX
       variety TX
       ambient TX
     Text
       Following Example 4.4 in @HREF ("https://arxiv.org/abs/1409.3109",
       "Toric vector bundles and parliaments of polytopes")@, we construct a
       globally-generated rank-two toric vector bundle on the first Hirzebruch
       surface.
     Example
       Y = hirzebruchSurface 1;
       rays Y
       W' = {{(e_1,4),(e_2,-2)}, {(e_1,3),(e_2,2)}, {(e_2,5),(e_1,0)}, {(e_1+e_2,3),(e_1,-1)}}
       G = toricReflexiveSheaf(W',Y)
       describe G
       isWellDefined G
       rank G
       variety G
       ambient G
   Caveat
     To avoid length unnessary calculations, this method assumes that the
     input correctly encodes a toric reflexive sheaf. Nevertheless, one can
     verify this by using @TO (isWellDefined,ToricReflexiveSheaf)@.
   SeeAlso
     (describe, ToricReflexiveSheaf)
     (isWellDefined, ToricReflexiveSheaf)
     (ambient, ToricReflexiveSheaf)
 ///
 
doc ///
   Key
     (toricReflexiveSheaf, ToricDivisor)
   Headline
     make a toric reflexive sheaf
   Usage
     toricReflexiveSheaf(D)
   Inputs
     D:ToricDivisor
   Outputs
     :ToricReflexiveSheaf
   Description
     Text
       Each toric divisor on a normal toric variety corresponds to a rank-one
       toric reflexive sheaf.  When the underlying variety is smooth, this
       rank-one sheaf is simply the corresponding line bundle.  Given a toric
       divisor, this method returns the corresponding rank-one toric reflexive
       sheaf.
     
     Text
       On projective $2$-space, an ample toric divisor corresponds to a line
       bundle.       
     Example
       X = toricProjectiveSpace(2);
       D = 2*X_0 + 3*X_1 + 5*X_2
       isAmple D and isEffective D
       E = toricReflexiveSheaf(2*X_0 + 3*X_1 + 5*X_2);
       describe E
       isWellDefined E
       rank E
       ambient E
       variety E
       isArithmeticallyFree E
     Text
       The structure sheaf on the underlying toric variety corresponds to the
       zero divisor.
     Example
       O = toricReflexiveSheaf(0*X_0)
       describe O
       isWellDefined O
       rank O
       ambient O
       variety O
       isArithmeticallyFree O
   SeeAlso
     toricReflexiveSheaf 
     isArithmeticallyFree
     (toricDivisor, ToricReflexiveSheaf)
 ///
 
doc ///
   Key
     (toricDivisor, ToricReflexiveSheaf)
   Headline
     make the toric divisor associated to a rank-one toric reflexive sheaf
   Usage
     D = toricDivisor E
   Inputs
     E:ToricReflexiveSheaf
   Outputs
     D:ToricDivisor
       if {\tt E} has rank-one then {\tt D} is the corresponds to a toric divisor
   Description
     Text
       Each toric divisor on a normal toric variety corresponds to a rank-one
       toric reflexive sheaf.  Given a rank-one toric reflexive sheaf, the
       method returns the corresponding toric divisor.  
     
     Text       
       The tangent bundle on projective $2$-space doesn't correspond to a
       single toric divisor, but a line bundle does.
     Example
       (X,R) = (toricProjectiveSpace 2, QQ[e_1,e_2]);
       L = toricReflexiveSheaf(2*X_0);
       D = toricDivisor L
       D == 2*X_0
   SeeAlso
     (toricReflexiveSheaf, ToricDivisor)
     isArithmeticallyFree
 ///
 
document {
   Key => 
     {(isWellDefined, ToricReflexiveSheaf)},
   Headline =>
     "whether a toric reflexive sheaf is well-defined",
   Usage =>
     "isWellDefined E",
   Inputs =>
     {"E" => ToricReflexiveSheaf},
   Outputs =>
     {Boolean => 
       {TO "true", " if the list of lists of pairs of ring elements and integers
       determine a toric reflexive sheaf"}},

       "The input data determines a toric reflexive sheaf on a normal toric
       variety if, for each irreducible torus-invariant divisor (or ray in
       the fan), the following conditions hold:",     
       UL{
	 {"each ", TO2(RingElement, "ring element"), " belongs to the ", 
	   TO2((ambient,ToricReflexiveSheaf), "ambient ring"),},
	 "each ring element is homogeneous,",
	 {"the degree of each ring element equals the ",
	   TO2((ambient,ToricReflexiveSheaf), "ambient degree"),},
	 "the ring elements form a basis for the homogeneous component in the
	 ambient degree of the ideal they generate,"
	 },
       "and, the ideals generated by the ring elements for each irreducible
       torus-invariant divisor are all equal.",
     PARA{},
       "Our favourite example, namely the tangent bundle on projective
       2-space, is well-defined.",
     EXAMPLE lines ///
       (X,R) = (toricProjectiveSpace(2),QQ[e_1,e_2]);
       W = {{(-e_1-e_2,1),(e_1,0)},{(e_1,1),(e_2,0)},{(e_2,1),(e_1,0)}};
       TX = toricReflexiveSheaf(W,X)
       isWellDefined TX
       ///,
     PARA{},
       "The next examples illustrate various ways that the input can fail to
       define a toric reflexive sheaf.",
     EXAMPLE lines ///
       debugLevel = 1;
       W1 = {{(-e_1-e_2,1),(e_1,0)},{(e_1,1),(e_2,0)},{(e_3,1),(e_1,0)}};
       E1 = toricReflexiveSheaf(W1,X);
       isWellDefined E1
       e_3
       ///,
     EXAMPLE lines ///         
       W2 = {{(-e_1-e_2,1),(e_1,0)},{(e_1,1),(e_2,0)},{(e_2+1,1),(e_1,0)}};
       E2 = toricReflexiveSheaf(W2,X);
       isWellDefined E2
       isHomogeneous W2#2#0#0
       ///,
     EXAMPLE lines ///         
       W3 = {{(-e_1-e_2,1),(e_1,0)},{(e_1,1),(e_2,0)},{(e_2^2,1),(e_1,0)}};
       E3 = toricReflexiveSheaf(W3,X);
       isWellDefined E3
       degree W3#2#0#0 =!= (ambient E3)#1
       ///,  
     EXAMPLE lines ///         
       W4 = {{(-e_1-e_2,1),(e_1,0)},{(e_1,1),(e_2,0)},{(2*e_1,1),(e_1,0)}};
       E4 = toricReflexiveSheaf(W4,X);
       isWellDefined E4
       rank E4 == rank source mingens ideal keys E4#2
       ///,         
     EXAMPLE lines ///         
       R' = QQ[e_1,e_2,e_3];
       W5 = {{(-e_1-e_2,1),(e_1,0)},{(e_1,1),(e_2,0)},{(e_3,1),(e_1,0)}};
       E5 = toricReflexiveSheaf(W5,X);
       isWellDefined E5
       ideal keys E5#2 != ideal keys E5#0
       ///,              
     PARA{},
       "This method also checks that the following aspects of the data structure:",
       UL {
	 {"the underlying ", TO HashTable, " has the expected keys, namely
	 integers, ", TT "ambient", ", ", TT "rank", ", ", TT "variety", ",
	 and ", TT "cache"},
	 {"the value for each integer keys is a ", TO HashTable},
	 {"the key of each HashTable associated to an integer is a ", 
	   TO RingElement},
	 {"the value of each HashTable associated to an integer is an ", 
	   TO ZZ},
	 {"the value of the ", TT "ambient", " key is a ", TO Sequence},
	 {"the ", TT "ambient", " sequence has two entries"},
	 {"the first entry in the ", TT "ambient", " sequence is a ", 
	   TO PolynomialRing},
	 {"the second entry in the ", TT "ambient", " sequence is a ", 
	   TO List},
	 {"the length of second entry in the ", TT "ambient", " sequence
	 equals the degree length of the ambient ring"},
	 {"each entry in second part of the ", TT "ambient", " sequence is an
	   ", TO ZZ},
	 {"the value of the ", TT "rank", " key is a ", TO ZZ},
	 {"the value of the ", TT "variety", " key is a ", 
	   TO NormalToricVariety},
	 {"the integer keys correspond to the irreducible torus-invariant
	 divisors on underlying normal toric variety"},
	 {"the value of the ", TT "cache", " key is a ", TO CacheTable}
	 },
   SeeAlso => {
     toricReflexiveSheaf}
}
 
doc ///
   Key
     (ambient, ToricReflexiveSheaf)
   Headline
     get the corresponding ambient vector space
   Usage
     (R,d) = ambient E
   Inputs
     E:ToricReflexiveSheaf
   Outputs
     :Sequence
       where {\tt R} is @TO2("PolynomialRing", "polynomial ring")@ and {\tt d}
       is a @TO2("List", "list")@ of integers corresponding to a degree in the
       polynomial ring
   Description
     Text
       The vector space corresponding to the fibre of a toric reflexive sheaf
       over the identity in the torus is realized as a linear subspace in the
       homogeneous component of degree {\tt d} in a graded
       @TO2("PolynomialRing", "polynomial ring")@ {\tt R}.  This method
       returns the pair {\tt (R,d)}.
       
     Text
       Most often {\tt R} is a standard graded polynomial ring and {\tt d} is
       simply $\{ 1\}$.  For instance, our favourite construction of the
       tangent bundle on projective 2-space realizes the ambient vector space
       as the degree-one component of a standard graded polynomial ring in two
       variables.       
     Example
       (X,R) = (toricProjectiveSpace(2), QQ[e_1,e_2]);
       W = {{(-e_1-e_2,1),(e_1,0)},{(e_1,1),(e_2,0)},{(e_2,1),(e_1,0)}}
       TX = toricReflexiveSheaf(W,X);
       ambient TX
       E = toricReflexiveSheaf(2*X_0)
       ambient E
       F = toricReflexiveSheaf(2*X_0) ++ toricReflexiveSheaf(3*X_1 - X_2)
       ambient F
   SeeAlso
     toricReflexiveSheaf 
///
 
doc ///
   Key
     (describe, ToricReflexiveSheaf)
   Headline
     displays the defining data
   Usage
     describe E
   Inputs
     E:ToricReflexiveSheaf
   Outputs
     :Net         
       a formatted array of the weighted bases defining the filtrations
       corresponding to each irreducible torus-invariant divisor
   Description
     Text
       For brevity, a @TO "ToricReflexiveSheaf"@ typically acquires the name
       of the global variable to which it was assigned.  The methods allows
       one to see the underlying data defining the toric reflexive sheaf.
       
     Text 
     
       The integers in the left column of the formatted array correspond to
       the irreducible torus-invariant divisors on the underlying toric
       variety; the rays in the fan are ordered and indexed by nonnegative
       integers; see @TO "NormalToricVarieties::normalToricVariety"@.  The
       vector space corresponding to the fibre of a toric reflexive sheaf over
       the identity in the torus is realized as a linear subspace in a
       homogeneous component of a graded @TO2 ("PolynomialRing", "polynomial
       ring")@; see @TO (ambient, ToricReflexiveSheaf)@.  For a given
       irreducible torus-invariant divisor, the corresponding rows in the
       formatted array list homogeneous @TO2("RingElement", "ring elements")@
       of the appropriate degree in this ambient ring together with the
       associated integer weight.  The $j$-th linear subspace in the
       filtration is the homogeneous component of the ideal generated by all
       the ring elements with weight greater than or equal to $j$.
       
     Text
       The tangent bundle on projective $2$-space has rank-two.  
     Example
       (X,R) = (toricProjectiveSpace(2), QQ[e_1,e_2]);
       W = {{(-e_1-e_2,1),(e_1,0)},{(e_1,1),(e_2,0)},{(e_2,1),(e_1,0)}}
       TX = toricReflexiveSheaf(W,X)
       describe TX
       subspace(0,-infinity,TX)              
       subspace(0,0,TX)
       subspace(0,1,TX)
       subspace(0,2,TX)
       subspace(0,infinity,TX)       
     Text
       The toric reflexive sheaf associated to a toric divisor has rank one.
     Example
       E = toricReflexiveSheaf(2*X_0)
       describe E
       subspace(1,-infinity,E)              
       subspace(1,0,E)
       subspace(1,1,E)
       subspace(1,infinity,E)   
   SeeAlso
     toricReflexiveSheaf 
     subspace
 ///

doc ///
   Key
     (rank, ToricReflexiveSheaf)
   Headline
     get the rank 
   Usage
     rank E
   Inputs
     E:ToricReflexiveSheaf
   Outputs
     :ZZ
   Description
     Text
       Over an integral scheme, the rank of a coherent sheaf is the dimension
       as a vector space over the function field of the fibre over the generic
       point.  For a torsion-free sheaf, this equals the dimension of the
       fiber over any point.
     
       The rank of a toric reflexive sheaf equals the dimension of the vector
       space corresponding to the fibre of a toric reflexive sheaf over the
       identity in the torus; see @TO (ambient, ToricReflexiveSheaf)@.
       
     Text
       The tangent bundle on projective 2-space has rank-two.  
     Example
       (X,R) = (toricProjectiveSpace(2), QQ[e_1,e_2]);
       W = {{(-e_1-e_2,1),(e_1,0)},{(e_1,1),(e_2,0)},{(e_2,1),(e_1,0)}};
       TX = toricReflexiveSheaf(W,X)
       rank TX
       (R,d) = ambient TX;
       hilbertFunction(d, module subspace(0, -infinity, TX))
     Text
       The toric reflexive sheaf associated to a toric divisor has rank one.
     Example
       L = toricReflexiveSheaf(2*X_0)
       rank L
     Text
       The rank of a direct sum is the sum of the rank of the summands.
     Example
       E = TX ++ L;
       rank E
   SeeAlso
     (ambient, ToricReflexiveSheaf) 
 ///
 
 doc ///
   Key
     (variety, ToricReflexiveSheaf)
   Headline
     get the underlying normal toric variety 
   Usage
     variety E
   Inputs
     E:ToricReflexiveSheaf
   Outputs
     :NormalToricVariety
   Description
     Text
       This method returns the underlying normal toric variety on which the
       reflexive sheaf is defined.
       
     Text
       For the tangent bundle on projective $2$-space or the line bundle
       associated to a toric divisor, we have the following       
     Example
       (X,R) = (toricProjectiveSpace(2), QQ[e_1,e_2]);
       W = {{(-e_1-e_2,1),(e_1,0)},{(e_1,1),(e_2,0)},{(e_2,1),(e_1,0)}}
       TX = toricReflexiveSheaf(W,X)
       variety TX
       E = toricReflexiveSheaf(2*X_0)
       variety E
   SeeAlso
     toricReflexiveSheaf 
     NormalToricVariety
 ///
 
doc ///
   Key
     (isArithmeticallyFree, ToricReflexiveSheaf)
     isArithmeticallyFree
   Headline
     whether a toric reflexive sheaf is a direct sum of toric line bundles
   Usage
     isArithmetically E
   Inputs
     E:ToricReflexiveSheaf
   Outputs
     :Boolean
       @TO true@ if the toric reflexive sheaf is isomorphic to a direct sum of
       torus-equivariant line bundles
   Description
     Text     
       A toric reflexive sheaf is isomorphic to a direct sum of
       torus-equivarient line bundles if and only if its rank is equal to the
       cardinality of its ground set; see Remark 3.3. in
       DiRocco-Jabbusch-Smith's @HREF ("https://arxiv.org/abs/1409.3109",
       "Toric vector bundles and parliaments of polytopes")@.
       
     Text
       The tangent bundle on projective $2$-space does not split into a
       direct sum of torus-equivariant line bundles, but its cover does.     
     Example
       (X,R) = (toricProjectiveSpace(2),QQ[e_1,e_2]);
       W = {{(-e_1-e_2,1),(e_1,0)},{(e_1,1),(e_2,0)},{(e_2,1),(e_1,0)}};
       TX = toricReflexiveSheaf(W,X)
       isArithmeticallyFree TX
       F = cover TX
       isArithmeticallyFree F
       apply(components F, D -> toricDivisor D)
     Text
       By definition, the direct sum of two toric line bundles is
       arithmetically free.
     Example       
       E = toricReflexiveSheaf(2*X_0) ++ toricReflexiveSheaf(3*X_1 - X_2);
       describe E
       isArithmeticallyFree E
   SeeAlso
     (directSum, ToricReflexiveSheaf)
     (cover, ToricReflexiveSheaf)
     (toricReflexiveSheaf, ToricDivisor)
///
 
doc ///
   Key
     (directSum, ToricReflexiveSheaf)
     (symbol ++, ToricReflexiveSheaf, ToricReflexiveSheaf)
   Headline
     make the direct sum of toric reflexive sheaves
   Usage
     F = E1 ++ E2
     F = directSum(E1,E2,...)
     F = directSum(name1 => E1, name2 => E2, ...)
   Inputs
     Ei:ToricReflexiveSheaf
   Outputs
     F:ToricReflexiveSheaf
       the direct sum of the input toric reflexive sheaves
   Description
     Text     
       The direct sum of toric reflexive sheaves is another toric
       reflexive sheaf.

     Example
       (X,R) = (toricProjectiveSpace(2),QQ[e_1,e_2]);
       W1 = {{(-e_1-e_2,2),(e_1,0)},{(e_1,-1),(e_2,-2)},{(e_2,7),(e_1,-1)}};
       E1 = toricReflexiveSheaf(W1,X);
       describe E1
       W2 = {{(-e_1-e_2,1),(e_1,0)},{(e_1,1),(e_2,0)},{(e_2,1),(e_1,0)}};
       E2 = toricReflexiveSheaf(W2,X);
       describe E2
       F1 = E1 ++ E2
       describe F1
       F2 = toricReflexiveSheaf(2*X_0) ++ toricReflexiveSheaf(3*X_1 - X_2)
       describe F2
       isArithmeticallyFree F2
   SeeAlso
     toricReflexiveSheaf 
     isArithmeticallyFree
 ///
 
doc ///
   Key
     (subspace, ZZ, ZZ, ToricReflexiveSheaf)	
     (subspace, ZZ, InfiniteNumber, ToricReflexiveSheaf)
     subspace
   Headline
     make a linear subspace in corresponding filtration
   Usage
      subspace(i,j,E)
   Inputs
     i:ZZ       
       indexing an irreducible torus-invariant divisor in the underlying toric
       variety
     j:ZZ
       or @TO "InfiniteNumber"@, indexing part of the separated exhaustive filtration       
     E:ToricReflexiveSheaf
   Outputs
     :Ideal
       in the ambient polynomial ring such the graded component in the ambient
       degree is the corresponding vector space       
   Description
     Text
       In this package, the vector space corresponding to the fibre of a toric
       reflexive sheaf over the identity in the torus is realized as a linear
       subspace in a homogeneous component of a graded polynomial ring.  This
       method returns the ideal in this graded polynomial ring whose
       homogeneous component is linear subspace in the corresponding
       flitration.
       
       More precisely, we assume that the irreducible torus-invariant divisors
       on the underlying toric variety (a.k.a. the rays in the fan) are
       ordered and indexed by nonnegative integers (see @TO
       "NormalToricVarieties::normalToricVariety"@), so the first argument
       corresponds to the $i$-th irreducible torus-invariant divisor.  The
       vector space corresponding to the toric reflexive sheaf is realized as
       a linear subspace in a homogeneous component of a graded @TO2
       ("PolynomialRing", "polynomial ring")@; see @TO (ambient,
       ToricReflexiveSheaf)@.  For a given irreducible torus-invariant
       divisor, the corresponding filtration is defined by a list of
       homogeneous @TO2("RingElement", "ring elements")@ of the appropriate
       degree in this ambient ring together with their associated integer
       weights.  The $j$-th linear subspace in the filtration is the
       homogeneous component of the ideal generated by all the ring elements
       with weight greater than or equal to $j$.
       
     Text
       Our favourite construction of the tangent bundle on projective
       $2$-space realizes the ambient vector space as the degree-one component
       of a standard graded polynomial ring in two variables.       
     Example
       (X,R) = (toricProjectiveSpace(2), QQ[e_1,e_2]);
       W = {{(-e_1-e_2,1),(e_1,0)},{(e_1,1),(e_2,0)},{(e_2,1),(e_1,0)}};
       TX = toricReflexiveSheaf(W,X)
       describe TX
       (R,d) = ambient TX
       V = subspace(0,-infinity,TX)
       hilbertFunction(d,module V)
       V0 = subspace(0,0,TX)
       hilbertFunction(d,module V0)       
       V1 = subspace(0,1,TX)       
       hilbertFunction(d,module V1)              
       V2 = subspace(0,2,TX)       
       hilbertFunction(d,module V2)                     
       subspace(0,infinity,TX)              
   SeeAlso
     toricReflexiveSheaf 
     (ambient, ToricReflexiveSheaf)
 ///
 
doc ///
   Key
     groundSet	
     (groundSet, ToricReflexiveSheaf)
   Headline
     make the associated matroid
   Usage
      groundSet E
   Inputs
     E:ToricReflexiveSheaf
   Outputs
     :List
       of @TO2("RingElement", "RingElements")@ which form the ground set of
       the associated matroid
   Description
     Text
       Proposition 3.1 in DiRocco-Jabbusch-Smith's @HREF
       ("https://arxiv.org/abs/1409.3109", "Toric vector bundles and
       parliaments of polytopes")@ introduces a canonical representable
       matroid associated to a toric reflexive sheaf.  This method returns a
       list of ring elements which represent this matroid in the
       @TO2("(ambient, ToricReflexiveSheaf)", "ambient vector space")@.
              
     Text
       Following Example 3.8 in DiRocco-Jabbusch-Smith's @HREF
       ("https://arxiv.org/abs/1409.3109", "Toric vector bundles and
       parliaments of polytopes")@, the ground set for the matroid associated
       to the tangent bundle on projective $2$-space has three elements.
     Example
       (X,R) = (toricProjectiveSpace(2), QQ[e_1,e_2]);
       W = {{(-e_1-e_2,1),(e_1,0)},{(e_1,1),(e_2,0)},{(e_2,1),(e_1,0)}};
       TX = toricReflexiveSheaf(W,X)
       rank TX
       groundSet TX
       apply(components cover TX, D -> toricDivisor D)       
     Text
       Example 3.7 in DiRocco-Jabbusch-Smith's @HREF
       ("https://arxiv.org/abs/1409.3109", "Toric vector bundles and
       parliaments of polytopes")@ shows that the ground set may be strictly
       larger than the union of the bases that split the filtration over the
       maximal cones.  In particular, for this toric vector bundle, the ground
       set has five elements.
     Example
       (Y,S) = (toricProjectiveSpace(1) ** toricProjectiveSpace(1), QQ[e_1,e_2,e_3]);
       V = {{(e_1+e_3,1),(e_3,0),(e_2,-1)},{(e_1+e_2,1),(e_2,0),(e_3,-1)},
	 {(e_2,2),(e_3,1),(e_1+e_3,0)},{(e_2,2),(e_3,1),(e_1+e_2,0)}};
       E = toricReflexiveSheaf(V,Y);
       rank E
       groundSet E
       F = cover E;
       apply(components F, D -> toricDivisor D)
       apply(components F, D -> HH^0(Y, OO(toricDivisor D)))
     Text
       The ground set for a direct sum is essentially the union of the ground
       sets of the summands.       
     Example
       G = TX ++ toricReflexiveSheaf(2*X_0) ++ toricReflexiveSheaf(3*X_1-X_2)
       describe G
       rank G
       groundSet G       
   SeeAlso
     toricReflexiveSheaf 
     (cover, ToricReflexiveSheaf)
///
 
doc ///
   Key
     (cover, ToricReflexiveSheaf)
   Headline
     make the canonical reflexive sheaf that surjects on the global sections     
   Usage
      F = cover E
   Inputs
     E:ToricReflexiveSheaf
   Outputs
     F:ToricReflexiveSheaf     
       the unique minimal arthimetically free reflexive sheaf that surjects
       onto the global section of {\tt E}
   Description
     Text     
       Proposition 1.1. in DiRocco-Jabbusch-Smith's @HREF
       ("https://arxiv.org/abs/1409.3109", "Toric vector bundles and
       parliaments of polytopes")@ describes the minimal collection of toric
       line bundles that surject onto the global sections of a toric vector
       bundle.  This method returns the direct sum of these rank-one toric
       reflexive sheaves.
       
     Text
       Following Example 3.8 in DiRocco-Jabbusch-Smith's @HREF
       ("https://arxiv.org/abs/1409.3109", "Toric vector bundles and
       parliaments of polytopes")@, we obtain part of the Euler sequence from
       the tangent bundle on projective 2-space.
     Example
       (X,R) = (toricProjectiveSpace(2), QQ[e_1,e_2]);
       W = {{(-e_1-e_2,1),(e_1,0)},{(e_1,1),(e_2,0)},{(e_2,1),(e_1,0)}};
       TX = toricReflexiveSheaf(W,X);
       F = cover TX;
       describe F
       apply(components F, E -> toricDivisor E)
   SeeAlso
     toricReflexiveSheaf 
     (generators, ToricReflexiveSheaf)
 ///
  
doc ///
   Key
     (symmetricPower, ZZ, ToricReflexiveSheaf)
   Headline
     make the symmetric power of a toric reflexive sheaf
   Usage
      symmetricPower(p, E)
   Inputs
     p:ZZ
     E:ToricReflexiveSheaf
   Outputs
     :ToricReflexiveSheaf     
       the {\tt p}-th symmetric power of {\tt E}
   Description
     Text
       Under the Klyachko equivalence of categories, the symmetric power of a
       toric reflexive sheaf $E$ is determined by the symmetric power of a
       vector space corresponding to $E$ equipped with the induced family of
       separated exhaustive descreasing filtrations indexed by the irreducible
       torus-invariant divisors.
              
     Text
       If $E$ has rank $r$, then the $p$-th symmetric power has rank $r+p-1$
       choose $p$.       
     Example
       (X,R) = (toricProjectiveSpace(2), QQ[e_1,e_2]);
       W = {{(-e_1-e_2,1),(e_1,0)},{(e_1,1),(e_2,0)},{(e_2,1),(e_1,0)}};
       TX = toricReflexiveSheaf(W,X);
       rank TX
       describe TX
       TX2 = symmetricPower(2,TX);
       rank TX2
       describe TX2
       TX3 = symmetricPower(3,TX);
       rank TX3
       describe TX3
     Text
       The symmetric power of a toric vector bundles correponds to the tensor
       power of the associated line bundle on the projectivization of the
       toric vector bundle.  As a consequence, a sufficiently large symmetric
       power of an ample toric vector bundle is globally generated.
     Example
       (X,R) = (toricProjectiveSpace 2, QQ[e_1,e_2,e_3]);
       W' = {{(e_1-e_2,5), (e_2-e_3,2), (e_1,-1)}, {(e_1,6), (e_2,0), (e_3,-1)}, {(e_3,3), (e_2,0), (e_1,-4)}};
       E = toricReflexiveSheaf(W', X);
       r = rank E 
       describe E
       apply(components cover E, L -> OO toricDivisor L)
       E2 = symmetricPower(2,E);
       rank E2 == binomial(r+2-1,2)
       describe E2
       all(components cover E2, L -> isNef toricDivisor L)
   SeeAlso
     (exteriorPower, ZZ, ToricReflexiveSheaf)
 ///
 
doc ///
   Key
     (exteriorPower, ZZ, ToricReflexiveSheaf)
   Headline
     make the exterior power of a toric reflexive sheaf
   Usage
      exteriorPower(p, E)
   Inputs
     p:ZZ
     E:ToricReflexiveSheaf
   Outputs
     :ToricReflexiveSheaf     
       the {\tt p}-th exterior power of {\tt E}
   Description
     Text
       Under the Klyachko equivalence of categories, the exterior power of a
       toric reflexive sheaf $E$ is determined by the exterior power of a
       vector space corresponding to $E$ equipped with the induced family of
       separated exhaustive descreasing filtrations indexed by the irreducible
       torus-invariant divisors.
              
     Text
       The top exterior power of the tangent bundle corresponds to the
       anti-canonical divisor.
     Example
       (X,R) = (toricProjectiveSpace(2), QQ[e_1,e_2]);
       W = {{(-e_1-e_2,1),(e_1,0)},{(e_1,1),(e_2,0)},{(e_2,1),(e_1,0)}};
       TX = toricReflexiveSheaf(W,X);
       rank TX
       describe TX
       TX2 = exteriorPower(2,TX);
       rank TX2
       describe TX2
       toricDivisor TX2 == - toricDivisor X
     Text
       If $E$ has rank $r$, then the $p$-th symmetric power has rank $r$
       choose $p$.  In 
     Example
       (X,R) = (toricProjectiveSpace 2, QQ[e_1,e_2,e_3]);
       W' = {{(e_1-e_2,5), (e_2-e_3,2), (e_1,-1)}, {(e_1,6), (e_2,0), (e_3,-1)}, {(e_3,3), (e_2,0), (e_1,-4)}};
       E = toricReflexiveSheaf(W', X);
       r = rank E
       describe E
       apply(components cover E, L -> OO toricDivisor L)
       E2 = exteriorPower(2,E);
       rank E2 == binomial(r,2)
       describe E2
       --all(components cover E2, L -> isNef toricDivisor L)
   SeeAlso
     (exteriorPower, ZZ, ToricReflexiveSheaf)
 ///
 
 doc ///
   Key
     (determinant, ToricReflexiveSheaf)
   Headline
     make the top exterior power of a toric reflexive sheaf
   Usage
      det E
   Inputs
     E:ToricReflexiveSheaf
   Outputs
     :ToricReflexiveSheaf     
       the to exterior power of {\tt E}
   Description
     Text
       If a toric reflexive sheaf has rank $r$, then its $r$-th exterior power
       has rank $1$.
       
     Text
       The top exterior power of the tangent bundle corresponds to the
       anti-canonical divisor.  
     Example
       (X,R) = (toricProjectiveSpace(2), QQ[e_1,e_2]);
       W = {{(-e_1-e_2,1),(e_1,0)},{(e_1,1),(e_2,0)},{(e_2,1),(e_1,0)}};
       TX = toricReflexiveSheaf(W,X);
       rank TX
       describe TX
       TX2 = det TX;
       rank TX2
       describe TX2
       toricDivisor TX2 == - toricDivisor X
     Example
       (X,R) = (toricProjectiveSpace 2, QQ[e_1,e_2,e_3]);
       W' = {{(e_1-e_2,5), (e_2-e_3,2), (e_1,-1)}, {(e_1,6), (e_2,0), (e_3,-1)}, {(e_3,3), (e_2,0), (e_1,-4)}};
       E = toricReflexiveSheaf(W', X);
       r = rank E
       describe E
       E3 = det E
       rank E3
       describe E3
       toricDivisor E3
   Caveat
     The method ignores the optional arguments.
   SeeAlso
     (exteriorPower, ZZ, ToricReflexiveSheaf)
 ///


 ///
   Key
     mukaiLazarsfeldBundle
     (mukaiLazarsfeldBundle, ToricDivisor)
   Headline
     make the kernel bundle 
   Usage
      mukaiLazarsfeldBundle D
   Inputs
     D:ToricDivisor
   Outputs
     :ToricReflexiveSheaf     
       representing the kernel of the map from the space of global sections to
       the corresponding rank-one reflexive sheaf
   Description
     Text
       If the toric divisor {\tt D} is globally generated, then the
       Mukai-Lazarsfeld bundle is the kernel of the canonial surjective map
       from the vector space global sections of {\tt OO(D)} tensor the
       structure sheaf {\tt OO_X} to the line bundle {\tt OO(D)}.
       
     Text
       The Euler sequence realizes a twist of the cotangent bundle on
       projective space as a Mukai-Lazarsfeld bundle.       
     Example
       X = toricProjectiveSpace(2);
       ML = mukaiLazarsfeldBundle X_0
       E = cover toricReflexiveSheaf X_0
       describe ML
       rank ML    
     Text
       ML2 = mukaiLazarsfeldBundle(2*X_0);
       describe ML2
   SeeAlso
     ToricDivisor
 ///
 
 doc ///
   Key
     ToricReflexiveSheafMap
   Headline
     the class of all the equivariant maps between toric reflexive sheaves
   Description
     Text
       Theorem 1.3.2 in Klyachko's @HREF
       ("http://www.mpim-bonn.mpg.de/preblob/4712","Vector bundles and torsion
       free sheaves on the projective plane")@ establishes that the category
       of toric reflexive sheaves is equivalent to the category of vector
       spaces with a family of separated exhaustive decreasing filtrations
       indexed by the irreducible torus-invariant divisors.  Under this
       equivalence, an equivariant map of toric reflexive sheaves corresponds
       to a linear map between the ambient vector spaces that is compatible
       with the families of separated exhaustive decreasing filtrations.
       Specifically, the image of each part in a filtration associated to the
       source lies in the corresponding part in the filtration associated to
       the target.
   SeeAlso
     (ambient, ToricReflexiveSheaf)
///
 
doc ///
   Key
     (source, ToricReflexiveSheafMap)
   Headline
     get the source
   Usage
     source f
   Inputs
     f:ToricReflexiveSheafMap
   Outputs
     :ToricReflexiveSheaf     
        the source of the equivariant map of toric reflexive sheaf
   Description
     Text
       For identity map on the tangent bundle on projective $2$-space, we see
       that the source and target is just the tangent bundle.
     Example
       (X,R) = (toricProjectiveSpace(2), QQ[e_1,e_2]);
       W = {{(-e_1-e_2,1),(e_1,0)},{(e_1,1),(e_2,0)},{(e_2,1),(e_1,0)}};
       TX = toricReflexiveSheaf(W,X);
       f = map(TX, TX, 1)
       source f
       source f === TX
     Text
       By definition, the generators of a toric reflexive sheaf is the
       equivariant map from its cover to itself.
     Example
       F = cover TX
       g = gens TX
       source g === F
   SeeAlso
     (target, ToricReflexiveSheafMap)
///
 
doc ///
  Key
    (target, ToricReflexiveSheafMap)
  Headline
    get the target
  Usage
    target f
  Inputs
    f:ToricReflexiveSheafMap
  Outputs
    :ToricReflexiveSheaf     
      the target of the equivariant map of toric reflexive sheaf
  Description
    Text
      For identity map on the tangent bundle on projective $2$-space, we see
      that the source and target is just the tangent bundle.
    Example
      (X,R) = (toricProjectiveSpace(2), QQ[e_1,e_2]);
      W = {{(-e_1-e_2,1),(e_1,0)},{(e_1,1),(e_2,0)},{(e_2,1),(e_1,0)}};
      TX = toricReflexiveSheaf(W,X);
      f = map(TX, TX, 1)
      target f
      target f === TX
    Text
      By definition, the generators of a toric reflexive sheaf is the
      equivariant map from its cover to itself.
    Example
      F = cover TX
      g = gens TX
      target g === TX
  SeeAlso
    (source, ToricReflexiveSheafMap)
///
 
doc ///
  Key
    (matrix, ToricReflexiveSheafMap)
  Headline
    get the underlying linear map
  Usage
    matrix f
  Inputs
    f:ToricReflexiveSheafMap
  Outputs
    :Matrix     
      the underlying linear map between corresponding vector spaces
  Description
    Text
      Under the Klyachko equivalence, an equivariant map of toric reflexive
      sheaves corresponds to a linear map between the ambient vector spaces
      that is compatible with the families of separated exhaustive decreasing
      filtrations.  Specifically, the image of each part in a filtration
      associated to the source lies in the corresponding part in the
      filtration associated to the target.  This routine returns the
      correpsonding linear map represented as a matrix relatively the the
      monomial basis for the homogeneous component of the ambient ring.
       
    Text
      For identity map on the tangent bundle on projective $2$-space, we get
      the identity matrix.
    Example
      (X,R) = (toricProjectiveSpace(2), QQ[e_1,e_2]);
      W = {{(-e_1-e_2,1),(e_1,0)},{(e_1,1),(e_2,0)},{(e_2,1),(e_1,0)}};
      TX = toricReflexiveSheaf(W,X);
      rank TX       
      f = map(TX, TX, 1)
      matrix f
    Text
      By definition, the generators of a toric reflexive sheaf is the
      equivariant map from its cover to itself.  In this case, the matrix
      captures the coefficients of the elements in the ground set.
    Example
      F = cover TX
      g = gens TX
      groundSet TX
  Caveat
    This routine ignores the option arguments.
  SeeAlso
    (ambient, ToricReflexiveSheaf)
    (groundSet, ToricReflexiveSheaf)
    (generators, ToricReflexiveSheaf)
///

doc ///
  Key
    (generators, ToricReflexiveSheaf)
  Headline
    gets the equivariant map from the cover    
  Usage
    generators E
    gens E
  Inputs
    E:ToricReflexiveSheaf
  Outputs 
    :ToricReflexiveSheafMap
  Description
    Text     
      Proposition 1.1. in DiRocco-Jabbusch-Smith's @HREF
      ("https://arxiv.org/abs/1409.3109", "Toric vector bundles and
      parliaments of polytopes")@ describes the minimal collection of toric
      line bundles that surject onto the global sections of a toric vector
      bundle.  This method returns the equivariant map from this the direct
      sum of the rank-one toric reflexive sheaves to the given toric reflexive
      sheaf.
       
    Text
      The underlying matrix of this map captures the coefficients of the
      elements in the ground set      
    Example
      (X,R) = (toricProjectiveSpace(2), QQ[e_1,e_2]);
      W = {{(-e_1-e_2,1),(e_1,0)},{(e_1,1),(e_2,0)},{(e_2,1),(e_1,0)}};
      TX = toricReflexiveSheaf(W,X);
      F = cover TX;
      gens TX       
      rank TX
      rank F
      groundSet TX
  Caveat
    The method ignores the optional arguments.    
  SeeAlso
    (cover, ToricReflexiveSheaf)
///
 
document {
   Key => 
     {(isWellDefined, ToricReflexiveSheafMap)},
   Headline =>
     "whether an equivariant map of toric reflexive sheaves is well-defined",
   Usage =>
     "isWellDefined f",
   Inputs =>
     {"f" => ToricReflexiveSheafMap},
   Outputs =>
     {Boolean => 
       {TO "true", " if the linear map determines an equivariant map of toric 
	 reflexive sheaves"}},

       "A linear map between the ambient vector spaces of two toric reflexive
       sheaves determines an equivariant map of toric reflexives sheaves if
       the following conditions hold:",
       UL{
	 "the source and target have the same underlying normal toric variety",
	 {"the linear map is compatible with the filtrations; the image of
	   each part in the filtrations associated to the source lies in the
	   corresponding part in the filtration associated to the target."},
	 },
     PARA{},
       "The identity map and the zero map yield equivariant maps of toric
       reflexive sheaves.",
     EXAMPLE lines ///
       (X,R) = (toricProjectiveSpace(2),QQ[e_1,e_2]);
       W = {{(-e_1-e_2,1),(e_1,0)},{(e_1,1),(e_2,0)},{(e_2,1),(e_1,0)}};
       TX = toricReflexiveSheaf(W,X);
       f = map(TX, TX, 1)
       isWellDefined f
       isWellDefined map(TX, TX, 0)
       ///,
     PARA{},
       "There is a canonical map from the arithmetically-free toric reflexive sheaf
       that covers a given toric reflexive sheaf.",       
     EXAMPLE lines ///
       F = cover TX
       g = gens TX
       isWellDefined g
       source g
       target g
       matrix g
       ///,       
     PARA{},
       "The next examples illustrate various ways that the input can fail to
       define an equivariant map of toric reflexive sheaves.",
     EXAMPLE lines ///
       (Y,S) = (toricProjectiveSpace(1) ** toricProjectiveSpace(1), QQ[e_1,e_2,e_3]);
       V = {{(e_1+e_3,1),(e_3,0),(e_2,-1)},{(e_1+e_2,1),(e_2,0),(e_3,-1)},{(e_2,2),(e_3,1),(e_1+e_3,0)},{(e_2,2),(e_3,1),(e_1+e_2,0)}};
       E1 = toricReflexiveSheaf(V,Y);
       isWellDefined E1
       debugLevel = 1;       
       f1 = map(TX,E1,0)
       isWellDefined f1
       ///,
     EXAMPLE lines ///   
       R' = ZZ/101[e_1,e_2];
       W' = {{(-e_1-e_2,1),(e_1,0)},{(e_1,1),(e_2,0)},{(e_2,1),(e_1,0)}};
       E2 = toricReflexiveSheaf(W',X);
       isWellDefined E2
       f2 = map(TX, E2, 1)       
       isWellDefined f2         
       ///,
     EXAMPLE lines ///         
      	f3 = map(TX, TX, {{1,0},{1,1}})
	isWellDefined f3
	basis(1,R)
	subspace(0,1,TX)
       ///,
     PARA{},
       "This method also checks that the following aspects of the data
       structure:",      
       UL {
	 {"the underlying ", TO HashTable, " has the expected keys, namely ",
	   TT "source", ", ", TT "target", ", ", TT "matrix", ", and ", 
	   TT "cache"},
	 {"the value of the ", TT "source", " key is a ", 
	   TO ToricReflexiveSheaf},
	 {"the value of the ", TT "target", " key is a ", 
	   TO ToricReflexiveSheaf},	 
	 {"the value of the ", TT "cache", " key is a ", TO CacheTable}
	 },
   SeeAlso => {
     (cover, ToricReflexiveSheaf)
     }
}


------------------------------------------------------------------------------
-- TESTS
------------------------------------------------------------------------------

TEST ///
  -- TEST 0: verify everything works for the tangent bundle on projective 2-space
  (X,R) = (toricProjectiveSpace 2, QQ[e_1,e_2]);
  W = {{(-e_1-e_2,1),(e_1,0)},{(e_1,1),(e_2,0)},{(e_2,1),(e_1,0)}};
  T = toricReflexiveSheaf(W, X);
  assert isWellDefined T
  assert not isArithmeticallyFree T
  assert isLocallyFree T
  assChar = associatedCharacters T;
  assert(set assChar#0 === set ({0,-1},{1,-1}))
  assert(set assChar#1 === set ({ -1,0},{ -1,1}))
  assert(set assChar#2 === set ({1,0},{0,1}))  
  assert isGloballyGenerated T
  assert(rank T == dim X)
  assert((R,{1}) === ambient T)
  assert(X === variety T)
  assert(subspace(0,infinity,T) == ideal(0_R))
  assert(subspace(0,1,T) == ideal(R_0 + R_1))
  assert(subspace(0,0,T) == ideal(R_0, R_1))
  assert(subspace(0,-infinity,T) == ideal(R_0, R_1))    
  assert(subspace(1,infinity,T) == ideal(0_R))  
  assert(subspace(1,1,T) == ideal(R_0))
  assert(subspace(1,0,T) == ideal(R_0, R_1))
  assert(subspace(1,-infinity,T) == ideal(R_0, R_1))      
  assert(subspace(2,infinity,T) == ideal(0_R))    
  assert(subspace(2,1,T) == ideal(R_1))
  assert(subspace(2,0,T) == ideal(R_0, R_1))
  assert(subspace(2,-infinity,T) == ideal(R_0, R_1))  
  assert({R_0+R_1,R_0,R_1} == groundSet T)
  F = cover T;
  assert(rank F == # groundSet T)
  assert isWellDefined F
  assert isArithmeticallyFree F
  assert isLocallyFree F
  assert(gens F == 1)
  f = gens T;
  assert(isWellDefined f)
  assert(source f === F)
  assert(target f === T)
  assert(matrix f == matrix {{1_QQ, 1, 0}, {1, 0, 1}})  
  (R,d) = ambient F;
  assert(numgens R == 3)
  assert(d == {1})
  assert(X === variety F)	 
  describe F  
  assert(subspace(0,infinity,F) == ideal(0_R))
  assert(subspace(0,1,F) == ideal(R_0))
  assert(subspace(0,0,F) == ideal(R_0, R_1, R_2))
  assert(subspace(0,-infinity,F) == ideal(R_0, R_1, R_2))    
  assert(subspace(1,infinity,F) == ideal(0_R))  
  assert(subspace(1,1,F) == ideal(R_1))
  assert(subspace(1,0,F) == ideal(R_0, R_1, R_2))
  assert(subspace(1,-infinity,F) == ideal(R_0, R_1, R_2))      
  assert(subspace(2,infinity,F) == ideal(0_R))    
  assert(subspace(2,1,F) == ideal(R_2))
  assert(subspace(2,0,F) == ideal(R_0, R_1, R_2))
  assert(subspace(2,-infinity,F) == ideal(R_0, R_1, R_2))    
  assert(apply(# rays X, i -> X_i) === apply(components F, E -> toricDivisor E))
  assert(isWellDefined directSum apply(# rays X, i -> toricReflexiveSheaf X_i))
  assert(isWellDefined(T ** (X_0+X_1+X_2)))
///

TEST ///
  -- TEST 1: verify everything for direct sums of line bundles
  X = smoothFanoToricVariety(3,15)
  L = toricReflexiveSheaf (- toricDivisor X)
  assert(variety L === X)
  assert(rank L === 1)
  assert({1} === (ambient L)#1)
  assert(coefficientRing (ambient L)#0 === QQ)
  assert(numgens (ambient L)#0 === 1)
  assert isWellDefined L
  assert isArithmeticallyFree L
  assert isLocallyFree L
  assChar = associatedCharacters L;
  all(#max X, 
    i -> all(entries (matrix ((rays X)_((max X)#i) ) * (transpose matrix assChar#i)), 
      e -> e === {1}))
  assert isGloballyGenerated L
  assert(toricDivisor L == - toricDivisor X)
  assert(# groundSet L === 1)
  describe det L
  describe L
  assert(det L === L)
  assert(toricDivisor symmetricPower(0,L) == 0*X_0)
  assert(toricDivisor symmetricPower(2,L) == -2 * toricDivisor X)
  assert(toricDivisor symmetricPower(3,L) == -3 * toricDivisor X)
  assert(isWellDefined gens L)
  assert(matrix gens L == id_(QQ^1))
  D = X_0 + 2*X_1 + 3*X_2 + 4*X_3 + 2*X_4 + 2*X_5 + X_6
  L' = L ** D
  assert(isWellDefined L')
  assert(toricDivisor L' == D - toricDivisor X)  
  L'' = toricReflexiveSheaf( 2*X_0 + X_1 + 2*X_2 + X_3 + 2*X_4 + X_5 + 2*X_6)
  assert(isWellDefined L')    
  E = L'' ++ L
  assert(isWellDefined E)
  assert(rank E === 2)
  assert(variety E === X)
  assert(isArithmeticallyFree E)
  assert(set components E - set(L'', L) === set {})
  f = map(E,E,3)
  assert(isWellDefined f)
  assert(matrix f == 3*id_(QQ^2))
  assert(rank ker f === 0)
  assert(ambient ker f === ambient source f)
  assert(toricDivisor det E == toricDivisor L'' + toricDivisor L)
///

TEST ///
  -- TEST 2: a rank three toric vector bundle that is ample but not globally generated
  (X,R) = (toricProjectiveSpace 2, QQ[e_1,e_2,e_3]);
  W = {{(e_1-e_2,5), (e_2-e_3,2), (e_1,-3)}, {(e_1,8), (e_2,0), (e_3,-1)}, 
    {(e_3,5), (e_2,0), (e_1,-4)}};
  E = toricReflexiveSheaf(W, X);
  assert isWellDefined E
  assert not isArithmeticallyFree E
  assert isLocallyFree E
  assChar = associatedCharacters E;
  assert(set assChar#0 === set ({8,-5},{0,-5},{ -1,-1}))
  assert(set assChar#1 === set ({ -1,-4},{ -2,0},{ -2,5}))
  assert(set assChar#2 === set ({8,-4},{0,0},{ -1,5}))  
  assert not isGloballyGenerated E
  describe E
  assert(rank E === 3)
  assert(groundSet E === {e_1, -e_1+e_2, e_2, -e_2+e_3, e_3})
  assert(apply(components cover E, L -> toricDivisor L) === { 
      -3*X_0+8*X_1-4*X_2, 5*X_0-4*X_2, -3*X_0, 2*X_0-X_1, -3*X_0-X_1+5*X_2})
  Eneg = symmetricPower(-1,E);
  assert isWellDefined Eneg
  rank Eneg === 0
  E0 = symmetricPower(0,E);
  assert(isWellDefined E0)
  assert(rank E0 === 1)
  E1 = symmetricPower(1,E)
  assert(E1 === E)
  E2 = symmetricPower(2,E);
  assert(isWellDefined E2)
  assert(rank E2 === binomial(rank E + 2 - 1, 2))
  ER = ring (groundSet E2)#0
  --assert(groundSet E2 == {ER_0^2-2*ER_0*ER_1+ER_1^2, ER_0^2,
  --    -ER_0^2+ER_0*ER_1, ER_0*ER_1-ER_1^2-ER_0*ER_2+ER_1*ER_2, ER_0*ER_1,
  --    -ER_0*ER_1+ER_0*ER_2,-ER_0*ER_2+ER_1^2, ER_1^2-2*ER_1*ER_2+ER_2^2,
  --    -ER_1^2+ER_1*ER_2, ER_0*ER_2, -ER_0*ER_2+ER_1*ER_2, ER_1*ER_2,
  --    -ER_1*ER_2+ER_2^2, ER_2^2})
  F2 = cover E2;
  assert(rank F2 == # groundSet E2)
  assert(isWellDefined F2)
  assert(isArithmeticallyFree F2)
  f = gens E2;
  assert(isWellDefined f)
  assert(source f === F2)
  assert(target f === E2)
///

TEST ///
  -- TEST 3 : Euler sequence on projective 3-space
  (X,R) = (toricProjectiveSpace 3, QQ[e_1..e_3]);
  W = {{(-e_1-e_2-e_3,1),(e_1,0),(e_2,0)},{(e_1,1),(e_2,0),(e_3,0)},{(e_2,1),(e_1,0),(e_3,0)},{(e_3,1),(e_1,0),(e_2,0)}};
  T = toricReflexiveSheaf(W,X);
  assert(isWellDefined T)
  assert(not isArithmeticallyFree T)
  F0 = cover T
  assert(isWellDefined F0)
  assert(isArithmeticallyFree F0)
  assert(rank F0 === 4)
  d0 = gens T
  assert(isWellDefined d0)
  K0 = ker d0
  assert(isWellDefined K0)
  assert(rank K0 === 1)
  iota = map(F0, K0, 1)
  assert(isWellDefined iota)
  F1 = cover K0
  assert(isWellDefined F1)
  assert(rank F1 == rank K0)
  f1 = gens K0
  assert(isWellDefined f1)
  d1 = iota * f1
  assert(isWellDefined d1)
  assert(d0 * d1 == 0)
///  

TEST ///
  -- TEST 4 : verifies routine on the zero sheaf
  (X,R) = (toricProjectiveSpace(2), QQ[e_1,e_2]);
  Z = toricReflexiveSheaf(R,{1},X);
  assert isWellDefined Z
  assert isArithmeticallyFree Z
  assert isLocallyFree Z
  assert(associatedCharacters Z === apply(max X, s -> {}))
  assert isGloballyGenerated Z
  assert((R,{1}) === ambient Z)
  assert(rank Z === 0)
  assert(variety Z === X)
  assert(components Z === {Z})
  assert(Z ++ Z === Z)
  assert(directSum(11:Z) === Z)
  assert(subspace(0,0,Z) == 0)
  assert(subspace(0,-4,Z) == 0)
  assert(subspace(0,infinity,Z) == 0)
  assert(subspace(0,-infinity,Z) == 0)
  assert isWellDefined map(Z,Z,1)
  assert(groundSet Z === {})
  assert isArithmeticallyFree Z
  assert(cover Z === Z)
  assert(gens Z == 0)
  assert(rank exteriorPower(-1,Z) === 0)
  assert( (ambient exteriorPower(-2,Z))#1 === { -2})
  assert( (ambient exteriorPower(7,Z))#1 === {7})  
  assert(exteriorPower(1,Z) === Z)  
  assert(rank exteriorPower(2,Z) === 0) 
  assert(rank symmetricPower(-1,Z) === 0)     
  assert( (ambient symmetricPower(-1,Z))#1 === { -1})    
  assert(rank symmetricPower(2,Z) === 0)       
///

TEST ///
  -- TEST 5 : verifies toricTangentBundle routine
  T = toricTangentBundle toricProjectiveSpace 2;
  assert isWellDefined T
  assert isLocallyFree T
  (R,d) = ambient T;
  for i from 0 to # rays variety T - 1 do (
    assert(subspace(i,0,T) == ideal basis(d,R));
    assert(subspace(i,1,T) == ideal(vars R * transpose matrix{(rays variety T)#i}));
    assert(subspace(i,2,T) == 0))
  T = toricTangentBundle toricProjectiveSpace 4;
  assert isWellDefined T
  (R,d) = ambient T;
  for i from 0 to # rays variety T - 1 do (
    assert(subspace(i,0,T) == ideal basis(d,R));
    assert(subspace(i,1,T) == ideal(vars R * transpose matrix{(rays variety T)#i}));
    assert(subspace(i,2,T) == 0))
  T = toricTangentBundle smoothFanoToricVariety(3,15);
  assert isWellDefined T  
  (R,d) = ambient T;
  for i from 0 to # rays variety T - 1 do (
    assert(subspace(i,0,T) == ideal basis(d,R));
    assert(subspace(i,1,T) == ideal(vars R * transpose matrix{(rays variety T)#i}));
    assert(subspace(i,2,T) == 0))
///

------------------------------------------------------------------------------
end---------------------------------------------------------------------------
------------------------------------------------------------------------------




------------------------------------------------------------------------------
-- methods to be added to package

dual ToricReflexiveSheaf := ToricReflexiveSheaf => E -> (  
ToricReflexiveSheaf ** ToricReflexiveSheaf := ToricReflexiveSheaf => (E,F) -> (
sheafHom (ToricReflexiveSheaf, ToricReflexiveSheaf) := ToricReflexiveSheaf => (E,F) -> (
euler ToricReflexiveSheaf := ZZ => E -> (
toricEuler ToricReflexiveSheaf := RingElement => E -> (

isAmple ToricReflexiveSheaf := Boolean => E -> (
isVeryAmple ToricReflexiveSheaf := Boolean => E -> (
isBasePointFree ToricReflexiveSheaf := Boolean => E -> (
cohomology ToricReflexiveSheaf := 

cokernel ToricReflexiveSheafMap
image ToricReflexiveSheafMap
coimage ToricReflexiveSheafMap
ToricReflexiveSheaf _ Array := ToricReflexiveSheafMap => (E,v) -> (
ToricReflexiveSheaf ^ Array := ToricReflexiveSheafMap => (E,v) -> (  
  
chowRing, chern classes, etc.

------------------------------------------------------------------------------
uninstallPackage "Parliaments"
restart
installPackage "Parliaments"
check "Parliaments"


-- Example 3.8
X = toricProjectiveSpace(1) ** toricProjectiveSpace (1);
S = QQ[e_1..e_3];
W = {{(e_1+e_2,1),(e_2,0),(e_3,-1)},{(e_1+e_2,0),(e_2,2),(e_3,1)},
  {(e_1+e_3,1),(e_2,-1),(e_3,0)},{(e_1+e_3,0),(e_2,2),(e_3,1)}}
E = toricReflexiveSheaf(W,X);
describe E
subspacePoset E
groundSet E
A = arrangement groundSet E
flats A
ideal X
rays X
length 
(R,d) = ambient E


-- Example: direct sum of two line bundles
X = toricProjectiveSpace(2);
S = QQ[e_1..e_2];
W = {{(e_1,1),(e_2,2)},{(e_1,0),(e_2,1)},{(e_1,0),(e_2,1)},}
E = toricReflexiveSheaf(W,X)
isWellDefined E
describe E
subspacePoset E
groundSet E

-- Example: tangent bundle ++ a line bundle
X = toricProjectiveSpace(2);
S = QQ[e_1..e_3];
W = {{(-e_1-e_2,3),(e_3,1),(e_1,-1)},{(e_1,3),(e_3,1),(e_2,-1)},
  {(e_2,4),(e_3,1),(e_1,0)}}
E = toricReflexiveSheaf(W,X)
isWellDefined E
subspacePoset E
groundSet E
needsPackage "HyperplaneArrangements";
A = arrangement groundSet E
flats A

X = toricProjectiveSpace 2;
E = mukaiLazarsfeldBundle (2*X_1)
exteriorPower(2,E)
isWellDefined E
E ** (2*X_0 - 2*X_1)
mukaiLazarsfeldBundle (2*X_0)
E#0

toricReflexiveSheaf({{},{},{}},X)


------------------------------------------------------------------
-- BERNT IVAR's EXAMPLE
restart
installPackage "Parliaments"
X = normalToricVariety({{1,0},{1,1},{1,2},{0,1},{ -1,0},{0,-1}},{{0,1},{1,2},{2,3},{3,4},{4,5},{0,5}})
isWellDefined X
isSmooth X
S = QQ[e_1,e_2];
L = {{(e_2,130),(e_1,339)}, {(e_2,-246),(e_1,324)}, {(e_2,-375),(e_1,442)}, {(e_2,61),(e_1,232)}, 
  {(e_1,79),(e_2,535)}, {(e_2,91),(e_1+e_2,414)}}
E = toricReflexiveSheaf(L,X)  
isWellDefined E
groundSet E

describe E

E#0
subspace(E,0,
  

needsPackage "Polyhedra"

------------------------------------------------------------------------------
XXX
------------------------------------------------------------------------------
uninstallPackage "Parliaments"
restart
path = prepend("~/MyDocuments/Research/ToricVectorBundles/", path)
installPackage "Parliaments"
check "Parliaments"

restart
needsPackage "Parliaments"

X = toricProjectiveSpace 2
E = toricTangentBundle X
outerNormals = matrix rays X;
assChar = associatedCharacters E
G = groundSet E
(R,d) = ambient E
(M,C) = coefficients( matrix {G}, Monomials => basis(d,R))
divisors = apply(components cover E, L -> toricDivisor L)
Sigma = max X

i = 0
j = 0
u = assChar#i#j
(max X)#i
charVector = transpose matrix {u}
(first transpose entries(outerNormals * charVector - matrix vector divisors#j))_((max X)#i)

coordinates = submatrix(outerNormals * charVector - matrix vector divisors#j,(max X)#i,)
first transpose entries coordinates

(X,R) = (toricProjectiveSpace 2, QQ[e_1,e_2,e_3]);
W = {{(e_1-e_2,5), (e_2-e_3,2), (e_1,-3)}, {(e_1,8), (e_2,0), (e_3,-1)}, 
  {(e_3,5), (e_2,0), (e_1,-4)}};
E = toricReflexiveSheaf(W, X);
outerNormals = matrix rays X
assChar = associatedCharacters E
G = groundSet E
(R,d) = ambient E
(M,C) = coefficients( matrix {G}, Monomials => basis(d,R))
divisors = apply(components cover E, L -> toricDivisor L)
i = 2
max X
u = assChar#i#1
      potentialBases := for u in assChar#i list (
      	charVector = transpose matrix {u}
      	select(#G, j -> (
	    j = 1
	    coordinates = outerNormals*charVector - matrix vector divisors#j
	    coordinates_(1,0)
	    member(1, (max X)#i)
	    
	    << coordinates << endl;
	    localCoordinates := transpose submatrix(coordinates,(max X)#i,);
	    all(first entries coordinates, c -> c == 0))
	  )
      any(boxProduct potentialBases, s -> det C_s =!= 0))));  




isGloballyGenerated = method()
isGloballyGenerated ToricReflexiveSheaf := Boolean => E -> (
  if E == 0 then return true;
  X := variety E;
  outerNormals := matrix rays X;
  n := # rays X;
  assChar := associatedCharacters E;
  G := groundSet E;
  (R,d) := ambient E;
  (M,C) := coefficients( matrix {G}, Monomials => basis(d,R));
  divisors := apply(components cover E, L -> toricDivisor L);
  all(#assChar, i -> (
      potentialBases := for u in assChar#i list (
      	charVector := transpose matrix {u};
      	select(#G, j -> (
	    coordinates := outerNormals*charVector - matrix vector divisors#j;
	    all(n, k -> if member(k, (max X)#i) then coordinates_(k,0) == 0 
	      else coordinates_(k,0) <= 0))));
      any(boxProduct potentialBases, s -> det C_s =!= 0))));  




X = smoothFanoToricVariety(3,15)
L = toricReflexiveSheaf (- toricDivisor X)
OO toricDivisor L
describe L
sigma = (max X)#0
U = normalToricVariety((rays X)_sigma, {toList(0..#sigma - 1)} )
isWellDefined U
LU = toricReflexiveSheaf(for i in sigma list pairs L#i,U);
isWellDefined LU
G = groundSet LU
reverse sort unique values LU#0
G#0 % subspace(0, 1, LU)
C = transpose matrix for g in G list (
    for i to # rays U - 1 list (
      weights := reverse sort unique values LU#i;
      j := 0;
      while g % subspace(i, weights#j, LU) != 0 do j = j+1;
      j));
   <<

    entries transpose ((inverse matrix rays U) * C)


transpose inverse matrix rays U

associatedCharacters T
max X
rays X
G = groundSet TU
C = for g in G list (
  for i from 0 to # rays U - 1 list (
    weights := reverse sort unique values TU#i;
    j := 0;
    while g % subspace(i, weights#j, TU) != 0 do j = j+1;
    j))
entries transpose ((inverse matrix rays U)*matrix C)




W = {{(-e_1-e_2,1),(e_1,0)},{(e_1,1),(e_2,0)},{(e_2,1),(e_1,0)}};
T = toricReflexiveSheaf(W,X);

(X,R) = (toricProjectiveSpace 2, QQ[e_1, e_2])
D = X_0
ML =  D
rank ML
isWellDefined ML
F0 = cover ML
rank F0
epsilon = gens ML
K0 = ker epsilon
isWellDefined K0
F1 = cover K0
rank F1 
gens K0
d1 = map(F0, K0, 1) * (gens K0)
K1 = ker d1
K1 == 0 
epsilon * d1
C = complex {matrix epsilon, matrix d1}
degree C_0
(C, Weights => {-1})
help betti


C0 = (target matrix epsilon) ** QQ[]
C1 = (source matrix epsilon) ** QQ[]
C2 = (source matrix d1) ** QQ[]
degrees C1
degrees matrix d1
help (map, Module, Module, Matrix)
C = chainComplex (map(C0,C1,matrix epsilon),map(C1,C2, matrix d1))
C0 = target matrix epsilon
C1 = (source matrix epsilon) ** QQ[]
C2 = (source matrix d1) ** QQ[]
map(C0,C1,(matrix epsilon) ** QQ[])
betti C
break

options betti


needsPackage "Complexes"

D = 2*X_0
ML = mukaiLazarsfeldBundle D
rank ML
ambient ML
isWellDefined ML
F0 = cover ML
rank F0
epsilon = gens ML
K0 = ker epsilon
isWellDefined K0
F1 = cover K0
rank F1 
gens K0
d1 = map(F0, K0, 1) * (gens K0)
K1 = ker d1
K1 == 0 
epsilon * d1

betti 
chainComplex(matrix epsilon, matrix d1)

break


------------------------------------------------------------------------------
-- ZZZ
restart
needsPackage "Parliaments";
X = toricProjectiveSpace 2;
D = 2*X_0;
ML = mukaiLazarsfeldBundle D
E = exteriorPower(2, ML)
res E
res (E ** D)
res (ML ** D)

C = time res E;
C
display C

D = {{0, rank target maps#0}} | apply(#maps, 
  i -> {i+1, rank source maps#i} | apply(components source maps#i, L -> toricDivisor L))
transpose 
transpose netList
Table transpose D
help table

display
net 


D


------------------------------------------------------------------------------
-- SYZYGIES OF VERONESE EMBEDDINGS?
--

restart
needsPackage "Parliaments"

display = C -> (
  D := netList( transpose {{ -1, rank target C#0}}, 
    Boxes => false, Alignment => Center, VerticalSpace => 1);
  for i to #C - 1 do (
    D = D | "  " | (netList ( {i, rank source C#i} | apply(components source C#i, 
	  L -> HH^i(variety L, OO toricDivisor L)), 
  	Boxes => false, Alignment => Center, VerticalSpace => 1)));
  D);

-- PP^2;  OO(3)
X = toricProjectiveSpace 2;
D = 3 * X_0;
ML = mukaiLazarsfeldBundle D;
C = res (ML ** D);
display C
time display res (exteriorPower(2,ML) ** D)
time display res (exteriorPower(3,ML) ** D)
time display res (exteriorPower(4,ML) ** D)
time display res (exteriorPower(5,ML) ** D)
time display res (exteriorPower(6,ML) ** D)
time display res (exteriorPower(7,ML) ** D)
time display res (exteriorPower(8,ML) ** D)

-- PP^2;  OO(4)
X = toricProjectiveSpace 2;
D = 4 * X_0;
ML = mukaiLazarsfeldBundle D;
C = res (ML ** D)
display C
time display res (exteriorPower(2,ML) ** D)
time display res (exteriorPower(3,ML) ** D)
time display res (exteriorPower(4,ML) ** D)
time display res (exteriorPower(5,ML) ** D)
time display res (exteriorPower(6,ML) ** D)
time display res (exteriorPower(7,ML) ** D)
time display res (exteriorPower(8,ML) ** D)
time display res (exteriorPower(9,ML) ** D)
time display res (exteriorPower(10,ML) ** D)
time display res (exteriorPower(11,ML) ** D)

-- PP^2;  OO(5)
X = toricProjectiveSpace 2;
D = 5 * X_0;
ML = mukaiLazarsfeldBundle D;
C = res (ML ** D);
display C
time display res (exteriorPower(2,ML) ** D)
time display res (exteriorPower(3,ML) ** D)
time display res (exteriorPower(4,ML) ** D)
time display res (exteriorPower(5,ML) ** D)
time display res (exteriorPower(6,ML) ** D)
time display res (exteriorPower(7,ML) ** D)
time display res (exteriorPower(8,ML) ** D)
time display res (exteriorPower(9,ML) ** D)
time display res (exteriorPower(10,ML) ** D)
time display res (exteriorPower(11,ML) ** D)
time display res (exteriorPower(12,ML) ** D)
time display res (exteriorPower(13,ML) ** D)


-- PP^3;  OO(3)
X = toricProjectiveSpace 3;
D = 3 * X_0;
ML = mukaiLazarsfeldBundle D;
C = res (ML ** D);
display C
time display res (exteriorPower(2,ML) ** D)
time display res (exteriorPower(3,ML) ** D)
time display res (exteriorPower(4,ML) ** D)
time display res (exteriorPower(5,ML) ** D)
time display res (exteriorPower(6,ML) ** D)
time display res (exteriorPower(7,ML) ** D)
time display res (exteriorPower(8,ML) ** D)

-- PP^3;  OO(4)
X = toricProjectiveSpace 3;
D = 4 * X_0;
ML = mukaiLazarsfeldBundle D;
C = res (ML ** D);
display C
time display res (exteriorPower(2,ML) ** D)
time display res (exteriorPower(3,ML) ** D)
time display res (exteriorPower(4,ML) ** D)
time display res (exteriorPower(5,ML) ** D)
time display res (exteriorPower(6,ML) ** D)
time display res (exteriorPower(7,ML) ** D)
time display res (exteriorPower(8,ML) ** D)
time display res (exteriorPower(9,ML) ** D)
time display res (exteriorPower(10,ML) ** D)
time display res (exteriorPower(11,ML) ** D)

-- PP^3;  OO(5)
X = toricProjectiveSpace 3;
D = 5 * X_0;
ML = mukaiLazarsfeldBundle D;
C = res (ML ** D);
display C
time display res (exteriorPower(2,ML) ** D)
time display res (exteriorPower(3,ML) ** D)
time display res (exteriorPower(4,ML) ** D)
time display res (exteriorPower(5,ML) ** D)
time display res (exteriorPower(6,ML) ** D)
time display res (exteriorPower(7,ML) ** D)
time display res (exteriorPower(8,ML) ** D)
time display res (exteriorPower(9,ML) ** D)
time display res (exteriorPower(10,ML) ** D)
time display res (exteriorPower(11,ML) ** D)
time display res (exteriorPower(12,ML) ** D)
time display res (exteriorPower(13,ML) ** D)



-----------------------------------------------------------------
-- Andreas Hochenegger question
restart
needsPackage "Parliaments";
X = toricProjectiveSpace 2;
Omega = toricCotangentBundle X;
E = symmetricPower(2,Omega) ** (X_0+X_1+X_2)
parliament = apply(components cover E, L -> toricDivisor L)
#parliament
for D in parliament list HH^0(X, OO D)



------------------------------------------------------------------------------
-- Hiro example
restart
needsPackage "Parliaments";
(X,R) = (hirzebruchSurface 1, QQ[e_1,e_2]);
W = {{(e_1,4),(e_2,-2)}, {(e_1,3),(e_2,2)}, {(e_2,5),(e_1,0)}, {(e_1+e_2,3),(e_1,-1)}}
E = toricReflexiveSheaf(W,X);
describe E
resolution E
characters E
orbits(X, 0)
associatedCharacters E
toricDivisor exteriorPower(2,E)
intersectionRing X



(X,R) = (toricProjectiveSpace 2, QQ[y_1,y_2]);
E = toricTangentBundle X
describe E
A = ZZ/32003[gens ring X | gens (ambient E)#0];
B = ZZ/32003[z_0..z_8];
f = map(A,B, {A_0*A_1*A_2*A_3, A_0^2*A_2*A_3, A_0*A_2^2*A_3,
	 A_0*A_1^2*A_4, A_0^2*A_1*A_4, A_0*A_1*A_2*A_4,
	 A_1^2*A_2*(A_3+A_4), A_0*A_1*A_2*(A_3+A_4), A_1*A_2^2*(A_3+A_4)})
I = saturate(ideal mingens ker f, ideal gens B)
netlist =  I_*
codim I
hilbertPolynomial(I, Projective => false)

C = ZZ/32003[gens ring X | gens B];
gens C
M = matrix{
    {C_0*C_1*C_2, C_0^2*C_2, C_0*C_2^2, 0_C, 0_C, 0_C, C_1^2*C_2, C_0*C_1*C_2, C_1*C_2^2},
    {0_C, 0_C, 0_C, C_0*C_1^2, C_0^2*C_1, C_0*C_1*C_2, C_1^2*C_2, C_0*C_1*C_2, C_1*C_2^2},
    {C_3,C_4,C_5, C_6, C_7, C_8, C_9, C_10, C_11}}
saturate(minors(3,M), ideal(C_0,C_1,C_2))

M = matrix{{ 

(X,R) = (toricProjectiveSpace 2, QQ[y_1,y_2]);
E = toricTangentBundle X
describe E
A = ZZ/32003[gens ring X | gens (ambient E)#0];
B = ZZ/32003[z_0..z_8];
f = map(A,B, {A_0*A_1*A_2*A_3, A_0^2*A_2*A_3, A_0*A_2^2*A_3,
	 A_0*A_1^2*A_4, A_0^2*A_1*A_4, A_0*A_1*A_2*A_4,
	 A_1^2*A_2*(A_3+A_4), A_0*A_1*A_2*(A_3+A_4), A_1*A_2^2*(A_3+A_4)})
I = saturate(ideal mingens ker f, ideal gens B)
codim I
hilbertPolynomial(I, Projective => false)

