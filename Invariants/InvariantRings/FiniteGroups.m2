--This file contains finite group action methods improving on old InvariantRing
--TODO 6/26/20 
--1. Update and check list below: merge (?) with old InvariantRing
--2. Check state of documentation
--3. Check state of tests



-------------------------------------------
--- FiniteGroupAction methods -------------
-------------------------------------------

-- TO DO: 1. Port and improve the remaining methods from the package "InvariantRing"
--    	     to act on the type FiniteGroupAction (rewritten as hooks as appropriate).
--    	  2. Create examples/documentation/tests for FiniteGroupAction methods.
--    	  3. Write functions to extract list of cyclic factors/weights for FiniteGroupAction
--    	     that happens to be abelian.  
--    	  4. Add OrderBound option to prevent infinite loops if passed an infinite group.


FiniteGroupAction = new Type of GroupAction

finiteAction = method()

finiteAction (List, PolynomialRing) := FiniteGroupAction => (G, R) -> (
    if not isField coefficientRing R then (
	error "finiteAction: Expected the second argument to be a polynomial ring over a field."
	);
    if any (G, g -> not instance(g, Matrix) or numRows g =!= numColumns g) then (
	error "finiteAction: Expected the first argument to be a list of square matrices."
	);
    if (numRows first G) =!= dim R then (error "finiteAction: Expected the number of rows of each matrix to equal the number of variables in the polynomial ring."); 
    try (
	gensG := apply(G, g -> sub(g, coefficientRing R))
	)
    else (
	error "finiteAction: Expected a list of matrices over the coefficient field of the polynomial ring."
	);
    new FiniteGroupAction from {
	cache => new CacheTable,
	(symbol ring) => R, 
	(symbol generators) => gensG,
	(symbol numgens) => #(gensG),
	}
    )

finiteAction (Matrix, PolynomialRing) := FiniteGroupAction => (g, R) -> finiteAction({g}, R)


-------------------------------------------

net FiniteGroupAction := G -> (net G.ring)|" <- "|(net G.generators)
-- If the list of generators is long, consider rewriting  to print only the first few generators together with "...".
-- Or find a better way to print if the size of the matrices is large.

generators FiniteGroupAction := opts -> G -> G.generators
-- gens must pass 'opts' before the argument, or it will not run!!

numgens FiniteGroupAction := ZZ => G -> G.numgens


-------------------------------------------

isAbelian = method()

isAbelian FiniteGroupAction := { } >> opts -> (cacheValue (symbol isAbelian)) (G -> runHooks(FiniteGroupAction, symbol isAbelian, G) )

-- The syntax "{ } >>" above is very important for some reason.
-- The hooks will not work properly without it.

addHook(FiniteGroupAction, symbol isAbelian, G -> break (
	X := G.generators;
    	n := #X;
    	if n == 1 then(
	    true 
	    )
    	else(
	    all(n - 1, i -> all(n - 1 - i, j -> (X#j)*(X#(n - 1 - i)) == (X#(n - 1 - i))*(X#j) ) )
	    )
	  ))
  
  
-------------------------------------------

generateGroup = method()

generateGroup FiniteGroupAction := { } >> opts -> (cacheValue (symbol generateGroup)) (G -> runHooks(FiniteGroupAction, symbol generateGroup, G) )

addHook(FiniteGroupAction, symbol generateGroup, G -> break (
    m := numgens G;
    n := dim G;
    K := coefficientRing ring G;
    X := gens G;
    
    S := new MutableHashTable from apply(m, i -> 
	i => new MutableHashTable from {id_(K^n) => X#i}
	);
    -- A hashtable of hashtables.  The outer hashtable records the index i of each group 
    -- generator.  The hashtable S#i represents the directed edges in the Schreier graph
    -- corresponding to multiplication by the i-th generator.
    
    A := new MutableHashTable from {id_(K^n) => {{}}}|apply(m, i -> X#i => {{i}});
    -- A hashtable of addresses associating to each matrix in the group a list of words
    -- on the (indices of the) generators whose product is that matrix.
    -- This could be used to speed up the computation of multiplicative functions on the group elements
    -- by using the values on the generators only.
    -- It can also be used to create a set of relations for the group.
    
    toUpdate := X;
    -- A list of matrices in the group that have not yet been multiplied by every generator.
    
    local h; local a;
    while #toUpdate > 0 do(
	h = first toUpdate;
	a = first A#h;
	
	scan(m, i -> (
		g := h*(X#i);
		a' := a|{i};
		
		-- Add the directed edge h => g to the hashtable S#i.
		S#i#h = g;
		
		-- If the product g has appeared before, add the new address a' 
		-- to the list of existing ones.  Otherwise, create a new list of 
		-- addresses for g, and add g to the list of matrices to be updated.
		if A#?g then (
		    A#g = (A#g)|{a'}
		    )
		else (
		    A#g = {a'};
		    toUpdate = toUpdate|{g}
		    )
		)
	    );
	
	toUpdate = drop(toUpdate, 1);
	);
    A = hashTable pairs A;
    S = hashTable apply(keys S, i -> i => hashTable pairs S#i);
    (S, A)
    )) 


-------------------------------------------

schreierGraph = method()

schreierGraph FiniteGroupAction := { } >> opts -> (cacheValue (symbol schreierGraph)) (G -> runHooks(FiniteGroupAction, symbol schreierGraph, G) )

addHook(FiniteGroupAction, symbol schreierGraph, 
    G -> break (generateGroup G)_0  
    )    
   

-------------------------------------------

group = method()

group FiniteGroupAction := { } >> opts -> (cacheValue (symbol group)) (G -> runHooks(FiniteGroupAction, symbol group, G) )

addHook(FiniteGroupAction, symbol group, 
    G -> break keys first schreierGraph G  
    )

-------------------------------------------

words = method()

words FiniteGroupAction := { } >> opts -> (cacheValue (symbol words)) (G -> runHooks(FiniteGroupAction, symbol words, G) )

addHook(FiniteGroupAction, symbol words, 
    G -> break applyValues((generateGroup G)_1, val -> first val)
    )

-------------------------------------------

relations FiniteGroupAction := { } >> opts -> (cacheValue (symbol relations)) (G -> runHooks(FiniteGroupAction, symbol relations, G) )

addHook(FiniteGroupAction, symbol relations, G -> break (
    relators := values last generateGroup G;
    W := apply(relators, r -> first r);
    relators = flatten apply(#W, i -> apply(drop(relators#i, 1), a -> {W#i,a} ) );
    relators = apply(relators, r -> (
	    w1 := first r;
	    w2 := last r;
	    j := 0;
	    while (j < #w1 and w1#j == w2#j) do j = j + 1;
	    {drop(w1, j), drop(w2, j)}
	    )
	);
    unique relators 
    )) 

-------------------------------------------

-- Unexported function used to extract the cyclic factors of a FiniteGroupAction that is abelian.
-- Currently, this does not keep track of which generators of the group are the minimal generators 
-- corresponding to the cyclic factors.

-*
cyclicFactors = G -> (
    if not isAbelian G then (error "cyclicFactors: Expected group to be abelian.");
    relators := relations G;
    m := numgens G;
    relators = transpose matrix apply(relators, L -> (
	    counts := apply(L, l -> applyValues(partition(i -> i, l), val -> #val) );
	    counts = apply(counts, l -> apply(m, i -> if l#?i then l#i else 0) );
	    first counts - last counts
	    )
	);
    relators = relations minimalPresentation coker relators;
    apply(numRows relators, i -> relators_i_i)
    )

*-

-------------------------------------------

permutationMatrix = method()

permutationMatrix String := Matrix => s -> (
    n := #s;
    p := apply(n, i -> (
	    v := value(s#i);
	    if v <= 0 or v > n then (
		error "permutationMatrix: Expected a string of positive integers
		representing a permutation."
		)
	    else v
	    )
	);
    if #(unique p) =!= n then (
	error "permutationMatrix: Expected a string of distinct integers."
	);
    matrix apply(n, i -> 
	apply(n, j -> if p#j - 1 == i then 1 else 0)
	)
    )

permutationMatrix (ZZ, Array) := Matrix => (n, c) -> permutationMatrix(n, {c})

permutationMatrix (ZZ, List) := Matrix => (n, p) -> (
    if n <= 0 then (error "permutationMatrix: Expected the first input to be a positive integer.");
    if any(p, c -> not instance(c, Array) or any(c, i -> i <= 0 or i > n)) then (
	error "permutationMatrix: Expected the second input to be a list of arrays
	 with integer entries between 1 and the first input."
	 );
     if any(p, c -> #(unique toList c) =!= #c) then (error "permutationMatrix: Expected each sequence in 
	 the list to have distinct entries.");
     s := new MutableHashTable from apply(n, i -> i + 1 => i + 1);
     scan(p, c -> (
	     k := #c;
	     u := hashTable pairs s;
	     scan(k, j -> (
		     if j < k - 1 then s#(c_j) = u#(c_(j+1))
		     else s#(c_j) = u#(c_0)
		     )
		 )
	     )
	 );
     s = horizontalJoin apply(values s, i -> toString i);
     permutationMatrix toString s
     )  
	 
permutationMatrix Array := Matrix => c -> permutationMatrix(max c, c)

permutationMatrix List := Matrix => p -> permutationMatrix(max (p/max), p)	     
	 
	









