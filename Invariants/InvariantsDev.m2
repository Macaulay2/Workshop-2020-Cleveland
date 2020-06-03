-- -*- coding: utf-8 -*-
newPackage(
        "InvariantsDev",
        Version => "0.1", 
        Date => "May 13, 2020",
        Authors => {
             {Name => "Luigi Ferraro", Email => "ferrarl@wfu.edu", HomePage => "http://users.wfu.edu/ferrarl/"},
             {Name => "Federico Galetto", Email => "f.galetto@csuohio.edu", HomePage => "https://math.galetto.org"},
             {Name => "Francesca Gandini", Email => "fra.gandi.phd@gmail.com", HomePage => "https://sites.google.com/a/umich.edu/gandini/home"},
	     {Name => "Hang Huang", Email => "hhuang235@tamu.edu", HomePage => "https://math.tamu.edu/~hhuang"},
	     {Name => "Matthew Mastroeni", Email => "mmastro@okstate.edu", HomePage => "https://mnmastro.github.io/"},
             {Name => "Xianglong Ni", Email => "xlni@berkeley.edu", HomePage => "https://math.berkeley.edu/~xlni/"}
             },
        Headline => "Computing Invariants for Tori and Abelian Groups",
        DebuggingMode => true,
        AuxiliaryFiles => false
        )

-- TO DO: 1. Eliminate any unused exported symbols below.
--    	  2. Eliminate any unused protected symbols below.
--    	  3. Determine whether there are functions that do not need to be exported.


-- Any symbols or functions that the user is to have access to
-- must be placed in one of the following two lists

-- Type names must be exported if they are used in the documentation
-- of an overloaded function.

export {
    "action",	     	     	  -- documented
    "actionMatrix",
    "finiteAbelianAction",
    "FiniteAbelianAction",    	  -- exported type name
    "finiteAction",    	       	  -- documented
    "FiniteGroupAction",    	  -- exported type name
    "group",	    	    	  -- documented
    "GroupAction",    	      	  -- exported type name
    "hilbertIdeal",
    "invariants",    	     	  -- documented for TorusAction,FiniteAbelianAction
    "invariantRing",	    	  
    "isAbelian",    	    	  -- documented
    "isInvariant",    	      	  -- documented
    "linearlyReductiveAction",
    "reynoldsOperator",	       	  -- documented
    "permutationMatrix",
    "RingOfInvariants",	       	  -- exported type name
    "schreierGraph",
    "equivariantHilbert",    	       	  -- cache table key
    "equivariantHilbertSeries",
    "torusAction",    	      	  -- documented
    "TorusAction",    	      	  -- exported type name
    "weights",	      	      	  -- documented
    "words"    	       	       	  -- documented
    }
--exportMutable {}

-- Unexported/overloaded functions:

-- cyclicFactors    	    	-- unexported
-- dim	      	      	      	-- overloaded, documented
-- generateGroup    	    	-- unexported, internally documented
-- generators	     	     	-- overloaded, documented
-- numgens    	      	      	-- overloaded, documented
-- ring	       	       	        -- overloaded, documented
-- presentation	       	       	-- overloaded
-- hilbertSeries    	    	-- overloaded
-- degreesRing	      	      	-- overloaded

--Protect Option/hashtable symbols
protect Abelian	       -- Strategy option for isInvariant
protect Nonabelian     -- Default strategy option for isInvariant

needsPackage("Polyhedra", Reload => true)
needsPackage("Elimination", Reload => true)


GroupAction = new Type of HashTable
FiniteGroupAction = new Type of GroupAction
TorusAction = new Type of GroupAction
FiniteAbelianAction = new Type of GroupAction
LinearlyReductiveAction = new Type of GroupAction
RingOfInvariants = new Type of HashTable    	  
-- For some reason, InvariantRing already seems to be a protected symbol. 
-- Not due to the InvariantRing package.


-------------------------------------------
--- Add hooks -----------------------------
-------------------------------------------

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

addHook(FiniteGroupAction, symbol schreierGraph, 
    G -> break (generateGroup G)_0  
    )
  
addHook(FiniteGroupAction, symbol group, 
    G -> break keys first schreierGraph G  
    )

addHook(FiniteGroupAction, symbol words, 
    G -> break applyValues((generateGroup G)_1, val -> first val)
    )

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

addHook(LinearlyReductiveAction, symbol hilbertIdeal, V -> break (
    A := groupIdeal V;
    M := actionMatrix V;
    R := ring V;
    if (numColumns M =!= numRows M) or (numRows M =!= #(gens R)) then print "Matrix size does not match polynomial ring";
    -- first, some information about the inputs:
    n := #(gens R);
    K := coefficientRing(R);
    l := #(gens ring M);
    
    -- now make the enlarged polynomial ring we'll work in, and convert inputs to that ring
    x := local x, y := local y, z := local z;
    S := K[x_1..x_n, y_1..y_n, z_1..z_l];
    M' := sub(M, apply(l, i -> (ring M)_i => z_(i+1)));
    A' := sub(A, apply(l, i -> (ring M)_i => z_(i+1)));
    
    -- the actual algorithm follows
    J' := apply(n, i -> y_(i+1) - sum(n, j -> M'_(j,i) * x_(j+1)));
    J := A' + ideal(J');
    I := eliminate(apply(l, i -> z_(i+1)),J);
    II := sub(I, apply(n, i -> y_(i+1) => 0));
    
    -- return the result back in the user's input ring R
    trim(sub(II, join(apply(n, i -> x_(i+1) => R_i),apply(n, i -> y_(i+1) => 0), apply(l, i -> z_(i+1) => 0))))
    ))

--presentation of invariant ring as polynomial ring modulo ideal
addHook(RingOfInvariants, symbol presentation, S -> break (
    	-- get ambient ring and generators of invariant ring
    	R := ambient S;
    	L := generators S;
    	-- get degrees of generators
    	gdegs := L / degree // flatten;
    	-- form a presentation of the invariant ring
    	U := QQ[Variables => #L,--number of variables
-- if next line is uncommented, M2 complains u is unexported
--	    VariableBaseName => symbol u,--symbol
	    Degrees => gdegs];--degrees
    	phi := map(R,U,L);
    	I := ker phi;
    	presentation(U/I)	
	))
  

-------------------------------------------
--- GroupAction methods -------------------
-------------------------------------------

ring GroupAction := Ring => G -> G.ring

dim GroupAction := ZZ => G -> dim ring G


-------------------------------------------
--- FiniteGroupAction methods -------------
-------------------------------------------

-- TO DO: 1. Port and improve the remaining methods from the package "InvariantRing"
--    	     to act on the type FiniteGroupAction (rewritten as hooks as appropriate).
--    	  2. Create examples/documentation/tests for FiniteGroupAction methods.
--    	  3. Write functions to extract list of cyclic factors/weights for FiniteGroupAction
--    	     that happens to be abelian.  
--    	  4. Add OrderBound option to prevent infinite loops if passed an infinite group.


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


-------------------------------------------

generateGroup = method()

generateGroup FiniteGroupAction := { } >> opts -> (cacheValue (symbol generateGroup)) (G -> runHooks(FiniteGroupAction, symbol generateGroup, G) )


-------------------------------------------

schreierGraph = method()

schreierGraph FiniteGroupAction := { } >> opts -> (cacheValue (symbol schreierGraph)) (G -> runHooks(FiniteGroupAction, symbol schreierGraph, G) )
     
   
-------------------------------------------

group = method()

group FiniteGroupAction := { } >> opts -> (cacheValue (symbol group)) (G -> runHooks(FiniteGroupAction, symbol group, G) )


-------------------------------------------

words = method()

words FiniteGroupAction := { } >> opts -> (cacheValue (symbol words)) (G -> runHooks(FiniteGroupAction, symbol words, G) )


-------------------------------------------

relations FiniteGroupAction := { } >> opts -> (cacheValue (symbol relations)) (G -> runHooks(FiniteGroupAction, symbol relations, G) )


-------------------------------------------

reynoldsOperator = method()

reynoldsOperator (RingElement, FiniteGroupAction) := RingElement => (f, G) -> (
    R := ring G;
    if ring f =!= R then (error "reynoldsOperator: Expected an element from the ring on which 
	the group acts.");
    if #(group G)%(char coefficientRing R) == 0 then (error "reynoldsOperator: The Reynolds 
	operator is not defined when the characteristic of the coefficient field divides the 
	order of the group.");
    (1/#(group G))*(sum apply(group G, g -> sub(f, (vars R)*(transpose g) ) ) )
    )


-------------------------------------------

-- Unexported function used to extract the cyclic factors of a FiniteGroupAction that is abelian.
-- Currently, this does not keep track of which generators of the group are the minimal generators 
-- corresponding to the cyclic factors.

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
	 
	

-------------------------------------------
--- TorusAction methods -------------------
-------------------------------------------

torusAction = method()

torusAction (Matrix, PolynomialRing) := TorusAction => (W, R) -> (
    if not isField coefficientRing R then (error "finiteAction: Expected the second argument to be a polynomial ring over a field.");
    if ring W =!= ZZ then (error "torusAction: Expected the first argument to be a matrix of integer weights.");
    if numColumns W =!= dim R then (error "torusAction: Expected the number of columns of the matrix to equal the dimension of the polynomial ring."); 
    r := numRows W;
    -- coefficient ring for torus characters
    z := getSymbol "z";
    C := ZZ[Variables=>r,VariableBaseName=>z,MonomialOrder=>GroupLex=>r,Inverses=>true];
    new TorusAction from {
	cache => new CacheTable,
	(symbol actionMatrix) => W,
	(symbol degreesRing) => C monoid degreesRing R,
	(symbol ring) => R, 
	(symbol rank) => r
	}
    )


-------------------------------------------

net TorusAction := T -> (net T.ring)|" <- "|(net T.actionMatrix)
-- If the weight matrix is huge, consider rewriting to print something else.

rank TorusAction := ZZ => T -> T.rank

weights = method()

weights TorusAction := Matrix => T -> T.actionMatrix 

degreesRing TorusAction := PolynomialRing => T -> T.degreesRing

-------------------------------------------
-- equivariant Hilbert series code
-- for tori and finite abelian groups
-- was written for tori first (hence the letter T)
-- but same code works for finite abelian case

-- this method returns the equivariant hilbert series
-- for a diagonal torus/finite abelian action on a polynomial ring
-- NOTE: group must act diagonally on single graded polynomial ring
-- by default, the series is returned as a rational function
-- if the option Order=>d is used, the expansion of the series
-- up to degree d-1 is returned (as for hilbertSeries)
equivariantHilbertSeries = method(Options => {Order => infinity}, TypicalValue => Divide)
equivariantHilbertSeries (FiniteAbelianAction) :=
equivariantHilbertSeries (TorusAction) := op -> T -> (
    ord := op.Order;
    if ord === infinity then (
	equivariantHilbertRational(T)
	)
    else (
	equivariantHilbertPartial(T,ord-1)
	)
    )

-- toric Hilbert series as a rational function
-- do not export
equivariantHilbertRational = T -> (
    n := dim T;
    W := weights T;
    R := degreesRing T;
    C := coefficientRing R;
    -- tally the weights of the action
    p := pairs tally entries transpose W;
    -- for each weight form the 1-zT factor with the right powr
    -- then multiply them into a product expression
    den := Product apply(sort apply(p, (w,e) -> {1 - C_w * R_0,e}), t -> Power t);
    -- return the rational function as an expression
    Divide{1,den}
)

-- computes expansion of toric Hilbert series up to order d
-- do not export
equivariantHilbertPartial = (T, d) -> (
    -- if not existing, create in the cache
    if not T.cache.?equivariantHilbert then (
	T.cache.equivariantHilbert = 1_(degreesRing T);
	);
    -- how far was it previously computed?
    -- get degree and coefficients
    currentDeg := first degree T.cache.equivariantHilbert;
    (M,C) := coefficients T.cache.equivariantHilbert;
    -- compute higher degrees recursively
    if (d > currentDeg) then (
	R := degreesRing T;
    	den := value denominator equivariantHilbertSeries T;
    	denDeg := first degree den;
	B := last coefficients den;
	for i from currentDeg+1 to d do (
	    M = M | matrix{{R_0^i}};
	    C = C || matrix{{-sum(1..min(i,denDeg),k -> C_(i-k,0)*B_(k,0) )}};
	    );
	);
    -- compute expansion up to desired degree
    p := first flatten entries (M_{0..d}*C^{0..d});
    -- store and return
    T.cache.equivariantHilbert = p
    )



-------------------------------------------
--- FiniteAbelianAction methods -----------
-------------------------------------------

finiteAbelianAction = method()

finiteAbelianAction (List, Matrix, PolynomialRing) := FiniteAbelianAction => (L, W, R) -> (
    if not isField coefficientRing R then (error "finiteAbelianAction: Expected the third argument to be a polynomial ring over a field.");
    if ring W =!= ZZ then (error "finiteAbelianAction: Expected the second argument to be a matrix of integer weights.");
    if numColumns W =!= dim R then (error "finiteAbelianAction: Expected the number of columns of the matrix to equal the dimension of the polynomial ring.");
    r := numRows W;
    if r =!= #L then (error "finiteAbelianAction: Expected the number of rows of the matrix to equal the size of the list."); 
    -- coefficient ring for group characters
    z := getSymbol "z";
    C := ZZ[Variables=>r,VariableBaseName=>z,MonomialOrder=>Lex];
    C = C / ideal apply(gens C,L,(x,i)->x^i-1);
    D := newRing(degreesRing R,MonomialOrder=>RevLex,Inverses=>false);
    new FiniteAbelianAction from {
	cache => new CacheTable,
	(symbol actionMatrix) => W,
	(symbol size) => L,
	(symbol ring) => R,
	(symbol numgens) => #L, 
	(symbol degreesRing) => C monoid D
	}
    )

-------------------------------------------

net FiniteAbelianAction := G -> (
    cyclicGroups := apply(G.numgens, i -> (
	    if i == G.numgens - 1 then (net ZZ|"/"|net G.size#i)
	    else (net ZZ|"/"|net G.size#i|" x ")
	    )
	);
    (net G.ring)|" <- "|(horizontalJoin cyclicGroups)|" via "|net G.actionMatrix
    )
-- If the weight matrix is huge, consider rewriting to print something else.

numgens FiniteAbelianAction := ZZ => G -> G.numgens

size FiniteAbelianAction := List => G -> G.size

weights FiniteAbelianAction := Matrix => G -> G.actionMatrix

degreesRing FiniteAbelianAction := QuotientRing => G -> G.degreesRing

-------------------------------------------
--- LinearlyReductiveAction methods -------
-------------------------------------------

linearlyReductiveAction = method()

linearlyReductiveAction (Ideal, Matrix, PolynomialRing) := LinearlyReductiveAction => (A, M, R) -> (
    if not isField coefficientRing R then (error "linearlyReductiveAction: Expected the third argument to be a polynomial ring over a field.");
    if (numColumns M =!= numRows M) or (numRows M =!= #(gens R)) then (error "linearlyReductiveAction: Matrix size does not match polynomial ring.");
    if coefficientRing ring A =!= coefficientRing R then (error "linearlyReductiveAction: Group and polynomial ring not defined over same field.");
    new LinearlyReductiveAction from {
	cache => new CacheTable,
	(symbol groupIdeal) => A, 
	(symbol actionMatrix) => M, 
	(symbol ring) => R
	}
    )


-------------------------------------------

net LinearlyReductiveAction := V -> (
    (net V.ring)|" <- "|(net ring V.groupIdeal)|"/"|(net V.groupIdeal)|
    " via "|(net V.actionMatrix)
    )

actionMatrix = method()

actionMatrix LinearlyReductiveAction := Matrix => V -> V.actionMatrix

groupIdeal = method()

groupIdeal LinearlyReductiveAction := Ideal => V -> V.groupIdeal


---------------------------------------------

hilbertIdeal = method()

hilbertIdeal LinearlyReductiveAction := { } >> opts -> (cacheValue (symbol hilbertIdeal)) (V -> runHooks(LinearlyReductiveAction, symbol hilbertIdeal, V))


-------------------------------------------
--- Computing invariants ------------------
-------------------------------------------

-- TO DO: 1. Implement invariants(FiniteGroupAction) after porting remaining
--    	     methods from the package "InvariantRing".
--    	  2. After writing code to extract the weights from a finite group action 
--    	     that happens to be abelian, add a Strategy option to invariants(FiniteGroupAction)
--    	     to let user decided whether to use invariants(FiniteAbelianAction).
--    	  3. Add error checking to isInvariant(LinearlyReductiveGroup).


invariants = method()

invariants TorusAction := List => T -> (
    R := ring T;
    r := rank T;
    n := dim R;
    W := weights T;
    local C;
    if r == 1 then C = convexHull W else C = convexHull( 2*r*W|(-2*r*W) );
    C = (latticePoints C)/vector;
    
    -- Creates a hashtable of lists indexed by the lattice points of the convex hull
    -- of the (scaled) weight vectors, initialized with the list of each weight vector
    -- being the corresponding variable in the ring.
    S := new MutableHashTable from apply(C, w -> w => {});
    scan(n, i -> S#(W_i) = {R_i});
    U := new MutableHashTable from S;
    
    local v, local m, local v', local u;
    nonemptyU := select(keys U, w -> #(U#w) > 0);
    --iteration := 0; --step by step printing
    
    -- While some list of monomials in U is nonempty, picks a monomial in U, multiplies
    -- it by every variable, and updates the lists of monomials in S and U if the product
    -- is minimal with respect to divisibility in the list of monomials in S with the same weight.
    while  #nonemptyU > 0 do(
	v = first nonemptyU;
	m = first (U#v);
	
	-- Uncomment lines in step by step printing to see steps
	-- Note: there is one such line before the while loop
	--print("\n"|"Iteration "|toString(iteration)|".\n"); --step by step printing
    	--print(net("    Weights: ")|net(W)); --step by step printing
	--print("\n"|"    Set U of weights/monomials:\n"); --step by step printing
	--print(net("    ")|net(pairs select(hashTable pairs U,l->l!= {}))); --step by step printing
	--print("\n"|"    Set S of weights/monomials:\n"); --step by step printing
	--print(net("    ")|net(pairs select(hashTable pairs S,l->l!= {}))); --step by step printing
	--iteration = iteration + 1; --step by step printing
	
	scan(n, i -> (
        u := m*R_i;
        v' := v + W_i;
        if ((U#?v') and all(S#v', m' -> u%m' =!= 0_R)) then( 
                S#v' = S#v'|{u};
                U#v' = U#v'|{u};
		)
	    )
	);
	U#v = delete(m, U#v);
	nonemptyU = select(keys U, w -> #(U#w) > 0)
	);
    
    -- The generating invariant monomials are the monomials in S of weight 0.
    return S#(0_(ZZ^r))
    )

invariants FiniteAbelianAction := List => G -> (
    W := weights G;
    R := ring G;
    L := size G;
    r := numRows W;
    n := numColumns W;
    temp1 := matrix{apply(flatten entries W^{0},i->i%L#0)};
    scan(r-1,i->temp1 = temp1 || matrix{apply(flatten entries W^{i+1},j->j%L#(i+1))});
    W = temp1;
    t := 1; -- t is the size of abelian group
    --sanity check 
    if #L =!= r then error "abelianInvariants: Expected size of the group to match the weight matrix.";
    scan(L,i->t = t*i);
    local C; -- C is a list of all possible weights
    for i from 0 to #L-1 do(
	if i == 0 then(
	    C = apply(L_i,j-> matrix {{j}});
	) else (
	temp := flatten apply(L_i,j->apply(C,M->M || matrix {{j}}));
	C = temp;
        );
    );
    S := new MutableHashTable from apply(C, w -> w => {});
    scan(n, i -> S#(W_i) = {R_i});
    U := flatten entries vars R;
    local v, local m, local u, local v';
    while  #U > 0 do(
    m = min U; 
    v = vector(apply(n,i->degree(R_i,m))); --degree vector of m
    v = W*v; --weight vector of m
    j := 0;
    scan(n,i->if m % R_i == 0 then (j = i+1;break));
    k := j;
    while k > 0 do(
        u = m*R_(k-1);
        temp := flatten entries (v + W_(k-1));
	temp = apply(#temp,i -> temp_i % L_i);
	v' = matrix(vector temp);
        if all(S#v', m' -> u%m' =!= 0_R) then (
	    S#v' = S#v'|{u};
            if first degree u < t then(
		U = U | {u}; ---only testing monomials of degree < #G
            );
        );
        k = k - 1;
    );
    U = delete(m, U);
    );
    return S#(matrix(0_(ZZ^r)))
    )


-------------------------------------------

--Prune and trim seem to alter existing generators. This just removes redundant ones:
manualTrim = method(TypicalValue => List)

manualTrim (List) := List => L -> (
    if not L#?0 then return L;
    L' := {0_(ring L#0)};
    
    scan(#L, i -> (
	if not (L#i % ideal(L') == 0) then L' = append(L', L#i)
    ));
    return drop(L',1)
)


-------------------------------------------

--Computes an *additive* basis for the degree d part of the invariant ring.
invariants (LinearlyReductiveAction, ZZ) := List => (V,d) -> (
    M := actionMatrix V;
    R := ring V;
    A := groupIdeal V;
    n := dim V;
    K := coefficientRing ring groupIdeal V;
    x := local x, z := local z;
    X := K[x_1..x_n];
    
    l := #(gens ring M);
    S := K[x_1..x_n, z_1..z_l];
    M' := sub(M, apply(l, i -> (ring M)_i => z_(i+1)));
    A' := sub(A, apply(l, i -> (ring M)_i => z_(i+1)));
    
    L := sub(basis(d,X), S);
    r := numColumns L;
    NFDL := apply(r, i -> (sub(L_(0,i), apply(n, j -> x_(j+1) => sum(n, k -> M'_(k,j) * x_(k+1)))) - L_(0,i)) % A');
    monomialsNFDL := flatten entries monomials(matrix{NFDL});
    m := #monomialsNFDL;
    B := matrix(apply(m, i -> apply(r, j -> coefficient(monomialsNFDL#i, NFDL#j))));
    KB := gens kernel B;
    return flatten entries sub(L * KB, join(apply(n, i -> x_(i+1) => R_i), apply(l, i -> z_(i+1) => 0)))
)

--Uses the preceding function together with hilbertIdeal to compute a set of generating invariants.
invariants (LinearlyReductiveAction) := List => V -> (
    I := hilbertIdeal V;
    R := ring V;
    n := dim V;
    K := coefficientRing ring groupIdeal V;
    x := local x;
    X := K[x_1..x_n];
    
    I' := flatten entries gens sub(I, apply(n, i -> (ring I)_i => x_(i+1)));
    
    degreeList := sort toList set apply(I', i -> first degree i);
    generatorList := {};
    
    local d;
    while (#degreeList > 0) do(
	d = degreeList#0;
    	Id := select(I', i -> first degree i == d);
	
	alreadyInv := true;
	j := 0;
	while alreadyInv and Id#?j do(
	    if not isInvariant(Id#j,V) then alreadyInv = false;
	    j = j+1
	);
    	if not alreadyInv then (
	    generatorList = join(generatorList, invariants(V,d))
	) else (
	    generatorList = join(generatorList, apply(Id, f -> sub(f, apply(n, i -> x_(i+1) => R_i))));
	);
    	degreeList = drop(degreeList,1)
    );
    return manualTrim generatorList
)

-------------------------------------------

isInvariant = method()

isInvariant (RingElement, FiniteGroupAction) := Boolean => (f, G) -> reynoldsOperator(f, G) == f
    -- reynoldsOperator already checks to see if f is in the ring on which G acts.

isInvariant (RingElement, TorusAction) := Boolean => (f, T) -> (
    if ring f =!= ring T then (error "isInvariant: Expected an element from the ring on which the group acts.");
    return (weights T) * transpose(matrix(exponents(f))) == 0
    )

isInvariant (RingElement, FiniteAbelianAction) := Boolean => (f, A) -> (
    if ring f =!= ring A then (error "isInvariant: Expected an element from the ring on which the group acts.");
    W := weights A;
    V := W * transpose(matrix(exponents(f)));
    n := dim A;
    d := size A;
    all(numgens A, i -> (V_0_i)%(d#i) == 0)
    )

isInvariant (RingElement, LinearlyReductiveAction) := Boolean => (f, V) -> (
    A := groupIdeal V;
    M := actionMatrix V;
    R := ring(f);
    if (numColumns M =!= numRows M) or (numRows M =!= #(gens R)) then print "Matrix size does not match polynomial ring";
    x := local x, z := local z;
    n := numColumns M;
    K := coefficientRing(ring(f));
    l := #(gens ring M);
    
    S := K[x_1..x_n, z_1..z_l];
    M' := sub(M, apply(l, i -> (ring M)_i => z_(i+1)));
    A' := sub(A, apply(l, i -> (ring M)_i => z_(i+1)));
    f' := sub(f, apply(n, i -> (ring(f))_i => x_(i+1)));
    Gf' := sub(f, apply(n, i -> (ring(f))_i => sum(n, j -> M'_(j,i) * x_(j+1))));
    return ( (Gf' - f') % A' == 0 )
)


-------------------------------------------
--- RingOfInvariants methods --------------
-------------------------------------------

-- TO DO: 1. Add hilbertSeries or molienSeries as functions on RingOfInvariants.
--    	  2. Errors, docs, examples, tests for presentation
--    	  3. Can we pass a symbol as an option for presentation to use as variable base name?

invariantRing = method()

invariantRing GroupAction := RingOfInvariants => G -> (
    -- Generating invariants are stored in the cache in case we want to add Options later
    -- that compute invariants only up to a fixed degree similar to 'res'.
    -- Being in the cache should allow the user to gradually update/increase the degree if there are
    -- many invariants.
    
    new RingOfInvariants from {
	cache => new CacheTable from { (symbol generators) => invariants G },
	(symbol ambient) => ring G, 
	(symbol action) => G
	}
    )

PolynomialRing^GroupAction := RingOfInvariants => (R, G) -> (
    if ring G =!= R then (error "Expected the first argument to be the polynomial ring on which the actions acts.");
    invariantRing G
    )


--presentation of invariant ring as polynomial ring modulo ideal
presentation RingOfInvariants := { } >> opts -> (cacheValue (symbol presentation)) (S -> runHooks(RingOfInvariants, symbol presentation, S) )

--hilbert Series of invariant ring
hilbertSeries RingOfInvariants := Divide => op -> S -> (
    hilbertSeries(coker presentation S,Order=>op.Order,Reduce=>op.Reduce)
    )

-------------------------------------------

net RingOfInvariants := S -> (
    horizontalJoin(
	{
	    (net coefficientRing ambient S),"["
	    }|
	apply(S.cache.generators, v -> (
		if v == last S.cache.generators and v == first S.cache.generators then net v 
		else if v == last S.cache.generators then " "|(net v)
		else (net v)|", " 
		)
	    )|
	{
	    "]"
	    }
	)
    )

action = method()

action RingOfInvariants := GroupAction => S -> S.action

ambient RingOfInvariants := PolynomialRing => S -> S.ambient

generators RingOfInvariants := List => null -> S -> S.cache.generators
-- gens must pass 'opts' before the argument, or it will not run!!



-------------------------------------------
--- Documentation -------------------------
-------------------------------------------


beginDocumentation()

document { 
	Key => InvariantsDev,
	Headline => "Computing Invariants for Tori and Abelian Groups",
	EM "Invariants", " is a package implementing algorithms
	to compute invariants of reductive groups.",
	PARA {
	    "Current algorithms include:"
	    },
	UL { 
	    {"A fast algorithm for invariants of finite abelian groups based on: ",
		"Gandini, F. ",
		HREF{"https://deepblue.lib.umich.edu/handle/2027.42/151589","Ideals of Subspace Arrangements"}, 
	   	". Thesis (Ph.D.)-University of Michigan. 2019. ISBN: 978-1392-76291-2. pp 29-34."
		},
	    {"A fast algorithm for invariants of tori based on: ",
		"Derksen, H. & Kemper, G. (2015). ",
		HREF{"https://link.springer.com/book/10.1007%2F978-3-662-48422-7","Computational Invariant Theory"}, 
	   	". Heidelberg: Springer. pp 174-177"
		}
            }
	}
    
document {
	Key => {action, (action, RingOfInvariants)},
	
	Headline => "the group action that produced a ring of invariants",
	
	Usage => "action S",
	
	Inputs => {
	    	"S" => RingOfInvariants => {"of the group action being returned"},
		},
	
	Outputs => {
		GroupAction => {"the action that produced the ring of invariants in the input"}
		},
	"This function is provided by the package ", TO InvariantsDev,".",
	
	PARA {
	    "This example shows how to recover the action of a
	    torus that produced a certain ring of invariants.
	    Note other action types are possible and may produce
	    a different looking output."
	    },
    	
	EXAMPLE {
		"R = QQ[x_1..x_4]",
		"T = torusAction(matrix {{0,1,-1,1},{1,0,-1,-1}}, R)",
		"S = R^T",
		"action S"
		},
	    }

document {
	Key => {(dim, GroupAction)},
	
	Headline => "dimension of the polynomial ring being acted upon",
	
	Usage => "dim G",
	
	Inputs => {
	    	"G" => GroupAction => {"a group action on a polynomial ring"},
		},
	
	Outputs => {
		ZZ => {"the dimension of the polynomial ring being acted upon"}
		},
	
	PARA {"This function is provided by the package ",
	    TO InvariantsDev,"."},
	
	EXAMPLE {
		"R = QQ[x_1..x_4]",
		"T = torusAction(matrix {{0,1,-1,1},{1,0,-1,-1}}, R)",
		"dim T == dim R"
		},
	    }

document {
	Key => {finiteAbelianAction, (finiteAbelianAction, List, Matrix, PolynomialRing)},
	Headline => "Finite abelian group action via weights",
	Usage => "finiteAbelianAction(d, W, R)",
	Inputs => {
	    	"d" => List => {"of orders of factors in the decomposition of the group"},
	    	"W" => Matrix => {"of weights of the group action"},
		"R" => PolynomialRing => {"on which the group acts"}
		},
	Outputs => {
		FiniteAbelianAction => {"the (diagonal) action of the finite abelian group corresponding to the given weight matrix"}
		},
	"This function is provided by the package ", TO InvariantsDev,". ",

    	PARA {	 
	    "Writing the finite abelian group as",
	    TEX /// $\mathbb{Z}/d_1 \oplus \cdots \oplus \mathbb{Z}/d_r$, ///,
	    "the list ", TT "d = {d_1,d_2,...,d_r},",  " contains the orders of the factors.",
	    " We assume that the group acts diagonally on the polynomial ring",
	    TEX /// $R = k[x_1,\ldots,x_n]$, ///,
	    "which is to say that if we denote the evident generators of the group by",
	    TEX /// $g_1,\ldots,g_r$ ///,
	    "then we have",
	    TEX /// $$g_i \cdot x_j = \zeta_i^{w_{ij}} x_j$$ ///,
	    "for",
	    TEX /// $\zeta_i$ ///,
	    "a primitive",
	    TEX /// $d_i$///,
	    "-th root of unity. The integers",
	    TEX /// $w_{ij}$ ///,
	    "comprise the weight matrix ", TT "W", "."  
	},
    
    	PARA {
	    "Here is an example of a product of two cyclic groups of order 3 acting on a three-dimensional vector space:"
	},
	
	EXAMPLE {
	    "R = QQ[x_1..x_3]",
	    "d = {3,3}",
	    "W = matrix{{1,0,1},{0,1,1}}",
	    "A = finiteAbelianAction(d, W, R)",
		},
    
	    }

document {
	Key => {FiniteAbelianAction},
	
	Headline => "the class of all diagonal actions by
	finite abelian groups",
	
	"This class is provided by the package ", TO InvariantsDev,".",
	
	PARA {
	    	TT "FiniteAbelianAction", " is the class of all
		diagonal actions by finite abelian groups
		on polynomial rings for the
		purpose of computing invariants.
		It is created using ", TO "finiteAbelianAction", "."
	    },
	}

document {
	Key => {finiteAction, 
	    (finiteAction, List, PolynomialRing),
	    (finiteAction, Matrix, PolynomialRing),
	    },
	
	Headline => "the group action generated by a list of matrices",
	
	Usage => "finiteAction(L, R), finiteAction(M, R)",
	Inputs => {
	    	"L" => List => {"of matrices representing the generators of a finite group"},
		"M" => Matrix => {"generating a finite cyclic group of matrices"},
		"R" => PolynomialRing => {"on which the group elements 
		    act by linear changes of coordinates"}
		},
	Outputs => {
		FiniteGroupAction => {"the action of the (finite) matrix group generated by 
		    the input matrices on the given polynomial ring"}
		},
	
	"This function is provided by the package ", TO InvariantsDev,".",
	
	PARA {
	    "The following example defines the permutation action of
	    a symmetric group on three elements."
	    },
	
	EXAMPLE {
	    	"R = QQ[x_1..x_3]",
		"L = apply(2, i -> permutationMatrix(3, [i + 1, i + 2] ) )",
		"S3 = finiteAction(L, R)",
		},
	
	PARA {
	    "On the other hand, the action below corresponds to a cyclic permutation 
	    of the variables."
	    },
	
	EXAMPLE {
		"P = permutationMatrix toString 231",
		"C3 = finiteAction(P, R)",
		},    
	    }

document {
	Key => {FiniteGroupAction},
	
	Headline => "the class of all finite group actions",
	
	"This class is provided by the package ", TO InvariantsDev,".",
	
	PARA {
	    	TT "FiniteGroupAction", " is the class of all finite
		matrix group actions on polynomial rings for the
		purpose of computing invariants.
		It is created using ", TO "finiteAction", ". ",
		"Note that diagonal actions of finite abelian
		groups can be created with the class ",
		TO "FiniteAbelianAction", " which implements more
		efficient methods for computing invariants."
	    },
	}

document {
	Key => {(generators, FiniteGroupAction)},
	Headline => "generators of a finite group",
	Usage => "generators G",
	Inputs => {
	    	"G" => FiniteGroupAction =>
		{"the action of a finite group"},
		},
	Outputs => {
		List => {"a list of generators of the group"}
		},
	"This function is provided by the package ", TO InvariantsDev,". ",

    	PARA {
	    "Use this function to get the user-defined
	    generators of a group action."
	},
    
    	PARA { "The following example defines the permutation action
	    of a symmetric group on three elements using three
	    transpositions."  },
	
	EXAMPLE {
	    "R = QQ[x_1..x_3]",
	    "L = {matrix {{0,1,0},{1,0,0},{0,0,1}}, matrix {{0,0,1},{0,1,0},{1,0,0}}, matrix {{1,0,0},{0,0,1},{0,1,0}} }",
	    "G = finiteAction(L, R)",
	    "generators G"
	    },
	    
	    }

document {
	Key => (generators, RingOfInvariants),
	
	Headline => "the generators for a ring of invariants",
	
	Usage => "generators S, gens S",
	
	Inputs => {
	    	"S" => RingOfInvariants,
		},
	    
	Outputs => {
		List => {"of algebra generators for the ring of invariants"}
		},
	    
	"This function is provided by the package ", TO InvariantsDev,". ",
	
	PARA {
	    "This method gets the algebra generators for a ring of invariants."
	    },
    	
	EXAMPLE {
		"R = QQ[x_1..x_4]",
		"W = matrix{{0,1,-1,1},{1,0,-1,-1}}",
		"T = torusAction(W, R)",
		"S = R^T",
		"gens S",
		},
	    }

document {
	Key => {group, (group, FiniteGroupAction)},
	
	Headline => "list all elements of the group of a finite group action",
	
	Usage => "group G",
	Inputs => {
	    	"G" => FiniteGroupAction
		},
	Outputs => {
		List => {"of all elements in the finite matrix group associated to
		    the given group action"}
		},
	
	"This function is provided by the package ", TO InvariantsDev,".",
	
	PARA {
	    "The following example defines the permutation action of
	    a symmetric group on three elements."
	    },
	
	EXAMPLE {
	    	"R = QQ[x_1..x_3]",
		"L = apply(2, i -> permutationMatrix(3, [i + 1, i + 2] ) )",
		"S3 = finiteAction(L, R)",
		"group S3"
		},
	PARA {
	    "The computation of all elements in the group is actually performed by the method ", 
	    TO schreierGraph, " since the process of computing the Schreier graph of the group
	    yields other useful information about the group besides just its elements."
	    },
	
	SeeAlso => {schreierGraph, relations, words}
	    }

document {
	Key => {GroupAction},
	
	Headline => "the class of all group actions",
	
	"This class is provided by the package ", TO InvariantsDev,".",
	
	PARA {
	    	TT "GroupAction", " is the class of all group actions
		on polynomial rings for the purpose of computing
		invariants. This is not typically used directly,
		delegating creation to the various constructor
		functions for different kinds of group actions:"
	    },
	UL {
	    {TO "FiniteGroupAction", ", the class of 
	    a finite matrix group action, is created with ",
	    TO "finiteAction"},
	    {TO "FiniteAbelianAction", ", the class of the diagonal
	    action of a finite abelian group, is created with ",
	    TO "finiteAbelianAction"},
	    {TO "TorusAction", ", the class of a diagonal
	    torus action, is created with ",
	    TO "torusAction"},
	    {TO "LinearlyReductiveAction", ", the class of a
	    linearly reductive matrix group action,
	    is created with ",
	    TO "linearlyReductiveAction"}
	    },
	
	PARA {
	    "Each class implements different algorithms to
	    compute invariants. Although mathematically speaking
	    all the above group actions are linearly reductive
	    (at least in the non modular case), the class ",
	    TO "LinearlyReductiveAction", " should be used only
	    when none of the other classes apply because it has fewer
	    and possibly less efficient methods."
	    },
	
	PARA {
	    	"The class ", TT "GroupAction ", "is implemented as
		a ", TT "HashTable", ". When created it stores
		information such as the action (in a format
		dependent upon the group) and the polynomial ring
	    	being acted upon."
	    },
	}

document {
	Key => {hilbertIdeal, (hilbertIdeal, LinearlyReductiveAction)},
	
	Headline => "compute (possibly non-invariant) generators for the Hilbert ideal",
	
	Usage => "hilbertIdeal V",
	
	Inputs => {
	        "V" => LinearlyReductiveAction => {"of a polynomial ring ", TT "S", " defining the group as an affine variety"},
		},
	    
	Outputs => {
		Ideal => {"the ideal of ", TT "R", " generated by the invariants (note that the generators of I are likely non-invariant)"}
		},
	    
	"This function is provided by the package ", TO InvariantsDev,
	".",
	
	PARA { 
	    "This function computes the Hilbert ideal generated in a polynomial ring by the 
	    invariants of positive degree of a linearly reductive action.  The algorithm is
	    based on: ",
	    },
       	
	UL { 
	    {"Derksen, H. & Kemper, G. (2015).", EM " Computational Invariant Theory", 
	   ". Heidelberg: Springer. pp 159-164"}
        },
	
	PARA {
	    "The hope is that this function will be used to compute actual generating invariants, 
	    but the crucial step of the Reynolds operator is still missing."
	    },
	
	
	PARA {
	    "The next example constructs a cyclic group of order 2
	    as a set of two affine points. Then it introduces an
	    action of this group on a polynomial ring in two variables
	    and computes the Hilbert ideal. The action permutes the
	    variables of the polynomial ring. Note that the
	    generators of the Hilbert ideal need not be invariant."
	    },
	
	EXAMPLE {
		"S = QQ[z]",
		"A = ideal(z^2 - 1)",
		"M = matrix{{(z+1)/2, (1-z)/2},{(1-z)/2, (z+1)/2}}",
		"sub(M,z=>1),sub(M,z=>-1)",
		"R = QQ[x,y]",
		"V = linearlyReductiveAction(A, M, R)",
		"I = hilbertIdeal V",
		"apply(I_*, f -> isInvariant(f,V))"
		},
	    }

-*
-- Modify this to document linearlyReductiveAction?

document {
	Key => {hilbertIdeal, (hilbertIdeal, LinearlyReductiveAction)},
	
	Headline => "Computes (possibly non-invariant) generators for the Hilbert ideal",
	
	Usage => "hilbertIdeal V",
	
	Inputs => {
	        "V" => LinearlyReductiveAction => {"of a polynomial ring ", TT "S", " defining the group as an affine variety"},
	    	"R" => PolynomialRing => {"on which the group acts"},
		"W" => Matrix => {"whose entries are in ", TT "S", ", that encodes the group action"}
		},
	    
	Outputs => {
		Ideal => {"the ideal of ", TT "R", " generated by the invariants (note that the generators of I are likely non-invariant)"}
		},
	    
	"This function is provided by the package ", TO InvariantsDev,
	". The hope is that this function will be used to compute actual generating invariants, 
	but the crucial step is still missing (the Reynolds operator). For now, it outputs the 
	ideal generated by the invariants in the polynomial ring, as the following example illustrates.",
	
	EXAMPLE {
		"S = QQ[z]",
		"hilbertIdeal(ideal(z^2 - 1), matrix{{(z+1)/2, (1-z)/2},{(1-z)/2, (z+1)/2}}, QQ[x,y])"
		},
	
	UL { 
	    {"Derksen, H. & Kemper, G. (2015).", EM "Computational Invariant Theory", 
	   ". Heidelberg: Springer. pp 159-164"}
        }

}
*-

document {
	Key => {invariantRing, 
	    (invariantRing, GroupAction),
	    (symbol ^, PolynomialRing, GroupAction)},
	
	Headline => "the ring of invariants of a group action",
	
	Usage => "invariantRing G, R^G",
	Inputs => {
	    	"G" => GroupAction,
	    	"R" => PolynomialRing => {"on which the group acts"},
		},
	Outputs => {
		RingOfInvariants => {"the ring of invariants of the given group action"}
		},
	    
	"This function is provided by the package ", TO InvariantsDev,". ",
	
	PARA {
	    "The following example defines an action of a 
	    two-dimensional torus on a four-dimensional vector space
	    with a basis of weight vectors whose weights are
	    the columns of the input matrix."
	},
    	
	EXAMPLE {
		"R = QQ[x_1..x_4]",
		"W = matrix{{0,1,-1,1},{1,0,-1,-1}}",
		"T = torusAction(W, R)",
		"S = invariantRing T",
		},
	    
	PARA {
	    "The algebra generators for the ring of invariants are computed upon
	    initialization by the method ",
	    TO invariants,"."
	    },

	PARA {
	    "Alternatively, we can use the following shortcut to construct
	    a ring of invariants."
	    },
    	
	EXAMPLE {
		"S = R^T",
		},
	    }

document {
	Key => {
	    invariants, 
	    (invariants, TorusAction),
	    (invariants, FiniteAbelianAction)
	    },
	
	Headline => "compute the generating invariants of a group action",
	
	Usage => "invariants T \n invariants A",
	
	Inputs => {  
	    	"T" => TorusAction => {"a diagonal action of a torus on a polynomial ring"},
		"A" => FiniteAbelianAction => {"a diagonal action of a finite abelian group on a polynomial ring"}
		},
	Outputs => {
		"L" => List => {"a minimal set of generating invariants for the group action"}
		},

	PARA {
	    "This function is provided by the package ", TO InvariantsDev, ". It implements algorithms to compute minimal sets 
	    of generating invariants for diagonal actions of tori and finite abelian groups.  The algorithm for tori due to 
	    Derksen and Kemper can be found in:"
	    },
       
       UL { 
	    {"Derksen, H. & Kemper, G. (2015).", EM "Computational Invariant Theory", 
	   ". Heidelberg: Springer. pp 159-164"}
        },
    
       PARA {
	    "The algorithm for tori computes a minimal set of generating monomial invariants for an action of a torus",
	    TEX /// $(k^\times)^r$ ///,
	    " on a polynomial ring ",
	    TEX /// $R = k[x_1,\ldots,x_n]$.///,
	    " We assume that the torus action is diagonal, in the sense that ",
	    TEX /// $(t_1,\ldots,t_r) \in (k^\times)^r$ ///,
	    " acts by",
	    TEX /// $$(t_1,\ldots,t_r) \cdot x_j = t_1^{w_{1j}}\cdots t_r^{w_{rj}} x_j$$ ///,
	    "for some integers ",
	    TEX /// $w_{ij}$. ///,
	    "These are the entries of the input matrix ", TT "W",
	    " for the torus action. In other words, the j-th column of ", TT "W", " is the weight vector of",
	    TEX /// $x_j$. ///
	},
    
    	PARA {
	    "Here is an example of a one-dimensional torus acting on a two-dimensional vector space:"
	},
    
    	EXAMPLE {
	    	"R = QQ[x_1,x_2]",
		"W = matrix{{1,-1}}",
		"T = torusAction(W, R)",
		"invariants T"
		},
	   
	PARA {
	    "The algorithm for finite abelian groups due to Gandini is based on the Derksen-Kemper algorithm for tori,
	     with some adjustments and optimizations for the finite group case.  A description of this algorithm can be found in: "
	     },
	 
        UL { 
	    {"Gandini, F. ", EM "Ideals of Subspace Arrangements", 
	   ". Thesis (Ph.D.)-University of Michigan. 2019. ISBN: 978-1392-76291-2. pp 29-34."}
        },
    
    	PARA {	 
	     "Writing the finite abelian group as",
	    TEX /// $\mathbb{Z}/d_1 \oplus \cdots \oplus \mathbb{Z}/d_r$, ///,
	    "the input ", TT "A", " is a finite abelian action which consists of ", TT "d", " the list ", TT "{d_1,d_2,...,d_r}, ", 
	    TT "W", " a weight matrix, and ",  TT "R"," a polynomial ring. We assume that the group acts diagonally on the polynomial ring",
	    TEX /// $R = k[x_1,\ldots,x_n]$, ///,
	    "which is to say that if we denote the evident generators of the group by",
	    TEX /// $g_1,\ldots,g_r$ ///,
	    "then we have",
	    TEX /// $$g_i \cdot x_j = \zeta_i^{w_{ij}} x_j$$ ///,
	    "for",
	    TEX /// $\zeta_i$ ///,
	    "a primitive",
	    TEX /// $d_i$///,
	    "-th root of unity. The integers",
	    TEX /// $w_{ij}$ ///,
	    "comprise the weight matrix ", TT "W", "."  
	},
    
    	PARA {
	    "Here is an example of a product of two cyclic groups of order 3 acting on a three-dimensional vector space:"
	},
	
	EXAMPLE {
	    "R = QQ[x_1..x_3]",
	    "d = {3,3}",
	    "W = matrix{{1,0,1},{0,1,1}}",
	    "A = finiteAbelianAction(d, W, R)",
	    "invariants A"
		},
    
    	SeeAlso => {invariantRing, torusAction, finiteAbelianAction, isInvariant},	
	}

document {
	Key => {isAbelian, (isAbelian, FiniteGroupAction)},

	Headline => "check whether a finite matrix group is Abelian",
	
	Usage => "isAbelian G",
	
	Inputs => {
	    	"G" => FiniteGroupAction
		},
	    
	Outputs => {
		Boolean => "whether the group associated to the action is Abelian"
		},
	    
	"This function is provided by the package ", TO InvariantsDev,". ",

	PARA {
	    "The following example defines the action of
	    a symmetric group permuting the three variables generating
	    a polynomial ring."
	    },
    	
	EXAMPLE {
	    "R = QQ[x_1..x_4]",
	    "P = apply(3, i -> permutationMatrix(4, [i + 1, i + 2] ) )",
	    "S4 = finiteAction(P, R)",
	    "isAbelian S4",
	    },
	    	    
	PARA {
	    "The following example defines the action of
	    the product of two cyclic groups. One group has order 3
	    and cyclically permutes the three variables generating
	    a polynomial ring. The other group has order 2 and
	    multiplies the variables by -1."
	    },
	
	EXAMPLE {
	    	"R = QQ[x_1..x_3]",
		"L = {matrix {{0,0,1},{0,1,0},{1,0,0}}, matrix {{-1,0,0},{0,-1,0},{0,0,-1}} }",
		"G = finiteAction(L, R)",
		"isAbelian G"
		},
	    }

document {
	Key => {isInvariant, 
	    (isInvariant, RingElement, FiniteGroupAction),
	    (isInvariant, RingElement, TorusAction),
	    (isInvariant, RingElement, FiniteAbelianAction),
	    },
	
	Headline => "check whether a polynomial is invariant under a group action",
	
	Usage => "isInvariant(f, G), isInvariant(f, T), isInvariant(f, A)",
	
	Inputs => {
	    	"f" => RingElement => {"a polynomial in the polynomial ring on which the group acts"},
	    	"G" => FiniteGroupAction,
		"T" => TorusAction,
		"A" => FiniteAbelianAction
		},
	    
	Outputs => {
		Boolean => "whether the given polynomial is invariant under the given group action"
		},
	    
	"This function is provided by the package ", TO InvariantsDev,". ",
    	
	PARA {
	    "This function checks if a polynomial is invariant
	    under a certain group action."
	    },
	
	PARA {
	    "The following example defines the permutation action
	    of a symmetric group on a polynomial ring with three
	    variables."
	    },
	
	EXAMPLE {
	    "R = QQ[x_1..x_3]",
	    "L = apply(2, i -> permutationMatrix(3, [i + 1, i + 2] ) )",
	    "S3 = finiteAction(L, R)",
	    "isInvariant(1 + x_1^2 + x_2^2 + x_3^2, S3)",
	    "isInvariant(x_1*x_2*x_3^2, S3)"
		},
    
    	PARA {
	    "Here is an example with a two-dimensional torus
	    acting on polynomial ring in four variables:"
	    },
	
	EXAMPLE {
	    "R = QQ[x_1..x_4]",
	    "W = matrix{{0,1,-1,1},{1,0,-1,-1}}",
	    "T = torusAction(W, R)",
	    "isInvariant(x_1*x_2*x_3, T)",
	    "isInvariant(x_1*x_2*x_4, T)"
		},
	    
         PARA {
	    "Here is another example of a product of two cyclic groups
	    of order 3 acting on a three-dimensional vector space:"
	    },
	
	EXAMPLE {
	    "R = QQ[x_1..x_3]",
	    "d = {3,3}",
	    "W = matrix{{1,0,1},{0,1,1}}",
	    "A = finiteAbelianAction(d, W, R)",
	    "isInvariant(x_1*x_2*x_3, A)",
	    "isInvariant((x_1*x_2*x_3)^3, A)"
		},
	    }	

document {
	Key => {(numgens, FiniteAbelianAction)},
	Headline => "number of generators of a finite abelian group",
	Usage => "numgens A",
	Inputs => {
	    	"A" => FiniteAbelianAction =>
		{"the action of a finite abelian group"},
		},
	Outputs => {
		ZZ => {"the number of generators of the group"}
		},
	"This function is provided by the package ", TO InvariantsDev,". ",

    	PARA {	 
	    "Writing the finite abelian group as",
	    TEX /// $\mathbb{Z}/d_1 \oplus \cdots \oplus \mathbb{Z}/d_r$, ///,
	    "this function returns ", TT "r", "."
	},
    
    	PARA {
	    "Here is an example of a product of two cyclic groups
	    of order 3 acting on a polynomial ring in 3 variables."
	},
	
	EXAMPLE {
	    "R = QQ[x_1..x_3]",
	    "d = {3,3}",
	    "W = matrix{{1,0,1},{0,1,1}}",
	    "A = finiteAbelianAction(d, W, R)",
	    "numgens A"
		},
	    }

document {
	Key => {(numgens, FiniteGroupAction)},
	Headline => "number of generators of a finite group",
	Usage => "numgens G",
	Inputs => {
	    	"G" => FiniteGroupAction =>
		{"the action of a finite group"},
		},
	Outputs => {
		ZZ => {"the number of generators of the group"}
		},
	"This function is provided by the package ", TO InvariantsDev,". ",

    	PARA {
	    "Use this function to get the number of user-defined
	    generators of a group action."
	},
    
    	PARA { "The following example defines the permutation action
	    of a symmetric group on three elements using three
	    transpositions."  },
	
	EXAMPLE {
	    "R = QQ[x_1..x_3]",
	    "L = {matrix {{0,1,0},{1,0,0},{0,0,1}}, matrix {{0,0,1},{0,1,0},{1,0,0}}, matrix {{1,0,0},{0,0,1},{0,1,0}} }",
	    "G = finiteAction(L, R)",
	    "numgens G"
	    },
	
	Caveat => {"The integer returned by this function is not
	    necessarily the minimal number of generators of the
	    group, rather it is the cardinality of the generating
	    set defined by the user."}
	    
	    }

document {
	Key => {reynoldsOperator, (reynoldsOperator, RingElement, FiniteGroupAction)},
	
	Headline => "the image of a polynomial under the Reynolds operator",
	
	Usage => "reynoldsOperator(f, G)",
	
	Inputs => {
	    	"G" => FiniteGroupAction,
		"f" => RingElement => {"a polynomial in the polynomial ring of the given group action"}
		},
	    
	Outputs => {
		RingElement => {"the invariant polynomial which is the image of the given 
		    polynomial under the Reynolds operator of the given finite group action"}
		},
	    
	"This function is provided by the package ", TO InvariantsDev,". ",
	
	PARA {
	    "The following example computes the image of a polynomial under the
	    Reynolds operator for a cyclic permutation of the variables."
	    },
    	
	EXAMPLE {
	    "R = ZZ/3[x_0..x_6]",
	    "P = permutationMatrix toString 2345671",
	    "C7 = finiteAction(P, R)",
	    "reynoldsOperator(x_0*x_1*x_2^2, C7)",
		},
	    }

document {
	Key => {(ring, GroupAction)},
	
	Headline => "the polynomial ring being acted upon",
	
	Usage => "ring G",
	
	Inputs => {
	    	"G" => GroupAction => {"a group action on a polynomial ring"},
		},
	
	Outputs => {
		Ring => {"the polynomial ring being acted upon"}
		},
	
	PARA {"This function is provided by the package ",
	    TO InvariantsDev,"."},
	
	EXAMPLE {
		"R = QQ[x_1..x_4]",
		"T = torusAction(matrix {{0,1,-1,1},{1,0,-1,-1}}, R)",
		"ring(T) === R"
		},
	    }

document {
	Key => {schreierGraph, (schreierGraph, FiniteGroupAction)},
	
	Headline => "Schreier graph of a finite group",
	
	Usage => "schreierGraph G",
	Inputs => {
	    	"G" => FiniteGroupAction => {"a finite group action"},
		},
	Outputs => {
		HashTable => {"representing the Schreier graph of the group"}
		},
	
	"This function is provided by the package ", TO InvariantsDev,".",
	
	PARA {
	    "For a finite group action, we form a ", TO "HashTable",
	    " whose keys are the generators provided
	    by the user. The value corresponding to a generator ",
	    TT "g", " is a ", TO "HashTable", " containing all pairs ",
	    TT "a => b", " such that ", TT "a*g == b",
	    ". This represents the Schreier graph of the group
	    relative to the generating set provided by the user."
	    },
	
	PARA {
	    "The following example defines the permutation action of
	    a symmetric group on three elements using only two
	    generators, a transposition and a 3-cycle."
	    },
	
	EXAMPLE {
	    	"R = QQ[x_1..x_3]",
		"L = {matrix {{0,1,0},{1,0,0},{0,0,1}}, matrix {{0,0,1},{0,1,0},{1,0,0}} }",
		"G = finiteAction(L, R)",
		"schreierGraph G"
		},
	    }

document {
	Key => {torusAction, (torusAction, Matrix, PolynomialRing)},
	
	Headline => "the torus action from a weight matrix",
	
	Usage => "torusAction(W, R)",
	
	Inputs => {
	    	"W" => Matrix => {"of weights of a torus action"},
		"R" => PolynomialRing => {"on which the torus acts"}
		},
	    
	Outputs => {
		TorusAction => {"the (diagonal) torus action with the given weight matrix"}
		},
	    
	"This function is provided by the package ", TO InvariantsDev,". ",

       	PARA {
	    "Use this function to set up an action of a torus",
	    TEX /// $(k^\times)^r$ ///,
	    " on a polynomial ring ",
	    TEX /// $R = k[x_1,\ldots,x_n]$.///,
	    " We assume that the action is diagonal, meaning that ",
	    TEX /// $(t_1,\ldots,t_r) \in (k^\times)^r$ ///,
	    " acts by",
	    TEX /// $$(t_1,\ldots,t_r) \cdot x_j = t_1^{w_{1j}}\cdots t_r^{w_{rj}} x_j$$ ///,
	    "for some integers ",
	    TEX /// $w_{ij}$. ///,
	    "These are the entries of the input matrix ", TT "W",
	    " for the torus action. In other words, the j-th column of ", TT "W", " is the weight vector of",
	    TEX /// $x_j$. ///
	    },
	
    	PARA {
	"The following example defines an action of a 
	two-dimensional torus on a four-dimensional vector space
	with a basis of weight vectors whose weights are
	the columns of the input matrix."
	},
        	
	EXAMPLE {
	    "R = QQ[x_1..x_4]",
	    "W = matrix{{0,1,-1,1},{1,0,-1,-1}}",
	    "T = torusAction(W, R)"
		},
	    }
	
document {
	Key => {TorusAction},
	
	Headline => "the class of all diagonal torus actions",
	
	"This class is provided by the package ", TO InvariantsDev,".",
	
	PARA {
	    	TT "TorusAction", " is the class of all
		diagonal torus actions on polynomial rings for the
		purpose of computing invariants.
		It is created using ", TO "torusAction", "."
	    },
	}

document {
	Key => {weights},
	Headline => "of a diagonal action",
	Usage => "weights A\n
	weights T",
	Inputs => {
	    	"A" => FiniteAbelianAction =>
		{"the diagonal action of a finite abelian group"},
	    	"T" => TorusAction =>
		{"a diagonal torus action"},
		},
	Outputs => {
		Matrix => {"the weight matrix of the group action"}
		},
	"This function is provided by the package ", TO InvariantsDev,". ",

}

document {
	Key => {(weights, FiniteAbelianAction)},
	Headline => "for the diagonal action of a finite abelian group",
	Usage => "weights A",
	Inputs => {
	    	"A" => FiniteAbelianAction =>
		{"the action of a finite abelian group"},
		},
	Outputs => {
		Matrix => {"the weight matrix of the group action"}
		},
	"This function is provided by the package ", TO InvariantsDev,". ",

    	PARA {	 
	    "Writing the finite abelian group as",
	    TEX /// $\mathbb{Z}/d_1 \oplus \cdots \oplus \mathbb{Z}/d_r$, ///,
	    "the list ", TT "d = {d_1,d_2,...,d_r},",  " contains the orders of the factors.",
	    " We assume that the group acts diagonally on the polynomial ring",
	    TEX /// $R = k[x_1,\ldots,x_n]$, ///,
	    "which is to say that if we denote the evident generators of the group by",
	    TEX /// $g_1,\ldots,g_r$ ///,
	    "then we have",
	    TEX /// $$g_i \cdot x_j = \zeta_i^{w_{ij}} x_j$$ ///,
	    "for",
	    TEX /// $\zeta_i$ ///,
	    "a primitive",
	    TEX /// $d_i$///,
	    "-th root of unity. This function returns the weight
	    matrix",
	    TEX /// $(w_{ij})$ ///, "."  
	},
    
    	PARA {
	    "Here is an example of a product of two cyclic groups
	    of order 3 acting on a polynomial ring in 3 variables."
	},
	
	EXAMPLE {
	    "R = QQ[x_1..x_3]",
	    "d = {3,3}",
	    "W = matrix{{1,0,1},{0,1,1}}",
	    "A = finiteAbelianAction(d, W, R)",
	    "weights A"
		},
	    }

document {
	Key => {(weights, TorusAction)},
	Headline => "of a diagonal torus action",
	Usage => "weights T",
	Inputs => {
	    	"T" => TorusAction => {"a torus action"},
		},
	Outputs => {
		Matrix => {"the weight matrix of the torus action"}
		},
	"This function is provided by the package ", TO InvariantsDev,". ",
    	PARA {
	    "Use this function to recover the weight matrix of a
	    diagonal torus action on a polynomial ring.
	    The variables of the ring are weight vectors with
	    weights corresponding in order to the columns of the
	    weight matrix."
	    },
	
    	PARA {
	"The following example defines an action of a 
	two-dimensional torus on a polynomial ring in four
	variables."
	},
        	
	EXAMPLE {
	    "R = QQ[x_1..x_4]",
	    "W = matrix{{0,1,-1,1},{1,0,-1,-1}}",
	    "T = torusAction(W, R)",
	    "weights T"
		},
	    }

document {
	Key => {words, (words, FiniteGroupAction)},
	
	Headline => "associate a word in the generators of a group to each element",
	
	Usage => "words G",
	Inputs => {
	    	"G" => FiniteGroupAction
		},
	Outputs => {
		HashTable => {"associating to each element in the group of the action
		    a word of minimal length in (the indices of) the generators of the group"}
		},
	
	"This function is provided by the package ", TO InvariantsDev,".",
	
	PARA {
	    "The following example computes, for each permutation in the symmetric group
	    on three elements, a word of minimal length in the Coxeter generators."
	    },
	
	EXAMPLE {
	    	"R = QQ[x_1..x_3]",
		"L = apply(2, i -> permutationMatrix(3, [i + 1, i + 2] ) )",
		"S3 = finiteAction(L, R)",
		"words S3"
		},
	PARA {
	    "The computation of the words addressing each element in the group is actually 
	    performed by the method ", TO schreierGraph, " since the process of computing 
	    the Schreier graph of the group yields other useful information about the group."
	    },
	
	SeeAlso => {group, schreierGraph, relations}
	    }


-------------------------------------------
--- TESTS ---------------------------------
-------------------------------------------

-- to do: Add TEST for every method in the package, ideally two tests for each

TEST ///
R1 = QQ[x_1..x_4]
T1 = torusAction(matrix {{-3, -1, 1, 2}}, R1)
invariants1 =  set {x_2*x_3, x_2^2*x_4, x_1*x_3*x_4, x_1*x_2*x_4^2, x_1^2*x_4^3, x_1*x_3^3}
assert(set invariants T1 === invariants1)
///

TEST ///
R2 = QQ[x_1..x_4]
T2 = torusAction(matrix{{0,1,-1,1},{1,0,-1,-1}}, R2)
invariants2 = set {x_1*x_2*x_3,x_1^2*x_3*x_4}
assert(set invariants T2 === invariants2)
///
     
-- to do: write this part to work with Invariants as InvariantsOld
--     	   and InvariantsDev becomes Invariants     
       
end







-- Here place M2 code that you find useful while developing this
-- package.  None of it will be executed when the file is loaded,
-- because loading stops when the symbol "end" is encountered.

restart
uninstallPackage "Invariants"
installPackage "Invariants"
--installPackage("Invariants", RemakeAllDocumentation=>true)
check Invariants

-- Local Variables:
-- compile-command: "make -C $M2BUILDDIR/Macaulay2/packages PACKAGES=Invariants pre-install"
-- End:

restart
uninstallPackage "InvariantsDev"
installPackage "InvariantsDev"
--installPackage("Invariants", RemakeAllDocumentation=>true)
check InvariantsDev

S = QQ[a,b,c,d]
idealSL2 = ideal(a*d - b*c - 1)
SL2std = matrix{{a,b},{c,d}}
R1 = QQ[x_1..x_2]
time V1 = linearlyReductiveAction(idealSL2,SL2std,R1)
time hilbertIdeal V1

needsPackage "SchurFunctors"
n = 3 -- 4 takes a second or so, 5 takes a long time (I didn't wait around for it to finish)
Rn = QQ[x_0..x_n]
Vn = linearlyReductiveAction(idealSL2, schur({n}, SL2std), Rn)
time hilbertIdeal Vn
invariants(Vn,6)
isInvariant(x_0,Vn)

needsPackage "InvariantsDev"
R1 = QQ[a_1..a_3]
W = matrix{{1,0,1},{0,1,1}}
L = {3,3}
T = finiteAction(W,R1,L)
R1^T
invariantRing T

S = QQ[z]
A = ideal(z^2 - 1)
M = matrix{{(1+z)/2, (1-z)/2},{(1-z)/2,(1+z)/2}}
R = QQ[a,b]
X = linearlyReductiveAction(A,M,R)
isInvariant(a,X)
