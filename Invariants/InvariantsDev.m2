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

-- TO DO: 1. Eliminate any unused exported symbols (linearInvariants?) below.
--    	  2. Eliminate any unused protected symbols below.
--    	  3. Determine whether there are functions that do not need to be exported.


-- Any symbols or functions that the user is to have access to
-- must be placed in one of the following two lists
export {
    "abelianInvariants",
    "action",
    "actionMatrix",
    "finiteAction",
    "group",
    "hilbertIdeal",
    "invariants",
    "invariantRing",
    "isAbelian",
    "isInvariant",
    "linearInvariants",
    "linearlyReductiveAction",
    "reynoldsOperator",
    "schreierGraph",
    "torusAction",
    "weights",
    "words"
    }
--exportMutable {}

--Protect Option/hashtable symbols
protect Action
protect Abelian	       -- Strategy option for isInvariant
protect Nonabelian     -- Default strategy option for isInvariant
protect RepDimension
protect GroupIdeal

needsPackage("Polyhedra", Reload => true)
needsPackage("Elimination", Reload => true)


GroupAction = new Type of HashTable
FiniteGroupAction = new Type of GroupAction
FiniteAbelianAction = new Type of FiniteGroupAction
TorusAction = new Type of GroupAction
LinearlyReductiveAction = new Type of GroupAction
RingOfInvariants = new Type of HashTable    	  
-- For some reason, InvariantRing already seems to be a protected symbol. 
-- Maybe because of the InvariantRing package?


-------------------------------------------
--- Add hooks -----------------------------
-------------------------------------------

addHook(FiniteGroupAction, symbol isAbelian, G -> break (
	X := G.generators;
    	n := #X;
    	if n == 1 then(
	    return true 
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

addHook(FiniteGroupAction, symbol size, G -> break (
    if not isAbelian G then (error "size: Expected group to be abelian.");
    relators := relations G;
    m := numgens G;
    relators = transpose matrix apply(relators, L -> (
	    counts := apply(L, l -> applyValues(partition(i -> i, l), val -> #val) );
	    counts = apply(counts, l -> apply(m, i -> if l#?i then l#i else 0) );
	    first counts - last counts
	    )
	);
    relators = relations minimalPresentation coker relators;
    apply(m, i -> relators_i_i)
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
--    	  3. Write functions to extract list of cyclic factor/weights for FiniteGroupAction
--    	     presented as a list of matrices.  Add hook functions to   
--    	  4. Modify generateGroup, group, schreierGraph, words to work when a finite abelian
--    	     group is initialized using a list of cyclic factors and a weight matrix.


finiteAction = method()

finiteAction (List, PolynomialRing) := FiniteGroupAction => (G, R) -> (
    if not isField coefficientRing R then (error "finiteAction: Expected the second argument to be a polynomial ring over a field.");
    if not all(G, g -> instance(g, Matrix)) then (error "finiteAction: Expected the first argument to be a list of matrices.");
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

finiteAction (Matrix, PolynomialRing, List) := FiniteGroupAction => (W, R, L) -> (
    if not isField coefficientRing R then (error "abelianGroupAction: Expected the second argument to be a polynomial ring over a field.");
    if ring W =!= ZZ then (error "abelianGroupAction: Expected the first argument to be a matrix of integer weights.");
    if numColumns W =!= dim R then (error "abelianGroupAction: Expected the number of columns of the matrix to equal the dimension of the polynomial ring.");
    if numRows W =!= #L then (error "abelianGroupAction: Expected the number of rows of the matrix to equal the size of the list."); 
    new FiniteGroupAction from {
	cache => new CacheTable from {
	    (symbol isAbelian) => true,
	    (symbol actionMatrix) => W,
	    (symbol rank) => numRows W,
	    (symbol size) => L,
	    (symbol relations) => diagonalMatrix L,
	    (symbol group) => coker diagonalMatrix L,
	    },
	(symbol ring) => R,
	(symbol generators) => gens ZZ^(numRows W),
	(symbol numgens) => numRows W, 
	}
    )

-------------------------------------------

net FiniteGroupAction := G -> (net G.ring)|" <- "|(net G.generators)
-- If the list of generators is long, consider rewriting  to print only the first few generators together with "...".
-- Or find a better way to print if the size of the matrices is large.

rank FiniteGroupAction := ZZ => G -> (
    if isAbelian G then G.cache.rank
    else (error "rank: Expected group to be abelian.")
    )

size FiniteGroupAction := { } >> opts -> (cacheValue (symbol size)) (G -> runHooks(FiniteGroupAction, symbol size, G) )

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
    if ring f =!= R then (error "reynoldsOperator: Expected an element from the ring on which the group acts.");
    (1/#(group G))*(sum apply(group G, g -> sub(f, (vars R)*(transpose g) ) ) )
    )


-------------------------------------------
--- TorusAction methods -------------------
-------------------------------------------

torusAction = method()

torusAction (Matrix, PolynomialRing) := TorusAction => (W, R) -> (
    if not isField coefficientRing R then (error "finiteAction: Expected the second argument to be a polynomial ring over a field.");
    if ring W =!= ZZ then (error "torusAction: Expected the first argument to be a matrix of integer weights.");
    if numColumns W =!= dim R then (error "torusAction: Expected the number of columns of the matrix to equal the dimension of the polynomial ring."); 
    new TorusAction from {
	cache => new CacheTable,
	(symbol actionMatrix) => W,
	(symbol ring) => R, 
	(symbol rank) => numRows W
	}
    )


-------------------------------------------

net TorusAction := T -> (net T.ring)|" <- "|(net T.actionMatrix)
-- If the weight matrix is huge, consider rewriting to print something else.

rank TorusAction := ZZ => T -> T.rank

weights = method()

weights TorusAction := Matrix => T -> T.actionMatrix 

weights FiniteGroupAction := Matrix => G -> (
    if isAbelian G then G.cache.actionMatrix
    else (error "weights: Expected group to be abelian.")
    )


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

net LinearlyReductiveAction := V -> net V.ring|"<--"|net (ring V.groupIdeal)|"/"|net V.groupIdeal|" via "|net V.actionMatrix

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

-- TO DO: 1. Finish creating invariants(FiniteGroupAction) after porting remaining
--    	     methods from the package "InvariantRing".
--    	  2. After writing code to extract the weights from a finite group action 
--    	     that happens to be abelian, add a Strategy option to invariants(FiniteGroupAction)
--    	     to let user decided whether to use abelianInvariants.



abelianInvariants = method()

abelianInvariants FiniteGroupAction := List => T -> (
    W := weights T;
    R := ring T;
    L := size T;
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

invariants = method()

invariants FiniteGroupAction := List => G -> (
    if isAbelian G then abelianInvariants G
    else (error "invariants: Invariants of a non-abelian finite group action not yet implemented.")
    )

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


isInvariant = method(TypicalValue => Boolean, Options => {Strategy => Nonabelian})

isInvariant (RingElement, FiniteGroupAction) := Boolean => opts -> (f, G) -> (
    if opts.Strategy == "Abelian" then (
	W := weights G;
	V := W * transpose(matrix(exponents(f)));
	n := dim G;
	L := size G;
	all(n, i -> (V#i)%(L#i) == 0)
	)
    else (
    -- reynoldsOperator already checks to see if f is in the ring on which G acts.
    reynoldsOperator(f, G) == f
    )
) 

isInvariant (RingElement, TorusAction) := Boolean => (f, T) -> (
    if ring f =!= ring T then (error "isInvariant: Expected an element from the ring on which the group acts.");
    return (weights T) * transpose(matrix(exponents(f))) == 0
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

generators RingOfInvariants := List => opts -> S -> S.cache.generators
-- gens must pass 'opts' before the argument, or it will not run!!



-------------------------------------------
--- Documentation -------------------------
-------------------------------------------


beginDocumentation()
-*
document { 
	Key => Invariants,
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
	Key => {torusInvariants, (torusInvariants,Matrix,PolynomialRing)},
	Headline => "Computes the primary invariants for a diagonal torus action given by column weight vectors",
	Usage => "torusInvariants(W,R)",
	Inputs => {  
	    	"R" => PolynomialRing => {"on which the torus acts diagonally"},
		"W" => Matrix => {"whose ith column is the weight vector of ", TT "R_i"}
		},
	Outputs => {
		List => {"A minimal set of generating invariants for the torus action"}
		},
	SeeAlso => {abelianInvariants},
	PARA {
	    "This function is provided by the package ", TO Invariants, ". It implements an algorithm by Derksen and Kemper for computing a minimal set of generating invariants for an action of a torus",
	    TEX /// $(k^\times)^r$ ///,
	    " on a polynomial ring ",
	    TEX /// $R = k[x_1,\ldots,x_n]$.///,
	    " We assume that the torus action is diagonal, in the sense that ",
	    TEX /// $(t_1,\ldots,t_r) \in (k^\times)^r$ ///,
	    " acts by",
	    TEX /// $$(t_1,\ldots,t_r) \cdot x_j = t_1^{w_{1j}}\cdots t_r^{w_{rj}} x_j$$ ///,
	    "for some integers ",
	    TEX /// $w_{ij}$. ///,
	    "These are the entries of the input matrix ", TT "W", ". In other words, the j-th column of ", TT "W", " is the weight vector of",
	    TEX /// $x_j$. ///
	},
    	PARA {
	    "Here is an example of a one-dimensional torus acting on a two-dimensional vector space:"
	},
    	EXAMPLE {
		"torusInvariants(matrix{{1,-1}}, QQ[x_1,x_2])"
		},
      
	UL { 
	    {"Derksen, H. & Kemper, G. (2015). ", EM "Computational Invariant Theory", 
	   ". Heidelberg: Springer. pp 174-177"}
        }	
}

document {
	Key => {abelianInvariants, (abelianInvariants,FiniteGroupAction)},
	Headline => "Computes the generators of ring of invariants for an abelian group action given by column weight vectors",
	Usage => "abelianInvariants(T)",
	Inputs => {
	        "T" => FiniteGroupAction => {"which encodes the action of a finite abelian group on a polynomial ring"}
		},
	Outputs => {
		List => {"A minimal set of generating invariants for the abelian group action"}
		},
	SeeAlso => {invariants},
	PARA {
	    "This function is provided by the package ", TO Invariants, ". It is based on the same algorithm as ", TO invariants,
	    " with some adjustments and optimizations for the finite group case; see the reference below for details. Writing the finite abelian group as",
	    TEX /// $\mathbb{Z}/d_1 \oplus \cdots \oplus \mathbb{Z}/d_r$, ///,
	    "the input ", TT "T", " is a finiteGroupAction which consists of " TT "L", " the list ", TT "{d_1,d_2,...,d_r}", ",", TT "R"," a polynomial ring and ",TT "W", " a weight matrix. We assume that the group acts diagonally on the polynomial ring",
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
        UL { 
	    {"Gandini, F. ", EM "Ideals of Subspace Arrangements", 
	   ". Thesis (Ph.D.)-University of Michigan. 2019. ISBN: 978-1392-76291-2. pp 29-34."}
        },
    	PARA {
	    "Here is an example of a product of two cyclic groups of order 3 acting on a three-dimensional vector space:"
	},
	
	EXAMPLE {
	    "R = QQ[x_1..x_3]",
	    "W = matrix{{1,0,1},{0,1,1}}",
	    "L = {3,3}",
	    "T = finiteAction(W,R,L)",
	    "abelianInvariants(T)"
		}
	}

document {
	Key => {hilbertIdeal, (hilbertIdeal,Ideal,Matrix,PolynomialRing)},
	Headline => "Computes generators (possibly non-invariant) for the invariant ideal",
	Usage => "hilbertIdeal(A,M,R)",
	Inputs => {
	        "A" => Ideal => {"of some polynomial ring ", TT "S", " defining the group as an affine variety"},
	    	"R" => PolynomialRing => {"on which the group acts"},
		"W" => Matrix => {"whose entries are in ", TT "S", ", that encodes the group action"}
		},
	Outputs => {
		Ideal => {"the ideal of ", TT "R", " generated by the invariants (note that the generators of I are likely non-invariant)"}
		},
	"This function is provided by the package ", TO Invariants,
	". The hope is that this function will used to compute actual generating invariants, but the crucial step is still missing (the Reynolds operator). For now, it outputs the ideal generated by the invariants in the polynomial ring, as the following example illustrates.",
	
	EXAMPLE {
		"S = QQ[z]",
		"hilbertIdeal(ideal(z^2 - 1), matrix{{(z+1)/2, (1-z)/2},{(1-z)/2, (z+1)/2}}, QQ[x,y])"
		},
	
	UL { 
	    {"Derksen, H. & Kemper, G. (2015).", EM "Computational Invariant Theory", 
	   ". Heidelberg: Springer. pp 159-164"}
        }

document {
	Key => {action, (action,RingOfInvariants)},
	Headline => "Group action that produced a certain ring of invariants",
	Usage => "action(R)",
	Inputs => {
	    	"R" => RingOfInvariants => {"of the group action being returned"},
		},
	Outputs => {
		GroupAction => {"the action that produced the ring of invariants in the input"}
		},
	"This function is provided by the package ", TO Invariants,".",
	PARA {
	    "This example shows how to recover the action of a
	    torus that produced a certain ring of invariants.
	    Note other action types are possible and may produce
	    a different looking output."
	    },
    	
	EXAMPLE {
		"R=QQ[x_1..x_4]",
		"T=torusAction matrix{{0,1,-1,1},{1,0,-1,-1}}",
		"S=R^T",
		"action S"
		},
}

document {
	Key => {finiteAction, (finiteAction,List)},
	Headline => "Group action generated by a list of matrices",
	Usage => "finiteAction(L)",
	Inputs => {
	    	"L" => List => {"of matrices representing elements of a finite group"},
		},
	Outputs => {
		GroupAction => {"the action of the (finite) matrix group generated by the input list"}
		},
	"This function is provided by the package ", TO Invariants,".",
	PARA {
	    "The following example defines the permutation action of
	    a symmetric group on three elements."
	    },
	
	EXAMPLE {
		"L={matrix{{0,1,0},{1,0,0},{0,0,1}},matrix{{0,0,1},{0,1,0},{1,0,0}}}",
		"finiteAction L"
		},
}

document {
	Key => {torusAction, (torusAction,Matrix)},
	Headline => "Torus action from a weight matrix",
	Usage => "torusAction(M)",
	Inputs => {
	    	"M" => Matrix => {"of weights of a torus action"},
		},
	Outputs => {
		GroupAction => {"the (diagonal) torus action with given weight matrix"}
		},
	"This function is provided by the package ", TO Invariants,". ",
	    PARA {
	"The following example defines an action of a 
	two-dimensional torus on a four-dimensional vector space
	with a basis of weight vectors whose weights are
	the columns of the input matrix."
	},
    	
	EXAMPLE {
		"T = torusAction matrix{{0,1,-1,1},{1,0,-1,-1}}"
		},
}

document {
	Key => {invariantRing, (invariantRing,GroupAction,PolynomialRing)},
	Headline => "The ring of invariants of a group action",
	Usage => "invariantRing(G,R)\nR^G",
	Inputs => {
	    	"G" => GroupAction => {""},
	    	"R" => PolynomialRing => {""},
		},
	Outputs => {
		RingOfInvariants => {"of the given group action"}
		},
	"This function is provided by the package ", TO Invariants,". ",
	PARA {
	"The following example defines an action of a 
	two-dimensional torus on a four-dimensional vector space
	with a basis of weight vectors whose weights are
	the columns of the input matrix."
	},
    	
	EXAMPLE {
		"R=QQ[x_1..x_4]",
		"T=torusAction matrix{{0,1,-1,1},{1,0,-1,-1}}",
		"S=invariantRing(T,R)",
		},
	PARA {
	"Note that this function sets up the ring of invariants
	but does not perform any computations. To obtain
	generators for the ring of invariants use ",
	TO invariants,". Here is a shortcut for this method."
	},
    	
	EXAMPLE {
		"S=R^T",
		},
}

document {
	Key => {invariants, (invariants,RingOfInvariants)},
	Headline => "Compute generators for a ring of invariants",
	Usage => "invariants(S)",
	Inputs => {
	    	"S" => RingOfInvariants => {""},
		},
	Outputs => {
		List => {"of generators for the ring of invariants"}
		},
	"This function is provided by the package ", TO Invariants,". ",
	PARA {
	    "This method computes generators for a ring of
	    invariants as an algebra over the field of coefficients
	    of the ambient polynomial ring.
	    The algorithm used depends on the group action."
	    },
	PARA {
	"The following example computes generators for the ring of
	invariants of a finite group action."
	},
    	
	EXAMPLE {
		"null",
		},
	PARA {
	"The next example computes generators for the ring of
	invariants of a torus action."
	},
    	
	EXAMPLE {
		"R=QQ[x_1..x_4]",
		"T=torusAction matrix{{0,1,-1,1},{1,0,-1,-1}}",
		"S=invariantRing(T,R)",
		"invariants(S)",
		},
	    }

*-

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
       
end

-- to do: write this part to work with Invariants as InvariantsOld
--     	   and InvariantsDev becomes Invariants

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
