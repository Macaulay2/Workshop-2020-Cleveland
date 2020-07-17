--This file contains methods to compute invariants (weight algorithms) and check invariants
--TODO 6/26/20 
--1. Update and check list below: take Molien series code from old InvariantRing 
--2. Check state of documentation
--3. Check state of tests

--NOTE
-- For some reason, InvariantRing already seems to be a protected symbol. 
-- Not due to the InvariantRing package.

-------------------------------------------
--- RingOfInvariants methods --------------
-------------------------------------------

-- TO DO: 1. Add hilbertSeries or molienSeries as functions on RingOfInvariants.
--    	  2. Errors, docs, examples, tests for presentation
--    	  3. (?) Can we pass a symbol as an option for presentation to use as variable base name?


RingOfInvariants = new Type of HashTable   

invariantRing = method(Options => {Strategy => UseNormaliz})

invariantRing GroupAction := RingOfInvariants => o -> G -> (
    -- Generating invariants are stored in the cache in case we want to add Options later
    -- that compute invariants only up to a fixed degree similar to 'res'.
    -- Being in the cache should allow the user to gradually update/increase the degree if there are
    -- many invariants.
    
    new RingOfInvariants from {
	cache => new CacheTable from { (symbol generators) => invariants(G, o) },
	(symbol ambient) => ring G, 
	(symbol action) => G
	}
    )

PolynomialRing^GroupAction := RingOfInvariants => (R, G) -> (
    if ring G =!= R then (error "Expected the first argument to be the polynomial ring on which the actions acts.");
    invariantRing G
    )

QuotientRing^LinearlyReductiveAction := RingOfInvariants => (Q, L) -> (
    if ring L =!= Q then (error "Expected the first argument to be the ring on which the actions acts.");
    invariantRing L
    )

-------------------------------------------

net RingOfInvariants := S -> (
    n := horizontalJoin(
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
	);
    -- this is used for linearly reductive actions on quotients
    -- to print relations on the ring of invariants
    if not zero ideal ambient S then (
	n = horizontalJoin(n," / ",net ideal ambient S);
	);
    return n;
    )

action = method()

action RingOfInvariants := GroupAction => S -> S.action

ambient RingOfInvariants := PolynomialRing => S -> S.ambient

generators RingOfInvariants := List => null -> S -> S.cache.generators
-- gens must pass 'opts' before the argument, or it will not run!!


-------------------------------------------

--presentation of invariant ring as polynomial ring modulo ideal

definingIdeal = method(Options => {Variable => "u"})

definingIdeal RingOfInvariants := opts -> S -> (
    u := getSymbol opts.Variable;
    local J;
    if S.cache#?definingIdeal then (
	J = S.cache#definingIdeal;
	if first baseName first (ring J)_* == u then return J
	);
    -- get ambient ring and generators of invariant ring
    R := ambient S;
    K := coefficientRing R;
    L := generators S;
    n := #L;
    -- get degrees of generators
    gdegs := L / degree // flatten;
    -- form a presentation of the invariant ring
    U := K[u_1..u_n, Degrees => gdegs];
    J = ker map(R,U,L);
    S.cache#(symbol definingIdeal) = J;
    return J
    )


-------------------------------------------

hilbertSeries RingOfInvariants := Divide => opts -> S -> (
    hilbertSeries(definingIdeal S, Order => opts.Order, Reduce => opts.Reduce)
    )


-------------------------------------------
--- Computing invariants ------------------
-------------------------------------------

-- TO DO: 2. After writing code to extract the weights from a finite group action 
--    	     that happens to be abelian, add a Strategy option to invariants(FiniteGroupAction)
--    	     to let user decided whether to use invariants(FiniteAbelianAction).
--    	  3. Add error checking to isInvariant(LinearlyReductiveGroup).

reynoldsOperator = method()

reynoldsOperator (RingElement, FiniteGroupAction) := RingElement => (f, G) -> (
    R := ring G;
    if not instance(f, R) then (error "reynoldsOperator: Expected an element from the ring on which 
	the group acts.");
    if #(group G)%(char coefficientRing R) == 0 then (error "reynoldsOperator: The Reynolds 
	operator is not defined when the characteristic of the coefficient field divides the 
	order of the group.");
    (1/#(group G))*(sum apply(group G, g -> sub(f, (vars R)*(transpose g) ) ) )
    )

reynoldsOperator (RingElement, DiagonalAction) := RingElement => (f, D) -> sum select(terms f, m -> isInvariant(m, D) )

-------------------------------------------

invariants = method(Options => {
	Strategy => UseNormaliz,
	Reynolds => true,
	DegreeBound => infinity
	})

invariants DiagonalAction := List => o -> D -> (
    (W1, W2) := weights D;
    R := ring D;
    R = (coefficientRing R)[R_*, MonomialOrder => GLex];
    d := cyclicFactors D;
    r := rank D;
    g := numgens D;
    n := dim D;
    mons := R_*;
    local C, local S, local U;
    local v, local m, local v', local u;
    
    -- Find invariants of the finite abelian factors. 
    if g > 0 then (
	t := product d;
	
	reduceWeight := w -> vector apply(g, i -> w_i%d#i);
	
	C = apply(n, i -> reduceWeight W2_i);
	
	S = new MutableHashTable from apply(C, w -> w => {});
	scan(#mons, i -> S#(reduceWeight W2_i) = S#(reduceWeight W2_i)|{mons#i});
	U = R_*;
	
	while  #U > 0 do(
	    m = min U; 
	    v = first exponents m;
	    k := max positions(v, i -> i > 0);
	    v = reduceWeight(W2*(vector v));
	    
	    while k < n do(
	    	u = m*R_k;
	    	v' = reduceWeight(v + W2_k);
	    	if (not S#?v') then S#v' = {};
	    	if all(S#v', m' -> u%m' =!= 0_R) then (
		    S#v' = S#v'|{u};
		    if first degree u < t then U = U | {u}
		    );
	    	k = k + 1;
	    	);
	    U = delete(m, U);
	    );
    	if S#?(0_(ZZ^g)) then mons = S#(0_(ZZ^g)) else mons = {}
    	);
    if r == 0 then return apply(mons, m -> sub(m, ring D) );
    
    -- Find invariants of the torus factors among the abelian invariant monomials.
    W1 = W1*(transpose matrix (mons/exponents/first));
    if o.Strategy == UsePolyhedra then (
	if r == 1 then C = convexHull W1 else C = convexHull( 2*r*W1|(-2*r*W1) );
	C = (latticePoints C)/vector;
	)
    else if o.Strategy == UseNormaliz then (
	if r == 1 then C = (normaliz(transpose W1, "polytope"))#"gen" 
	else C = (normaliz(transpose (2*r*W1|(-2*r*W1)), "polytope"))#"gen";
	C = transpose C_(apply(r, i -> i));
	C = apply(numColumns C, j -> C_j)
	);
    
    -- Creates a hashtable of lists indexed by the lattice points of the convex hull
    -- of the (scaled) weight vectors, initialized with the list of each weight vector
    -- being the corresponding variable in the ring.
    S = new MutableHashTable from apply(C, w -> w => {});
    scan(#mons, i -> S#(W1_i) = S#(W1_i)|{mons#i});
    U = new MutableHashTable from S;
    
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
	
	scan(#mons, i -> (
		u := m*mons#i;
        	v' := v + W1_i;
		-- Checks whether the monomial u is not divisible by some monomial m' already
		-- found such that the quotient m'' is invariant under the finite abelian action.
        	if ((U#?v') and all(S#v', m' -> (
			    if u%m' =!= 0_R then true
			    else if g > 0 then (
				m'' := u//m';
			    	v'' := reduceWeight(W2*(vector first exponents m''));
			    	v'' =!= 0_(ZZ^g)
				)
			    else false
			    )
			)
		    ) 
		then( 
                    S#v' = S#v'|{u};
                    U#v' = U#v'|{u};
		    )
	    	)
	    );
	U#v = delete(m, U#v);
	nonemptyU = select(keys U, w -> #(U#w) > 0)
	);
    
    if S#?(0_(ZZ^r)) then mons = S#(0_(ZZ^r)) else mons = {};
    return apply(mons, m -> sub(m, ring D) )
    )

-*
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
    scan(n, i -> S#(W_i) = S#(W_i)|{R_i});
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
    -- if there are no invariants return an empty list
    if S#?(0_(ZZ^r)) then return S#(0_(ZZ^r)) else return {}
    )
*-

-*
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
    scan(n, i -> S#(W_i) = S#(W_i)|{R_i});
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

*-


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

-*
--Computes an *additive* basis for the degree d part of the invariant ring.
invariants (LinearlyReductiveAction, ZZ) := List => o -> (V,d) -> (
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
*-

-- Computes an *additive* basis for the degree d part of the
-- invariant ring following Algorithm 4.5.1 of Derksen-Kemper.
-- This is a variation on Xianlong Ni's original code
-- that should work for quotients of polynomial rings.
-- Degree is passed as a list or as an integer.
invariants (LinearlyReductiveAction, List) := List => o -> (V,d) -> (
    M := actionMatrix V;
    Q := ring V;
    A := groupIdeal V;
    n := #(gens Q);
    K := coefficientRing ring groupIdeal V;
    x := local x, z := local z;
    --X := K[x_1..x_n];
    
    l := #(gens ring M);
    S := Q**K[z_1..z_l];
    M' := sub(M, apply(l, i -> (ring M)_i => S_(n+i)));
    A' := sub(A, apply(l, i -> (ring M)_i => S_(n+i)));
    
    L := sub(basis(d,Q), S);
    if zero L then return {};
    if L == id_(S^1) then return {1_Q};
    r := numColumns L;
    NFDL := apply(r, i -> (sub(L_(0,i), apply(n, j -> S_j => sum(n, k -> M'_(k,j) * S_k))) - L_(0,i)) % A');
    monomialsNFDL := flatten entries monomials(matrix{NFDL});
    m := #monomialsNFDL;
    B := matrix(apply(m, i -> apply(r, j -> coefficient(monomialsNFDL#i, NFDL#j))));
    KB := gens kernel B;
    return flatten entries sub(L * KB, join(apply(n, i -> S_i => Q_i), apply(l, i -> S_(n+i) => 0)))
)

invariants (LinearlyReductiveAction, ZZ) := List => o -> (V,d) -> (
    invariants(V,{d})
    )

--Uses the preceding function together with hilbertIdeal to compute a set of generating invariants.
invariants (LinearlyReductiveAction) := List => o -> V -> (
    I := hilbertIdeal V;
    Q := ring V;
    n := #(gens Q);
    K := coefficientRing ring groupIdeal V;
    x := local x;
    X := K[x_1..x_n];
    
    degreeList := sort unique apply(I_*, i -> degree i);
    generatorList := {};
    
    local d;
    while (#degreeList > 0) do(
	d = degreeList#0;
    	Id := select(I_*, i -> degree i == d);
	
	alreadyInv := true;
	j := 0;
	while alreadyInv and Id#?j do(
	    if not isInvariant(Id#j,V) then alreadyInv = false;
	    j = j+1
	);
    	if not alreadyInv then (
	    generatorList = join(generatorList, invariants(V,d))
	) else (
	    generatorList = join(generatorList, Id);
	);
    	degreeList = drop(degreeList,1)
    );
    return manualTrim generatorList
)

-------------------------------------------
-- invariants for finite groups
-------------------------------------------

-- Below is an implementation of King's algorithm following
-- Derksen-Kemper Algorithm 3.8.2 for the non-modular case
invariants FiniteGroupAction := List => o -> G -> (
    R := ring G; -- ring with group action
    S := {}; -- list of minimal generating invariants
    b := #(group G); -- bound for algorithm termination
    if ( char(R) != 0 and b % char(R) == 0 ) then 
    error "Not implemented in the modular case";
    if unique degrees R =!= {{1}} then
    error "Only implemented for standard graded polynomial rings";
    -- if user provides a DegreeBound smaller than the order of
    -- the group, then use that
    if o.DegreeBound < b then b = o.DegreeBound;
    for d from 1 to b do (
	-- growing GB for computations
    	Gb := gb(promote(ideal S,R),DegreeLimit=>d);
	-- get leading terms
	I := monomialIdeal leadTerm Gb;
	-- take all degree d monomials and reduce modulo I
	-- does not require Groebner bases
	-- empirical evidence suggests reversing order of list
	-- produces nicer looking invariants for GRevLex
	M := reverse select(flatten entries (basis(d,R)%I),m->not zero m);
	-- if all monomials reduce to zero, done
	if M === {} then break else (
	    if o.Reynolds then (
	    	for m in M do (
	    	    f := reynoldsOperator(m,G);
	    	    g := f % Gb;
	    	    if not zero g then (
		    	S = S | {f};
		    	Gb = forceGB ( (gens Gb) | matrix{{g}} );
	    	    	);
		    );
	    	) else (
		for f in invariants(G,d) do (
	    	    g := f % Gb;
	    	    if not zero g then (
		    	S = S | {f};
		    	Gb = forceGB ( (gens Gb) | matrix{{g}} );
	    	    	);
		    );
	    	);
    	    );
	);
    -- in characteristic zero remove denominators
    if char(R) == 0 then (
	S = apply(S,s->(mingens ideal s)_(0,0));
	);
    return S;
    )

-- the following is an implementation of the linear algebra
-- method to compute invariants of a given degree for finite groups
-- following §3.1.1 of Derksen-Kemper
invariants(FiniteGroupAction, List) := List => o -> (G,d) -> (
    R := ring G;
    K := coefficientRing R;
    B := basis(d,R);
    -- for each group generator g and monomial m of degree d
    -- compute g*m-m, then extract coefficients relative to basis B
    L := apply(gens G, g -> sub(B,(vars R)*(transpose g)) - B);
    L = apply(L, l -> last coefficients l);
    -- stack coefficients into single matrix
    -- then move to field and compute kernel
    M := sub(matrix pack(L,1),K);
    C := gens ker M;
    -- multiply kernel generators by variables to get a matrix of
    -- invariants
    I := B*sub(C,R);
    -- return the entries of the matrix
    flatten entries I
    )

-- this allows to pass degree as integer instead of list
invariants(FiniteGroupAction, ZZ) := List => o -> (G,d) -> (
    invariants(G,{d})
    )

-------------------------------------------

isInvariant = method()

isInvariant (RingElement, FiniteGroupAction) := Boolean => (f, G) -> reynoldsOperator(f, G) == f
    -- reynoldsOperator already checks to see if f is in the ring on which G acts.

isInvariant (RingElement, DiagonalAction) := Boolean => (f, D) -> (
    if not instance(f, ring D) then (
	error "isInvariant: Expected an element from the ring on which the group acts."
	);
    (W1, W2) := weights D;
    d := cyclicFactors D;
    torus := W1 * transpose(matrix (exponents f) ); 
    finite := W2 * transpose(matrix (exponents f) );
    return ( torus == 0 and all(#d, i -> finite_0_i%d#i == 0) )
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





