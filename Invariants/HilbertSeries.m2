restart
needsPackage "InvariantsDev"

--presentation of invariant ring as polynomial ring modulo ideal
--implement as a hook so kernel is not recomputed each time
--NOTE: presentation is a method without options so I do not know
--how to pass an option for the variable base name
presentation RingOfInvariants := Ring => S -> (
    -- get ambient ring and generators of invariant ring
    R := ambient S;
    L := generators S;
    -- get degrees of generators
    gdegs := L / degree // flatten;
    -- form a presentation of the invariant ring
    U := QQ[Variables => #L,--number of variables
	VariableBaseName => symbol u,--symbol
	Degrees => gdegs];--degrees
    phi := map(R,U,L);
    I := ker phi;
    U/I
    )

--hilbert Series of invariant ring
hilbertSeries RingOfInvariants := Divide => op -> S -> (
    hilbertSeries(presentation S,Order=>op.Order,Reduce=>op.Reduce)
    )

-- creates and stores the degrees ring for the toric hilbert series
-- currently stores to cache
-- later create this as part of the action and store one
-- level above cache
degreesRing TorusAction := PolynomialRing => T -> (
    if T.cache.?degreesRing then T.cache.degreesRing
    else (
    	r := rank T;
    	z := getSymbol "z";
    	-- coefficient ring for torus characters
	C := ZZ[Variables=>r,VariableBaseName=>z,
	    MonomialOrder=>GroupLex=>r,Inverses=>true];
    	-- ring for the toric Hilbert series
    	R := C monoid degreesRing ring T;
    	-- store and return
	T.cache.degreesRing = R
	)
    )


-- this method returns the equivariant hilbert series
-- for a diagonal torus action on a polynomial ring
-- NOTE: torus must act diagonally on single graded polynomial ring
-- by default, the series is returned as a rational function
-- if the option Order=>d is used, the expansion of the series
-- up to degree d-1 is returned
toricHilbertSeries = method(Options => {Order => infinity})
toricHilbertSeries (TorusAction) := Thing => op -> T -> (
    ord := op.Order;
    if ord === infinity then (
	toricHilbertRational(T)
	)
    else (
	toricHilbertPartial(T,ord-1)
	)
    )

-- toric Hilbert series as a rational function
-- do not export
toricHilbertRational = T -> (
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
toricHilbertPartial = (T, d) -> (
    -- if not existing, create in the cache
    if not T.cache.?toricHilbert then (
	T.cache.toricHilbert = 1_(degreesRing T);
	);
    -- how far was it previously computed?
    -- get degree and coefficients
    currentDeg := first degree T.cache.toricHilbert;
    (M,C) := coefficients T.cache.toricHilbert;
    -- compute higher degrees recursively
    if (d > currentDeg) then (
	R := degreesRing T;
    	den := value denominator toricHilbertSeries T;
    	denDeg := first degree den;
	B := last coefficients den;
	for i from currentDeg+1 to d do (
	    M = M | matrix{{R_0^i}};
	    C = C || matrix{{-sum(1..min(i,denDeg),k -> C_(i-k,0)*B_(k,0) )}};
	    );
	);
    -- return a polynomial up to desired degree
    first flatten entries (M_{0..d}*C^{0..d})
    )


-- examples
-- finite abelian
R = QQ[x_1..x_3]
d = {3,3}
W = matrix{{1,0,1},{0,1,1}}
A = finiteAbelianAction(d, W, R)
S = R^A
presentation S
hilbertSeries S
hilbertSeries(S,Reduce=>true)
hilbertSeries(S,Order=>5)
-- torus
R = QQ[x_1..x_4]
W = matrix{{0,1,-1,1},{1,0,-1,-1}}
T = torusAction(W, R)
S = R^T
toricHilbertSeries T
h = toricHilbertSeries(T,Order=>8)
phi = map(degreesRing R, degreesRing T)
phi h
hilbertSeries(S,Order=>8)

----------------------------------------
-- Fred's experiments
----------------------------------------

-- for testing only
-- can be removed eventually
testHilbertFunction = method()
testHilbertFunction (Matrix, ZZ) := Thing => (W, d) -> (
    r := numRows W;
    z := getSymbol "z";
    T := getSymbol "T";
    R := ZZ[z_1..z_r,T, Inverses => true, MonomialOrder=>RevLex];
    -- the degree zero component has dimension 1
    n := numColumns W;
    -- compute the denominator of the Hilbert series
    -- which is a polynomial in T of degree n
    ms := apply(n, i -> R_(flatten entries W_{i}));
    fs := apply(n, i -> sum apply(d+1, j -> (ms#i*(T_R))^j));
    g := product fs;
    (M,C) := coefficients(g,Variables=>{T_R});
    C_(d,0)
    )



------------------------------
-- Luigi's code --------------
------------------------------
partialToricHilbertSeries = method()
partialToricHilbertSeries (Matrix, ZZ) := Thing => (W, d) -> (
    r := numRows W;
    n := numColumns W;
    W=-W;
    z := getSymbol "z";
    t := getSymbol "t";
    R := QQ[z_1..z_r,t, Inverses => true, MonomialOrder=>Lex];
    ms := apply(n, i -> R_(flatten entries W_{i}));
    fs := apply(n, i -> sum apply(d, j -> (ms#i*(t_R))^j));
    g := product fs;
    L := sum select(terms g, term -> (isSubset(support(term),{t_R}) and first degree term <= d));
    L
)

TEST ///
W=-matrix {{-1,0,1},{0,-1,1}};
d=9;
s=partialToricHilbertSeries(W,d)
R= ring s;
series=1+t^3+t^6+t^9
assert(s === series)
///

