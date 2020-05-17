-- this method prints the equivariant hilbert series
-- for a diagonal torus action on a polynomial ring
-- INPUT: weight matrix for action of torus on variables
-- COMMENT: this is the action on V^* because variables are
-- coordinates of V
equivariantHilbertSeries = method()
equivariantHilbertSeries (Matrix) := Expression => W -> (
    r := numRows W;
    n := numColumns W;
    z := getSymbol "z";
    T := getSymbol "T";
    R := ZZ[z_1..z_r,T, Inverses => true, MonomialOrder=>RevLex];
    ms := apply(n, i -> R_(flatten entries W_{i}));
    den := product apply(ms, m -> expression(1)-expression(m*T_R));
    expression(1)/den
)



-- INPUT: W weight matrix for diagonal torus action on ring,
-- d desired degree for Hilbert function
-- OUTPUT: a Laurent polynomial which is the character of the
-- degree d component of the polynomial ring wrt the torus action
toricHilbertFunction = method()
toricHilbertFunction (Matrix, ZZ) := Thing => (W, d) -> (
    r := numRows W;
    z := getSymbol "z";
    T := getSymbol "T";
    R := ZZ[z_1..z_r,T, Inverses => true, MonomialOrder=>RevLex];
    -- the degree zero component has dimension 1
    n := numColumns W;
    -- compute the denominator of the Hilbert series
    -- which is a polynomial in T of degree n
    ms := apply(n, i -> R_(flatten entries W_{i}));
    D := product apply(ms, m -> 1_R-(m*T_R));
    -- extract its coefficients and degree
    (M,C) := coefficients(D,Variables=>{T_R});
    -- call the function that computes the value recursively
    -- and pass the ring so it's not recreated each time
    recHilb(d,n,C,R)
    )

-- TO DO: should cache and reuse values
-- this computes toric hilbert series recursively
-- it is not exported and not to be called directly
-- INPUT: d desired degree, n degree of denominator of hilbert series,
-- C matrix of coefficients of denominator, R degrees ring
-- COMMENT: calling from toricHilbertFunction creates all
-- inputs correctly
recHilb = (d, n, C, R) -> (
    if d==0 then return 1_R;    
    -sum(toList(1..min(d,n)), k -> 
	binomial(d,k) * k!*C_(k,0) * (d-k)!*recHilb(d-k,n,C,R)
	)//d!
    )


-- INPUT: W weight matrix for diagonal torus action on ring,
-- d desired degree for Hilbert function
-- OUTPUT: dim of degree d component of ring of invariants
-- WARNING: improve consistency with existing hilbertFunction format
hilbertFunction (Matrix, ZZ) := ZZ => (W, d) -> (
    p := toricHilbertFunction(W,d);
    n := numgens ring p;
    -- subbing 0 in variables of Laurent ring always gives 0
    sub(p,matrix{toList(n:0)})
    )

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

totalHilbertSeries = method()
totalHilbertSeries (List) := Thing => (L) -> (
    R:=ring first L;
    l=#L;
    gdegs:= L / degree // flatten;
    z := getSymbol "z";
    S:=QQ[z_1..z_l, Degrees => gdegs];
    phi:=map(R,S,L);
    I:=ker phi;
    T:=S/I;
    return reduceHilbert hilbertSeries T
    )
