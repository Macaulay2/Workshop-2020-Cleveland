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




deriv = method()
deriv (Matrix, ZZ) := Thing => (W, d) -> (
    r := numRows W;
    z := getSymbol "z";
    T := getSymbol "T";
    R := ZZ[z_1..z_r,T, Inverses => true, MonomialOrder=>RevLex];
    if d==0 then return 1_R;    
    n := numColumns W;
    ms := apply(n, i -> R_(flatten entries W_{i}));
    D := product apply(ms, m -> 1_R-(m*T_R));
    (M,C) := coefficients(D,Variables=>{T_R});
    deg := numRows(C) - 1;
    if d-deg>0 then C = C || map(R^(d-deg),R^1,0);
    recursion(W,d,R,deg,C)
    )

recursion = (W, d, R, deg, C) -> (
    s := -sum(d,k->binomial(d,k)*(d-k)!*C_(d-k,0)*recursion(W,k,R,deg,C))//d!;
    return s;
    )

TEST ///
W=matrix {{-1,0,1},{0,-1,1}};
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
