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

equivariantHilbertSeries = method()
equivariantHilbertSeries (Matrix) := Expression => W -> (
    r := numRows W;
    n := numColumns W;
    W=-W;
    z := getSymbol "z";
    T := getSymbol "T";
    R := ZZ[z_1..z_r,T, Inverses => true, MonomialOrder=>RevLex];
    ms := apply(n, i -> R_(flatten entries W_{i}));
    den := product apply(ms, m -> expression(1)-expression(m*T_R));
    expression(1)/den
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
