needsPackage("Polyhedra", Reload => true)

primaryInvariants = method()

primaryInvariants (Matrix, PolynomialRing) := Thing => (W, R) -> (
    r := numRows W;
    n := numColumns W;
    local C;
    if r == 1 then C = convexHull W else C = convexHull( 2*r*W|(-2*r*W) );
    C = (latticePoints C)/vector;
    S := new MutableHashTable from apply(C, w -> w => {});
    scan(n, i -> S#(W_i) = {R_i});
    U := new MutableHashTable from S;
    local v, m, v', u;
    nonemptyU := select(keys U, w -> #(U#w) > 0);
    while  #nonemptyU > 0 do(
	v = first nonemptyU;
	m = first (U#v);
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
    return S#(0_(ZZ^r))
    )


TEST ///


R1 = QQ[x_1..x_4]
W1 = matrix {{-3, -1, 1, 2}}
invariants1 =  set {x_2*x_3, x_2^2*x_4, x_1*x_3*x_4, x_1*x_2*x_4^2, x_1^2*x_4^3, x_1*x_3^3}
assert(set primaryInvariants(W1, R1) === invariants1)


///