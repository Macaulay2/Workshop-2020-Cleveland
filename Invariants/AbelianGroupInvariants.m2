restart
primaryInvariantsAbelian = method()
primaryInvariantsAbelian (Matrix, PolynomialRing, List) := Thing => (W, R, L) -> (
    r := numRows W;
    n := numColumns W;
    t := 1; -- t is the size of abelian group
    --sanity check 
    if #L =!= r then print "Size of the group does not match the weight";
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
    local v, m, u, v';
    while  #U > 0 do(
    m = min U; 
    v = vector(apply(n,i->degree(R_i,m))); --degree vector of m
    v = W*v; --weight vector of m
    j := 0;
    scan(n,i->if m % R_i == 0 then (j = i+1;break));
    k := j;
    while k > 0 do(
        u := m*R_(k-1);
        temp := flatten entries (v + W_(k-1));
	temp = apply(#temp,i -> temp_i % L_i);
	v' := matrix(vector temp);
        if all(S#v', m' -> u%m' =!= 0_R) then (
	    S#v' = S#v'|{u};
            if first degree u < t then(
		U = U | {u};
            );
        );
        k = k - 1;
    );
    U = delete(m, U);
    );
    return S#(matrix(0_(ZZ^r)))
)



end


-----example using Amy's code-----
needsPackage "Invariants"
R = QQ[a_1..a_3]
W = matrix{{1,0,1},{0,1,1}}
elapsedTime abelianInvariants(W,R,{3,3})

----same example using InvariantRing package----
needsPackage "InvariantRing"
-- adjoin primitive cubic root of unity to QQ
kk = toField(QQ[z]/ideal(z^2+z+1))
G = generateGroup({matrix{{z,0,0},{0,1,0},{0,0,z}},
    matrix{{1,0,0},{0,z,0},{0,0,z}}},kk)
S = kk[b_1..b_3]
elapsedTime invariantRing(S,G)
