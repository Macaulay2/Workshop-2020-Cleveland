--This file contains torus/abelian action methods and Hilbert series methods
--TODO 7/1/20
--1. Check state of documentation
--2. Check state of tests

DiagonalAction = new Type of GroupAction

-------------------------------------------
--- DiagonalAction methods -------------------
-------------------------------------------

diagonalAction = method()


-- Constructor for a general diagonal action.

diagonalAction (Matrix, Matrix, List, PolynomialRing) := DiagonalAction => (W1, W2, d, R) -> (
    if not isField coefficientRing R then (
	error "diagonalAction: Expected the last argument to be a polynomial ring over a field."
	);
    if ring W1 =!= ZZ or ring W2 =!= ZZ then (
	error "diagonalAction: Expected the first and second arguments to be matrices of integer weights."
	);
    if numColumns W1 =!= dim R or numColumns W2 =!= dim R then (
	error "diagonalAction: Expected the number of columns of each matrix to equal the dimension of the polynomial ring."
	);
    if numRows W2 =!= #d then (
	error "diagonalAction: Expected the number of rows of the second argument to equal the size of the list."
	);
    if any(d, j -> not instance(j, ZZ) or j <= 0) then (
	error "diagonalAction: Expected the second argument to be a list of positive integers."
	);     
    -- coefficient ring for group characters
    r := numRows W1;
    g := numRows W2;
    z := getSymbol "z";
    C := ZZ[Variables=> r + g,VariableBaseName=>z,
	MonomialOrder=> {GroupLex => r,GroupLex => g},
	Inverses=>true];
    new DiagonalAction from {
	cache => new CacheTable,
	(symbol cyclicFactors) => d,
	(symbol degreesRing) => C monoid degreesRing R,
	(symbol numgens) => g, 
	(symbol ring) => R, 
	(symbol rank) => r,
	(symbol weights) => (W1, W2)
	}
    )

diagonalAction (Matrix, List, PolynomialRing) := DiagonalAction => (W, d, R) -> (
    if ring W =!= ZZ then (
	error "diagonalAction: Expected the first argument to be a matrix of integer weights."
	);
    r := numRows W - #d;
    if r < 0 then (
	error "diagonalAction: The number of rows of the matrix cannot be smaller than the size of the list."
	); 
    W1 := W^(apply(r, i -> i));
    W2 := W^(apply(#d, i -> r + i));
    diagonalAction(W1, W2, d, R)
    )

-- Constructor for a diagonal torus action.

diagonalAction (Matrix, PolynomialRing) := DiagonalAction => (W, R) -> diagonalAction(W, {}, R)


-------------------------------------------

net DiagonalAction := D -> (
    torus := "";
    cyclicGroups := "";
    r := D.rank;
    g := D.numgens;
    local weightMatrix;
    if r > 0 then (
	torus = (expression coefficientRing D.ring)^(expression "*");
	if r > 1 then torus = (expression ("("|net torus|")"))^(expression r)
	);
    if g > 0 then (
	cyclicGroups = cyclicGroups|horizontalJoin apply(g, i -> (
		if i == g - 1 then (net ZZ|"/"|net D.cyclicFactors#i)
		else (net ZZ|"/"|net D.cyclicFactors#i|" x ")
		)
	    );
	if r > 0 then (
	    torus = net torus|" x ";
	    weightMatrix = D.weights
	    )
	else weightMatrix = last D.weights
	)
    else weightMatrix = first D.weights;
    stack {(net D.ring)|" <- "|net torus|net cyclicGroups|" via ","", net weightMatrix}
    )

cyclicFactors = method()

cyclicFactors DiagonalAction := List => D -> D.cyclicFactors

degreesRing DiagonalAction := Ring => D -> D.degreesRing

numgens DiagonalAction := ZZ => D -> D.numgens

rank DiagonalAction := ZZ => D -> D.rank

weights = method()

weights DiagonalAction := Matrix => D -> D.weights


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

equivariantHilbertSeries DiagonalAction := op -> T -> (
    if #(gens degreesRing T) != 1 then
    error "only implemented for standard graded polynomial rings";
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
    W1 := first weights T;
    W2 := last weights T;
    -- reduce entries of W2 mod group orders so they are >=0
    d := cyclicFactors T;
    W2 = matrix apply(entries W2,d,(row,m)->apply(row,i->i%m));
    -- stack weights into one matrix
    W := W1 || W2;
    R := degreesRing T;
    C := coefficientRing R;
    -- tally the weights of the action
    p := pairs tally entries transpose W;
    -- for each weight form 1-zT factor with power from tally
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
	r := rank T;
	g := numgens T;
	cf := cyclicFactors T;
    	den := value denominator equivariantHilbertSeries T;
    	denDeg := first degree den;
	B := last coefficients den;
	-- this map sends coefficients of the Hilbert series
	-- to their own ring without the variable T
	CR := coefficientRing R;
	phi := map(CR,R);
	-- next map gets rid of the torus characters
	-- by substituting 1 into them
	-- it also takes abelian characters mod cyclic factors
	CRab := ZZ[Variables=>g];
	CRab = CRab / ideal apply(g,i -> CRab_i^(cf_i)-1);
	psi := map(CRab,CR,toList(r:1)|(gens CRab));
	-- next map 'goes back' into ring of all characters
	psi' := map(CR,CRab,apply(g, i-> CR_(r+i)));
	-- now reduce the existing coefficients
	(m,c) := coefficients(phi B,Variables=>apply(g, i-> CR_(r+i)));
	m = psi' psi m;
	B = m*c;
	for i from currentDeg+1 to d do (
	    -- coefficient of the next degree in the recursion
	    p := -sum(1..min(i,denDeg),k -> C_(i-k,0)*B_(k,0) );
	    -- send p to the ring without T and get coefficients
	    (m,c) = coefficients(phi p,Variables=>apply(g, i-> CR_(r+i)));
	    -- applying psi reduces exponents as desired
	    -- applying psi' brings back to ring with other vars
	    m = psi' psi m;
	    -- monomials*(new coeffs)=desired poly
	    p = (m*c)_(0,0);
	    -- add this new coeff and the power of T
	    M = M | matrix{{R_0^i}};
	    C = C || matrix{{p}};
	    );
	);
    -- compute expansion up to desired degree
    q := first flatten entries (M_{0..d}*C^{0..d});
    -- store and return
    T.cache.equivariantHilbert = q
    )
