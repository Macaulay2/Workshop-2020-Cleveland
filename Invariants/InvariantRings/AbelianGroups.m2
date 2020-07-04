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
    --C := ZZ[Variables=> r + g,VariableBaseName=>z, Inverses => true, MonomialOrder=> GroupLex];
    --if g > 0 then C = C / ideal apply(g, i -> C_(r+i)^(d#i) - 1);
    --D := newRing(degreesRing R,MonomialOrder=>RevLex,Inverses=>false);
    new DiagonalAction from {
	cache => new CacheTable,
	(symbol cyclicFactors) => d,
	--(symbol degreesRing) => C monoid D,
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
	    torus = torus|" x ";
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
    W := (first weights T)||(last weights T);
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




