TorusAction = new Type of GroupAction
FiniteAbelianAction = new Type of GroupAction

-------------------------------------------
--- TorusAction methods -------------------
-------------------------------------------

torusAction = method()

torusAction (Matrix, PolynomialRing) := TorusAction => (W, R) -> (
    if not isField coefficientRing R then (error "finiteAction: Expected the second argument to be a polynomial ring over a field.");
    if ring W =!= ZZ then (error "torusAction: Expected the first argument to be a matrix of integer weights.");
    if numColumns W =!= dim R then (error "torusAction: Expected the number of columns of the matrix to equal the dimension of the polynomial ring."); 
    r := numRows W;
    -- coefficient ring for torus characters
    z := getSymbol "z";
    C := ZZ[Variables=>r,VariableBaseName=>z,MonomialOrder=>GroupLex=>r,Inverses=>true];
    new TorusAction from {
	cache => new CacheTable,
	(symbol actionMatrix) => W,
	(symbol degreesRing) => C monoid degreesRing R,
	(symbol ring) => R, 
	(symbol rank) => r
	}
    )


-------------------------------------------

net TorusAction := T -> (net T.ring)|" <- "|(net T.actionMatrix)
-- If the weight matrix is huge, consider rewriting to print something else.

rank TorusAction := ZZ => T -> T.rank

weights = method()

weights TorusAction := Matrix => T -> T.actionMatrix 

degreesRing TorusAction := PolynomialRing => T -> T.degreesRing


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

equivariantHilbertSeries (FiniteAbelianAction) :=
equivariantHilbertSeries (TorusAction) := op -> T -> (
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


-------------------------------------------
--- FiniteAbelianAction methods -----------
-------------------------------------------

finiteAbelianAction = method()

finiteAbelianAction (List, Matrix, PolynomialRing) := FiniteAbelianAction => (L, W, R) -> (
    if not isField coefficientRing R then (error "finiteAbelianAction: Expected the third argument to be a polynomial ring over a field.");
    if ring W =!= ZZ then (error "finiteAbelianAction: Expected the second argument to be a matrix of integer weights.");
    if numColumns W =!= dim R then (error "finiteAbelianAction: Expected the number of columns of the matrix to equal the dimension of the polynomial ring.");
    r := numRows W;
    if r =!= #L then (error "finiteAbelianAction: Expected the number of rows of the matrix to equal the size of the list."); 
    -- coefficient ring for group characters
    z := getSymbol "z";
    C := ZZ[Variables=>r,VariableBaseName=>z,MonomialOrder=>Lex];
    C = C / ideal apply(gens C,L,(x,i)->x^i-1);
    D := newRing(degreesRing R,MonomialOrder=>RevLex,Inverses=>false);
    new FiniteAbelianAction from {
	cache => new CacheTable,
	(symbol actionMatrix) => W,
	(symbol size) => L,
	(symbol ring) => R,
	(symbol numgens) => #L, 
	(symbol degreesRing) => C monoid D
	}
    )

-------------------------------------------

net FiniteAbelianAction := G -> (
    cyclicGroups := apply(G.numgens, i -> (
	    if i == G.numgens - 1 then (net ZZ|"/"|net G.size#i)
	    else (net ZZ|"/"|net G.size#i|" x ")
	    )
	);
    (net G.ring)|" <- "|(horizontalJoin cyclicGroups)|" via "|net G.actionMatrix
    )
-- If the weight matrix is huge, consider rewriting to print something else.

numgens FiniteAbelianAction := ZZ => G -> G.numgens

size FiniteAbelianAction := List => G -> G.size

weights FiniteAbelianAction := Matrix => G -> G.actionMatrix

degreesRing FiniteAbelianAction := QuotientRing => G -> G.degreesRing

