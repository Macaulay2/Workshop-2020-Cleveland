--This file contains method to compute the Hilbert ideal for linearly reductive action
--TODO 6/26/20 
--1. Currently no specific TODO on this file, check code to see if any
--2. Check state of documentation
--3. Check state of tests
	  

-------------------------------------------
--- LinearlyReductiveAction methods -------
-------------------------------------------
LinearlyReductiveAction = new Type of GroupAction  

linearlyReductiveAction = method()

linearlyReductiveAction (Ideal, Matrix, PolynomialRing) :=
linearlyReductiveAction (Ideal, Matrix, QuotientRing) := LinearlyReductiveAction => (A, M, Q) -> (
    R := ambient Q;
    if not isField coefficientRing R then (error "linearlyReductiveAction: Expected the third argument to be a polynomial ring over a field.");
    if (numColumns M =!= numRows M) or (numRows M =!= #(gens R)) then (error "linearlyReductiveAction: Matrix size does not match polynomial ring.");
    if coefficientRing ring A =!= coefficientRing R then (error "linearlyReductiveAction: Group and polynomial ring not defined over same field.");
    new LinearlyReductiveAction from {
	cache => new CacheTable,
	(symbol groupIdeal) => A, 
	(symbol actionMatrix) => M, 
	(symbol ring) => Q
	}
    )


-------------------------------------------

net LinearlyReductiveAction := V -> (
    stack {(net V.ring)|" <- "|(net ring V.groupIdeal)|"/"|(net V.groupIdeal)|" via ",
	"", net V.actionMatrix}
    )

actionMatrix = method()

actionMatrix LinearlyReductiveAction := Matrix => V -> V.actionMatrix

groupIdeal = method()

groupIdeal LinearlyReductiveAction := Ideal => V -> V.groupIdeal


---------------------------------------------

hilbertIdeal = method()

hilbertIdeal LinearlyReductiveAction := { } >> opts -> (cacheValue (symbol hilbertIdeal)) (V -> runHooks(LinearlyReductiveAction, symbol hilbertIdeal, V))

addHook(LinearlyReductiveAction, symbol hilbertIdeal, V -> break (
    A := groupIdeal V;
    M := actionMatrix V;
    R := ring V;
    if (numColumns M =!= numRows M) or (numRows M =!= #(gens R)) then print "Matrix size does not match polynomial ring";
    -- first, some information about the inputs:
    n := #(gens R);
    K := coefficientRing(R);
    l := #(gens ring M);
    
    -- now make the enlarged polynomial ring we'll work in, and convert inputs to that ring
    x := local x, y := local y, z := local z;
    S := K[z_1..z_l, x_1..x_n, y_1..y_n];
    M' := sub(M, apply(l, i -> (ring M)_i => z_(i+1)));
    A' := sub(A, apply(l, i -> (ring M)_i => z_(i+1)));
    
    -- the actual algorithm follows
    J' := apply(n, i -> y_(i+1) - sum(n, j -> M'_(j,i) * x_(j+1)));
    J := A' + ideal(J');
    I := eliminate(apply(l, i -> z_(i+1)),J);
    II := sub(I, apply(n, i -> y_(i+1) => 0));
    
    -- return the result back in the user's input ring R
    trim(sub(II, join(apply(n, i -> x_(i+1) => R_i),apply(n, i -> y_(i+1) => 0), apply(l, i -> z_(i+1) => 0))))
    ))




