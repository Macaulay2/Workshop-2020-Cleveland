newPackage(
	"NumericalCertification",
    	Version => "1.0", 
    	Date => "October, 2018",
    	Authors => {
	     {Name => "Kisun Lee", Email => "klee669@gatech.edu"},
	     {Name => "Thomas Yahl", Email => "thomasjyahl@math.tamu.edu"},
     	     {Name => "Special thanks: Michael Burr, Anton Leykin"}
	     },
    	HomePage => "http://people.math.gatech.edu/~klee669",
    	Headline => "numerical certification",
	PackageExports => {"NumericalAlgebraicGeometry"},
	Configuration => {"ALPHACERTIFIEDexec" => "alphaCertified"},
    	DebuggingMode => true,		 -- set to true only during development
    	--DebuggingMode => false,
	AuxiliaryFiles => true
    	)

-- Any symbols or functions that the user is to have access to
-- must be placed in one of the following two lists

export {"pointNorm", 
    "ALPHACERTIFIEDexec",
    "polyNorm", 
    "polySysNorm", 
    "newtonOper",
    "computeConstants", 
    "certifyRegularSolution", 
    "certifyDistinctSolutions", 
    "certifyRealSolution",
    "alphaTheoryCertification",
    "Interval", 
    "interval", 
    "mInterval", 
    "intervalNorm", 
    "intervalMatrix", 
    "IntervalMatrix", 
    "wInterval", 
    "intervalMatrixNorm",
    "krawczykOper", 
    "InvertibleMatrix",
    "krawczykMethod",
    "krawczykMethodOptions",
    "identityIntMat", 
    "intervalOption",
    "IntervalOption",
    "subOnMonomial",
    "intervalOptionList", 
    "IntervalOptionList",
    "ingredientsForKoper",
    "inverseMat",
    "intervalJacMat",
    "sqabsForGaussianRational",
    "conjugateGaussian",
    "conjugateGaussianRationalMatrix",
    "degCoeff",
    "toACertifiedPoly",
    "pointBlock",
    "toACertifiedPoint",
    "alphaCertified",
    "ALGORITHM",
    "ARITHMETICTYPE",
    "PRECISION",
    "REFINEDIGITS",
    "NUMRANDOMSYSTEMS",
    "RANDOMDIGITS",
    "RANDOMSEED",
    "NEWTONONLY",
    "NUMITERATIONS",
    "REALITYCHECK",
    "REALITYTEST",
    "Hessian",--
    "computeOrthoBasis",--
    "computeD",
    "Aoperator",--these are added
    "Hoperator",--these are added
    "gammaKBound",--these are added 
    "certifyRootMultiplicityBound"--these are added
    }
exportMutable {}



ALPHACERTIFIEDexe=(options NumericalCertification).Configuration#"ALPHACERTIFIEDexec"


Interval = new Type of List
IntervalOption = new Type of Option
IntervalMatrix = new Type of List
IntervalOptionList = new Type of List

-- the following net function changes design of intervals in M2 output
net Interval := i -> net "[" | net first i | ", " | net last i | "]" 


conjugateGaussian = method()
conjugateGaussian(RingElement) := x -> (
    R := ring x;
    var := first gens R;
    x - 2* var * coefficient(var, x)
    )

conjugateGaussianRationalMatrix = method()
conjugateGaussianRationalMatrix(Matrix) := m -> (
    matrix apply(entries m, k -> apply(k, i -> conjugateGaussian i))
    )


sqabsForGaussianRational = method()
sqabsForGaussianRational(RingElement) := x -> (
    R := ring x;
    var := first gens R;
    rationalRing := coefficientRing R;
    sub((coefficient(var, x))^2, rationalRing) + sub((x - var * coefficient(var, x))^2, rationalRing)
    )



pointNorm = method()
pointNorm(Point) := x -> (
    pointNorm matrix x
    )
pointNorm(Matrix) := x -> (
    coordinateList := flatten entries x;
    -- returns the square of the norm
    R := ring first coordinateList;
    if precision R =!= infinity then (
    	1 + sum(apply(coordinateList, i -> abs(i)^2))
	)
    else if R =!= QQ then (
	var := first gens R;
	rationalRing := coefficientRing R;
	1 + sum apply(coordinateList, i -> sqabsForGaussianRational i)
	)
    else (
    	1 + sum(apply(coordinateList, i -> i^2))
	)
    )



polyNorm = method()
polyNorm(Number) := r -> (
    abs(r)^2
    )
polyNorm(RingElement) := r -> (
    R := coefficientRing ring r;
    L := listForm r;
    if precision R =!= infinity then (
	sum(L,a->(
		(e,c) := a;
		abs(c)^2*(product(e,b->b!)*(((degree r)#0-(sum e))!)/((degree r)#0)!)
		)
	)
    )
    else if R =!= QQ then (
	var := first gens R;
	rationalRing := coefficientRing R;
    	sum(L,a->(
	(e,c) := a;
	    (sqabsForGaussianRational c)*(product(e,b->b!)*(((degree r)#0-(sum e))!)/((degree r)#0)!)
 	))
	)
    else (
	sum(L,a->(
		(e,c) := a;
		(c^2)*(product(e,b->b!)*(((degree r)#0-(sum e))!)/((degree r)#0)!)
		)
	)
	)
    )





polySysNorm = method()
polySysNorm(PolySystem) := f -> (
    listOfEq := equations f;
    listOfpolyNorms := apply(listOfEq, i -> polyNorm(i));
    N := sum listOfpolyNorms
    )


newtonOper = method()
newtonOper(PolySystem, Point) := (f, x) -> (
    newtonOper(f, matrix x)
    )
newtonOper(PolySystem, Matrix) := (f, x) -> (
    jacOfPoly := jacobian f;
    evalJac := evaluate(jacOfPoly, x);
    inverseOfJac := inverse(evalJac);
    evalSys := evaluate(f, x);
    point {transpose x - inverseOfJac * evalSys}
    )
    


computeConstants = method() --computes alpha^2 beta^2 gamma^2
computeConstants(PolySystem, Matrix) := (f, x) -> (
    computeConstants(f, point x)
    )
computeConstants(PolySystem, Point) := (f, x) -> (
    eqs := equations f;
    J := evaluate(jacobian f, x);
    inverseJ := inverse J;
    R := coefficientRing ring f;
    pointNormx := pointNorm x;
    degs := select(flatten apply(eqs, i -> degree i), i -> i =!= 0);
    if precision R =!= infinity then (
	R = R;
    	if det J == 0 then error "The Jacobian is not invertible";
    	-- beta
    	y := point(inverseJ * evaluate(f,x));
    	beta := sub(sum apply(y#Coordinates, i -> abs(i)^2),R);
    	deltaD := diagonalMatrix flatten apply(degs, i -> sqrt(i * (pointNormx)^(i-1))); 
     	mu := max {1, polySysNorm(f) * (norm(2,inverseJ * deltaD))^2};
	)
    else if R =!= QQ then (
	var := first gens R;
	R = coefficientRing R;
	print "Warning: invertibility check for Jacobian is skipped for Gaussian rational inputs";
    	-- beta
    	y = point(inverseJ * evaluate(f,x));
    	beta = sub(sum apply(y#Coordinates, i -> sqabsForGaussianRational i),R);
    	deltaD = diagonalMatrix flatten apply(degs, i -> i * (pointNormx)^(i-1)); 
	sqFrobenius := trace(inverseJ * deltaD * (transpose conjugateGaussianRationalMatrix inverseJ));
     	mu = max {1, polySysNorm(f) * (sub((coefficient(var, sqFrobenius))^2, R) + sub((sqFrobenius - var * coefficient(var,sqFrobenius)), R))};  
	)
    else (
	R = R;
    	if det J == 0 then error "The Jacobian is not invertible";
    	-- beta
    	y = point(inverseJ * evaluate(f,x));
    	beta = sub(sum apply(y#Coordinates, i -> i^2),R);
    	deltaD = diagonalMatrix flatten apply(degs, i -> i * (pointNormx)^(i-1)); 
     	mu = max {1, polySysNorm(f) * trace(inverseJ * deltaD * (transpose inverseJ))};  
	); 
    -- gamma
    gamma := sub(mu*((max degs)^3)/(4* pointNormx), R);
    alpha := sub(beta * gamma, R);
    (alpha, beta, gamma)
    )


certifyRegularSolution = method() -- returns null if not successful, (alpha,beta,gamma) if alpha-certified 
certifyRegularSolution(PolySystem, Matrix) := (f, x) -> (
    computeConstants(f, point x)
    )
certifyRegularSolution(PolySystem, Point) := (f, x) -> (
    alpha := first computeConstants(f,x);
    -- check: alpha < (13-3*sqrt(17))/4
    if 16*alpha < 169 and (322-16*alpha)^2 > 78*78*17 then true else false
    )
certifyRegularSolution(PolySystem, List) := (f, L) -> (
    apply(L, i -> certifyRegularSolution(f, i))
    )

certifyDistinctSolutions = method()
certifyDistinctSolutions(PolySystem, Matrix, Matrix) := (f, x1, x2) -> (
    certifyDistinctSolutions(f, point x1, point x2)
    )
certifyDistinctSolutions(PolySystem, Point, Point) := (f, x1, x2) -> (
    R := coefficientRing ring f;
    if precision R =!= infinity then (
	R = R;
	)
    else if R =!= QQ then (
	R = coefficientRing R;
	)
    else (
 	R = R;
	); 
    Consts1 := computeConstants(f,x1);
    Consts2 := computeConstants(f,x2);
    if precision R =!= infinity then (
    	normOfDist := (norm(2,point{(coordinates x1)-(coordinates x2)}))^2;
	)
    else (
    	normOfDist = sum apply((point{(coordinates x1)-(coordinates x2)})#Coordinates, c->sub(c^2,R));
	);
    if Consts1 #0 >= ((13-3*sqrt(17))/4)^2 or Consts2 #0 >= ((13-3*sqrt(17))/4)^2 then (
	false
	)
    else if normOfDist > 4*((Consts1)#1 + (Consts2)#1 + 2*sqrt((Consts1)#1 * (Consts2)#1)) then (
	true
	)
    else if (Consts1)#0 < 9/10000 and normOfDist < 1/(400*(Consts1)#2) or (Consts2)#0 < 9/10000 and normOfDist < 1/(400*(Consts2)#2) then (
	false
	)
    else (
      	false
	)
    )


certifyRealSolution = method()
certifyRealSolution(PolySystem, Matrix) := (f, x) -> (
    certifyRealSolution(f, point x)
    )
certifyRealSolution(PolySystem, Point) := (f, x) -> (
    (alpha, beta, gamma) := computeConstants(f,x);
    R := coefficientRing ring f;
    if precision R =!= infinity then (
    	imagPart := apply(coordinates x, i -> imaginaryPart(i));
	R = R;
	)
    else if R =!= QQ then (
	coordinatesOfx := coordinates x;
	l := length coordinatesOfx;
	imagPart = {};
	for i from 0 to l-1 do if degree(coordinatesOfx#i) === 1 then (
		append(imagPart,leadCoefficient sub(i,R));
		)
	    else (
		append(imagPart, 0);
		);
	R = coefficientRing R;
	)
    else (
    	imagPart = apply(coordinates x, i -> imaginaryPart(i));
	R = R;
	); 
    normOfimagPart := sum apply(imagPart, i -> sub(i^2,R));
    if (normOfimagPart > 4*beta) then false
    else if alpha < 9/10000 and normOfimagPart < 1/(400*gamma) then true
    else (
	print "apply more Newton's operators!";
    false
    )
    )

alphaTheoryCertification = method()
alphaTheoryCertification(PolySystem, List) := (f, X) -> (
    R := coefficientRing ring f;
    if precision R =!= infinity then (
	R = R;
	)
    else if R =!= QQ then (
	R = coefficientRing R;
	)
    else (
 	R = R;
	); 
    Y := select(X, i->certifyRegularSolution(f,i)=!=false); 
    C := apply(X, i-> first computeConstants(f,i)); -- Can we have this without using function twice?
    S := new MutableList from Y;
    for i from 0 to length(Y) - 1 do S#i = true;
    for i from 0 to length(Y) - 2 do for j from i+1 to length(Y) - 1 do if (
	S#i == true and S#j == true
	)
    then (
	S#j = certifyDistinctSolutions(f,Y#i, Y#j);
	);
    D := {};
    for i from 0 to length(Y) - 1 do if S#i == true then D = append(D, Y#i);
    Real := {};
    if R =!= CC then for i from 0 to length(D) - 1 do if certifyRealSolution(f,D#i) == true then Real = append(Real,D#i);
    new HashTable from {"certifiedSolutions" => Y, "alphaValues" => C, "certifiedDistinct" =>D, "certifiedReal" => Real}
    )










-- a function converting a polynomial into alphaCertified input format.
-- input : polynomial
-- output : the first line is the number of terms of an input.
--    	    the second to last lines represent terms of an input polynomial in a way that
--    	    the first (variable-many) numbers are  degrees of each variable in the monomial and 
--          the last two numbers are real and imaginary parts of its coefficient
degCoeff = method()
degCoeff(RingElement) := f -> (
    variables := gens ring f;
    R := coefficientRing ring f;
    if precision R == infinity then (
	print "error! Use a polynomial ring with coefficients CC or RR"; break
	);
    (E, C) := coefficients f;
    E = flatten entries E;
    C = flatten entries C;
    strList := apply(length E, i -> 
        replace("[{,},,]", "", toString(apply(variables, j -> 
	    degree(j, E#i)) | {lift(realPart sub(C#i,CC), QQ), lift(imaginaryPart sub(C#i,CC), QQ)}))
	);
    prepend(length E, strList)
    )
    
    
    


-- a function converting a polynomial system into alphaCertified input format.
-- input : polynomial system
-- output : a directory to a temporary file which can be used as an input for alphaCertified.
--          the first line consists of the number of variables and the number of polynomials.
--    	    each block represents information about each polynomial in the system.
toACertifiedPoly = method()
toACertifiedPoly(PolySystem) := P -> (
    fn := temporaryFileName();
    (numOfVars, numOfPolys) := (P.NumberOfVariables, P.NumberOfPolys);
    fn << toString numOfVars | " " | toString numOfPolys << endl;
    fn << "" << endl;
    polyList := flatten entries P.PolyMap;
    strList := apply(polyList, i -> 
	degCoeff i);
    apply(flatten strList, i -> fn << i << endl);
    fn << close;
    fn
    )



-- a function converting a point into a block of digits for alphaCertified input.
-- input : Matrix representing a coordinate of a point or Point
-- output : a list of coordinates of a given point.
pointBlock = method()
pointBlock(Point) := P -> (
    pointBlock matrix P
    )
pointBlock(Matrix) := M -> (
    strList := apply(flatten entries M, i -> 
        replace("[{,},,]", "", toString({lift((realPart i)_QQ,QQ), lift((imaginaryPart i)_QQ,QQ)}))
	);
    strList = append(strList, "")    
    )
    
    

toACertifiedPoint = method()
toACertifiedPoint(List) := L -> (
    fn := temporaryFileName();
    n := length L;
    fn << toString n << endl;
    fn << "" << endl;
    apply(L, i -> 
	apply(pointBlock i, j -> 
	    fn << j << endl)
	);
    fn << close;
    fn
    )
    
alphaCertified = method(Options => {
	ALGORITHM => 2,
	ARITHMETICTYPE => 0,
	PRECISION => 96,
	REFINEDIGITS => 0,
	NUMRANDOMSYSTEMS => 2,
	RANDOMDIGITS => 10,
	RANDOMSEED => random 10000,
	NEWTONONLY => 0,
	NUMITERATIONS => 2,
	REALITYCHECK => 1,
	REALITYTEST => 0
	}
	)
alphaCertified(PolySystem, List) := o -> (P, L) -> (
    fin1 := toACertifiedPoly P;
    fin2 := toACertifiedPoint L;
    fin3 := temporaryFileName();
    apply(# o, i -> fin3 << toString(keys o)#i | ": "|toString(values o)#i|";" << endl);
    fin3 << close;
    run("cd " | ALPHACERTIFIEDexe |"; ./alphaCertified " | fin1 |" "| fin2 |" " | fin3);
    )
    
    
    







--------------------------------
--Start Multiple Roots Section--
--------------------------------
--make everything work with exact arithmetic.


FrobeniusSquared = method()
FrobeniusSquared(Matrix) := M->(
    R := ring M;
    if (R === QQ) then (
	trace(transpose(M)*M)
	) else if (numgens R == 1) then (
	i := first gens R;
	trace(transpose(M)*sub(M,i=>-i))
	) else (
	(norm(2,M))^2
	)
    )

--this is kind of dumb, but its an easy solution
roundUp = method()
roundUp(RR) := z->(
    ceiling(10^30*z)/10^30
    )

Hessian = method(TypicalValue => Matrix)
Hessian(PolySystem) := f->(
    return(jacobian jacobian f)
    )

Hessian(PolySystem,Point) := (f,x0)->(
    return(evaluate(Hessian(f),x0))
    )

rationalUnitaryMatrix = method(TypicalValue => Matrix)
rationalUnitaryMatrix(ZZ) := n->(
    M := random(QQ^n,QQ^n,UpperTriangular=>true);
    S := M-transpose(M);
    I := id_(QQ^n);
    A := inverse(S-I)*(S+I);
    return(A)
    )

--this is currently non-deterministic. 
computeOrthoBasis = method(TypicalValue => Matrix)
computeOrthoBasis(PolySystem,Point) := (F,x0)->(
    R := coefficientRing ring F;
    n := F#NumberOfPolys;
    J := evaluate(jacobian F,x0);
    --this if should basically be "if the ring is the Gaussian rationals"                                                                    
    ----the map phi just makes Gaussian rationals into complex numbers                                                                     
    if (numgens R == 1) then (
        phi := map(CC,R,{ii+0p53});
        J = phi(J)
        ) else (
        J = sub(J,CC)
        );
    kappa := n-numericalRank J;
    V := submatrix(rationalUnitaryMatrix(n),0..kappa-1);
    return(V)
    )

Aoperator = method(TypicalValue => Matrix)
Aoperator(PolySystem,Point,Matrix) := (F,x0,V)->(
    n := F#NumberOfPolys;
    eqs := equations F;
    J := evaluate(jacobian F,x0);
    --is there a way to get individual equations as polySystems?
    HessianList := apply(eqs,f->Hessian(polySystem matrix{{f}},x0));
    kappa := numcols V;
    --this is bad, find a better way of writing this.
    A := J + 1/2*sum(kappa,i->fold(apply(n,j->transpose(V_{i})*HessianList#j*V_{i}*transpose(V_{i})),(A,B)->A||B));
    return(A)
    )



Hoperator = method(TypicalValue => Matrix)
Hoperator(PolySystem,Point,Matrix) := (F,x0,V)->(
    J := evaluate(jacobian F,x0);
    H := J*V*(transpose V);
    return(H)
    )

--this is used only for finite precision currently.
gammaKBound = method(TypicalValue => Number)
gammaKBound(PolySystem,Point) := (F,x0)->(
    eqs := equations F;
    pointNormx := pointNorm x0;
    degs := select(flatten apply(eqs, i -> degree i), i -> i =!= 0);
    V := computeOrthoBasis(F,x0);
    A := Aoperator(F,x0,V);
    H := Hoperator(F,x0,V);
    deltaF := diagonalMatrix flatten apply(degs, i -> sqrt(i * (pointNormx)^(i-1))); 
    mu := max {1, polySysNorm(F) * norm(2,inverse(A-H) * deltaF)};
    gammaK := mu*(max degs)^(3/2)/(2*pointNormx);
    return(gammaK)
    )

computeD = method()
computeD(Number) := k -> (
    d := symbol d;
    R := RR[d];
    f := (1-d^2)-(k+1)^2 * k^2 * d^2 * (1-d^2) - k*d^2 - d;
    listOfRoots := roots f;
    min delete( ,apply(listOfRoots, i -> 
	    if (imaginaryPart i) == 0 and (realPart i) > 0 then i))
    )

--needs better name and output
--needs to be checked a bit
certifyRootMultiplicityBound = method(TypicalValue => ZZ)
certifyRootMultiplicityBound(PolySystem,Point) := (F,x0)->(
    R := coefficientRing ring F;
    eqs := equations F;
    degs := select(flatten apply(eqs, i -> degree i), i -> i =!= 0);
    pointNormx := pointNorm x0;
    V := computeOrthoBasis(F,x0);
    A := Aoperator(F,x0,V);
    H := Hoperator(F,x0,V);
    kappa := numcols V;
    --worry about rounding this?
    d := roundUp realPart computeD kappa;
    rhs := 1;
    lhs := 1;
    
    if (numgens R == 1) then (
	--this is to make gaussian rationals actual complex numbers
	phi := map(CC,R,{ii+0p53});
	--this computes the inequality differently to be more computable for exact computation.
	deltaFNormSquared := sum(degs,di->di*pointNormx^(2*(di-1)));
	muSquared := max {1, polySysNorm(F) * FrobeniusSquared(inverse(A-H)) * deltaFNormSquared};
	gammaKSquared := (max degs)^3 * muSquared/(4*pointNormx);
	Feval := evaluate(F,x0);
	normFeval := roundUp norm(2,phi(evaluate(F,x0)));
	normH := roundUp norm(2,phi(H));
	normInverseAminusH := roundUp norm(2,phi(inverse(A-H)));
	
	--this needs a LOWER bound for gammaK. 
	--1 is the lower bound used here.
	lhs = sub(normFeval + normH*d/4,QQ);
	rhs = sub(d / (32 * gammaKSquared^2 * normInverseAminusH),QQ);
	return(lhs < rhs, 2^kappa)
	
	) else (
	
    	deltaF := diagonalMatrix flatten apply(degs, i -> sqrt(i * (pointNormx)^(i-1)));
	
    	lhs = norm(2,evaluate(F,x0)) + (d)*norm(2,H)/4;
    	rhs = d/(32*(gammaKBound(F,x0))^4*norm(2,inverse(A-H)));
    	return(lhs < rhs, 2^kappa)
	)
    )


------------------------------
--End Multiple Roots Section--
------------------------------



certifySolutions = method()
certifySolutions(PolySystem, List) := (P, L) -> (
    regSolutions := delete( ,apply(L, i -> if certifyRegularSolution(P, i) then i));
    apply(regSolutions, i -> L = delete(i, L));
    multSolutions := delete( ,apply(L, i -> if first certifyRootMultiplicityBound(P,i) then i));
    new HashTable from {"certifiedRegularSolutions" => alphaTheoryCertification(P, regSolutions),
	 "certifiedMultipleSolutions" => multSolutions}
    )










intervalOption = method(TypicalValue => IntervalOption)
intervalOption(Option) := o -> new IntervalOption from (
    (a,b) := toSequence o;
    if not instance(b, Interval) then error "only an Interval can be substituted";
    o
    )


intervalOptionList = method(TypicalValue => IntervalOptionList)
intervalOptionList(List) := l -> new IntervalOptionList from (
    if not instance(first l, IntervalOption) then error "only an IntervalOption can be an input";
    l
    )


-- Function to define intervals
interval = method(TypicalValue => Interval)
interval (Number, Number) := (a, b) -> new Interval from (
    ai := imaginaryPart a;
    bi := imaginaryPart b;
    if ai == 0 and bi == 0 then (
	if a < b then (int := (a, b);
	    intReturn:= toList int
	    )
	else (int = (b, a);
	    intReturn = toList int
	    )
	)
    else intReturn = toList (min(a-ai*ii, b-bi*ii) + min(ai*ii, bi*ii), max(a-ai*ii, b-bi*ii) + max(ai*ii, bi*ii))
    )
-- If interval function takes only one input, the it makes an interval with width 0
interval (Number) := a -> new Interval from (
    interval (a,a)
    )
-- interval function for polynomial entries
interval (Number, RingElement) := (a, b) -> new Interval from (
    a' := sub(a, ring b);
    int := toList (a',b)
    )
interval (RingElement, Number) := (b, a) -> new Interval from (
    a' := sub(a, ring b);
    int := toList (a',b)
    )
interval (RingElement, RingElement) := (f,g) -> new Interval from (
    int := toList (f,g)
    )
interval (RingElement, Interval) := (f, i) -> new Interval from (
    f * i
    )
interval(RingElement) := i -> new Interval from (
    interval(i, i)
    ) 
-- if interval function takes Interval, then it just shows its input again. It will be needed when we do the computation between number and interval such as interval(a+I).
interval(Interval) := i -> new Interval from (
    i
    )


-- binary operators for intervals
Interval + Interval := (i1,i2) -> (
    if (class i1#0 === RingElement or class i1#1 === RingElement or i2#0 === RingElement or i2#1 === RingElement) 
    then (i1 + i2)
    else
    a := i1#0;
    b := i2#0;
    c := i1#1;
    d := i2#1;
    a' := a+b;
    b' := d+c;
    interval(a',b')
    )


Interval - Interval := (i1,i2) -> (
        if (class i1#0 === RingElement or class i1#1 === RingElement or i2#0 === RingElement or i2#1 === RingElement) 
    then (i1 - i2)
    else
        a := i1#0;
    b := i2#0;
    c := i1#1;
    d := i2#1;
    a' := a-d;
    b' := c-b;
    interval(a',b')
    )


Interval * Interval := (i1,i2) -> (
    a := i1#0;
    c := i2#0;
    b := i1#1;
    d := i2#1;
    if (length degree a =!= 0 or length degree b =!= 0 or length degree c =!= 0 or length degree d =!= 0) then (
	    A := {a*c,a*d,b*c,b*d};
	    interval(min A, max A)
	    )
    else (
	(ai,bi,ci,di) := apply((a,b,c,d), k -> imaginaryPart k);
	(ar,br,cr,dr) := apply((a,b,c,d), k -> realPart k);
	if ai == 0 and bi ==0 and ci == 0 and di == 0 then (
	    A = {a*c,a*d,b*c,b*d};
	    interval(min A, max A)
	    )
	else (
	    Ar := {ar*cr, ar*dr, br*cr, br*dr};
	    Ai := {ai*ci, ai*di, bi*ci, bi*di};
	    rePart := interval(min Ar, max Ar) - interval(min Ai, max Ai);
	    Br := {ar*ci, ar*di, br*ci, br*di};
	    Bi := {ai*cr, ai*dr, bi*cr, bi*dr};
	    imPart := interval((min Br)* ii, (max Br)* ii) + interval((min Bi)* ii, (max Bi)* ii);
	    rePart + imPart
	    )
	) 
    )
Number * Interval := (a,i1) -> (
    b:=i1#0;
    c:=i1#1;
    if a<0 then interval(a*c,a*b)
    else
    interval(a*b,a*c)
    )
RingElement * Interval := (a,i1) -> (
    interval(a,a) * i1
    )
Interval * RingElement := (i1, a) -> (
    interval(a,a) * i1
    )


Interval ^ Number := (i,a) -> (
    if a == 0 then interval(1,1) 
    else if a == 1 then i  
    else j := i ; k := 1 ; l := while k < a list j*i do (k=k+1 ; j=j*i); 
    (flatten join{{interval(1,1),i},l})#a
    )


Number ^ Interval := (a, i) -> (
    b := i#0;
    c := i#1;
    interval(a^b,a^c)
    )


Interval/Interval := (i1,i2) -> (
    if (i2#0 < 0 and 0 < i2#1) then print "division is impossible"
    else (
    a := 1/(i2#1);
    b := 1/(i2#0); 
    i2' := interval(a,b);
       i1*i2'
       )
       )









subOnMonomial = method()
subOnMonomial(Number, IntervalOption) := (f, ab) -> (
    interval(f,f)
    )
subOnMonomial(RingElement, IntervalOption) := (f, ab) -> (
    ringOff := ring f;
    (a,b) := toSequence ab;
    degreeOfVar := degree(a,f);
    if degreeOfVar == 0 then return f
    else f = sub(f, a=>1);
    f * (b^degreeOfVar)
    )   
sub(Number, IntervalOption) := (f, ab) -> (
    interval(f,f)
    )
sub(RingElement, IntervalOption) := (f, ab) -> (
    listOfTerms := terms f;
    (a,b) := toSequence ab;
    sum apply(listOfTerms, i -> interval(subOnMonomial(i, ab)))
    )   
sub(Interval, IntervalOption) := (i, ab) -> (
    i1 := sub(i#0,ab);
    i2 := sub(i#1,ab);
    interval(min(i1#0, i2#0), max(i1#1, i2#1))
    )
sub(Number, IntervalOptionList) := (f, l) -> (
    interval(f,f)
    )
sub(RingElement, IntervalOptionList) := (f, l) -> (
    last apply(l, i -> f = sub(f,i))
    )
-- substitution function for interval and interval option list
-- using above function, it changes all variables in the option list into intervals in the option list
sub(Interval, IntervalOptionList) := (f, o) -> (
    interval((sub((f)#0,o))#0,(sub((f)#1,o))#1)
    )



-- width of an interval
wInterval = method()
wInterval(Interval) := i -> (
    i#1-i#0
    )


-- midpoint of an interval
mInterval = method()
mInterval(Interval) := i -> (
    (i#0+i#1)/2
    )


-- midpoint function can be applied to a list of intervals
mInterval(List) := l -> (
    kk := apply(l, k -> mInterval(k));
    kk
    )


-- interval norm shows us the maximum element in an interval
intervalNorm = method()
intervalNorm(Interval) := i -> (
    l := max i;
    l
    )


-- the function to construct an interval matrix
-- In order to compute interval matrices, input should be the nested list of intervals such as {{[1,2],[2,3]},{[1,3],[2,4]}}
intervalMatrix = method(TypicalValue => IntervalMatrix)
intervalMatrix(List) := l -> new IntervalMatrix from (
    l
    )


-- interval matrix multiplication
IntervalMatrix * IntervalMatrix := (l, n) -> (
    numrow := length l;
    numc := length(l#0);
    numcol := length(n#0);
    mat :=  apply(apply(l, i -> (k := 0; while k < numc list ( j := 0; while j < numcol list ((i#k)*((n#k)#j)) do j = j+1)  do k=k+1)), b -> sum b);
    intervalMatrix mat
    )

-- intervalMatrixNorm computes the norm of interval matrix, an interval extension of the maximum row sum norm
intervalMatrixNorm = method()
intervalMatrixNorm(IntervalMatrix) := i -> (
    numrow := length(i);
    numcol := length(i#0);
    if class i#0#0#0 === ZZ then (
	R := QQ
	)
    else (
    	R = coefficientRing ring i#0#0#0;
    );
    if precision R =!= infinity then (
	R = R;
	listOfAbs := (l := 0; while l < numcol list sum((apply(i, j -> (k := 0; while k < numrow list abs(sub(j#k#1,R)) do k = k+1)))#l) do l = l+1);
	)
    else if R =!= QQ then (
	rationalRing := coefficientRing R;
	listOfAbs = (l = 0; while l < numcol list sum((apply(i, j -> (k := 0; while k < numrow list abs(sub(j#k#1,rationalRing)) do k = k+1)))#l) do l = l+1);
	)
    else (
	R = R;
	listOfAbs = (l = 0; while l < numcol list sum((apply(i, j -> (k := 0; while k < numrow list abs(sub(j#k#1,R)) do k = k+1)))#l) do l = l+1);
	); 
    max listOfAbs
    )



-- the function constructs an nxn interval identity matrix
-- will be used in order to compute Krawczyk operator
identityIntMat = method()
identityIntMat(ZZ) := n -> (
    lt := toList(1..n);
    intervalMatrix apply(lt, i -> for k from 1 to n list (if i == k then interval(1,1) else interval(0,0)))
    )




inverseMat = method()
inverseMat(IntervalMatrix) := m -> (
    mf := matrix applyTable(m, i -> mInterval i);
    inverse mf
    )


intervalJacMat = method()
intervalJacMat(PolySystem, IntervalOptionList) := (polySys, option) -> (
    eqsOfp := equations polySys;
    polyMapOfeqs := polySys#PolyMap;
    numOfVars := numgens ring polySys;
    R := coefficientRing(ring polySys);
    numOfGens := numgens R;
    jacOfSys := transpose jacobian transpose polyMapOfeqs;
    entriesOfJac := entries jacOfSys;
    ijm := intervalMatrix applyTable(entriesOfJac, a -> interval(sub(a, option)));
    ijm
    )


ingredientsForKoper = method(Options=>{InvertibleMatrix => null})
ingredientsForKoper(PolySystem, IntervalOptionList) := o -> (polySys, option) -> (
    eqsOfp := equations polySys;
    numOfVars := numgens ring polySys;
    ijm := intervalJacMat(polySys, option);
    midPointf := matrix applyTable(ijm, i -> mInterval i);
    midpointsOfIntervals := toList apply(option, i ->  mInterval(i#1));
    optionForPoints := toList apply(0.. length(option)-1, k -> 
	(option#k)#0 => midpointsOfIntervals#k);
    if o.InvertibleMatrix =!= null then (
	inverseMatrix := o.InvertibleMatrix
	)
    else (
	inverseMatrix = inverseMat ijm
	);
    midpointsIntoIntervals := intervalMatrix applyTable(entries inverseMatrix, a -> interval(a,a));
    z := intervalMatrix apply(option, i -> {interval(-wInterval((i#1)/2),wInterval((i#1))/2)} );
    (identityIntMat(numOfVars)-midpointsIntoIntervals*ijm, inverseMatrix)
    )





-- function to construct the Krawczyk operator
-- inputs are list of polynomials in system and n-box of intervals
krawczykOper = method(Options=>{
	InvertibleMatrix => null})
krawczykOper(PolySystem, IntervalOptionList) := o -> (polySys, option) -> (
    eqsOfp := equations polySys;
    lengthofmat := length(eqsOfp);
    y := toList apply(option, i ->  mInterval((i)#1) );
    z := intervalMatrix apply(option, i -> {interval(-wInterval((i#1)/2),wInterval((i#1))/2)} );
    oll := toList apply(0.. length(option)-1, k -> (option#k)#0 => y#k);
    matrixIngredients := ingredientsForKoper(polySys, option);
    identitysubstractmatrix := matrixIngredients#0;
    -- START constructing the (box containing the) inverse 
    if o.InvertibleMatrix =!= null then (
	my := o.InvertibleMatrix
	)
    else (
	my = matrixIngredients#1
	);
    -- substitute y values into system
    eval := matrix apply(eqsOfp, k -> {sub(k,oll)});
    -- multiplying Y matrix and f(y)
    entofmat := entries( ( (transpose matrix {take(y,lengthofmat)})-(my*eval)));
    -- computing Krawczyk operator
    (intervalMatrix apply(entofmat, i ->  {interval((i#0),(i#0))}))+(identitysubstractmatrix*z)
    )
krawczykOper(Matrix, IntervalMatrix, PolySystem, IntervalOptionList) := o -> (mat, intervalMat, polySys, option) -> (
    eqsOfp := equations polySys;
    lengthofmat := length(eqsOfp);
    y := toList apply(option, i ->  mInterval((i)#1) );
    z := intervalMatrix apply(option, i -> {interval(-wInterval((i#1)/2),wInterval((i#1))/2)} );
    oll := toList apply(0.. length(option)-1, k -> (option#k)#0 => y#k);
    -- START constructing the (box containing the) inverse 
    if o.InvertibleMatrix =!= null then (
	my := o.InvertibleMatrix
	)
    else (
	my = mat
	);
    identitysubstractMatrix := intervalMat;
    -- substitute y values into system
    eval := matrix apply(eqsOfp, k -> {sub(k,oll)});
    -- multiplying Y matrix and f(y)
    entofmat := entries( ( (transpose matrix {take(y,lengthofmat)})-(my*eval)));
    -- computing Krawczyk operator
    (intervalMatrix apply(entofmat, i ->  {interval((i#0),(i#0))}))+(identitysubstractMatrix*z)
    )



krawczykMethod = method(Options=>{
	InvertibleMatrix => null})
krawczykMethod(PolySystem, IntervalOptionList) := o -> (polySys, option) -> (
    if o.InvertibleMatrix =!= null then (
    	identitysubstractmatrix := ingredientsForKoper(polySys, option, InvertibleMatrix => o.InvertibleMatrix);
	kUnique := identitysubstractmatrix#0;
	mat := identitysubstractmatrix#1;
    	kOperator := krawczykOper(mat, kUnique, polySys, option, InvertibleMatrix => o.InvertibleMatrix);
	)
    else (
    	identitysubstractmatrix = ingredientsForKoper(polySys, option);
	kUnique = identitysubstractmatrix#0;
	mat = identitysubstractmatrix#1;
    	kOperator = krawczykOper(mat, kUnique, polySys, option);
	);
    intervalList := (apply(option, k -> k#1));
    k := 0;
    R := coefficientRing ring polySys;
    if precision R =!= infinity then (
	R = R;
    	for i from 0 to (length(option) - 1) do if (
	    realPart sub(kOperator#i#0#0, R)  < realPart intervalList#i#0 or
	    realPart sub(kOperator#i#0#1, R)  > realPart intervalList#i#1 or
	    imaginaryPart sub(kOperator#i#0#0, R)  < imaginaryPart intervalList#i#0 or 
	    imaginaryPart sub(kOperator#i#0#1, R)  > imaginaryPart intervalList#i#1
	    ) 
    	then  break k = 1;
	)
    else if R =!= QQ then (
	var := first gens R;
	rationalRing := coefficientRing R;
    	for i from 0 to (length(option) - 1) do if (
	    sub(coefficient(var,kOperator#i#0#0), rationalRing)  
	    < sub(coefficient(var, sub(intervalList#i#0, R)), rationalRing) or 
	    sub(coefficient(var,kOperator#i#0#1), rationalRing)  
	    > sub(coefficient(var, sub(intervalList#i#1, R)), rationalRing) or
	    sub(kOperator#i#0#0 - coefficient(var,kOperator#i#0#0), rationalRing) 
	    < sub(intervalList#i#0 - var * coefficient(var,sub(intervalList#i#0, R)), rationalRing) or
	    sub(kOperator#i#0#1 - coefficient(var,kOperator#i#0#1), rationalRing) 
	    > sub(intervalList#i#1 - var * coefficient(var,sub(intervalList#i#1, R)), rationalRing)
	    ) 
    	then  break k = 1;
	)
    else (
	R = R;
    	for i from 0 to (length(option) - 1) do if (
	    sub(kOperator#i#0#0, R)  < intervalList#i#0 or
	    sub(kOperator#i#0#1, R)  > intervalList#i#1 
	    ) 
    	then  break k = 1;
	); 
    if k === 0 then ( if o.InvertibleMatrix =!= null then (
	    if class R === ComplexField or class R === QuotientRing and 2 * (intervalMatrixNorm(kUnique))^2 < 1 then (
		    print "given interval contains a unique solution"; 
			true
    	    	    	)
		    else if intervalMatrixNorm(kUnique) < 1 then (
		        print "given interval contains a unique solution"; 
			true
			)
		    else (
			print "Uniqueness fail";
			false
			)
		    )
		else if class R === ComplexField or class R === QuotientRing and 2 * (intervalMatrixNorm(kUnique))^2 < 1 then (
      		        print "given interval contains a unique solution"; 
			true
    	    	    	)
		    else if intervalMatrixNorm(kUnique) < 1 then (
		    print "given interval contains a unique solution"; 
		    true
		    )
		else (
		    print "Uniqueness fail";
		    false
		    )
		)
	    else (
		print "Existence fail";
		false
		)
	    )

TEST ///
R = RR[x1,x2,y1,y2]
f = polySystem {3*y1 + 2*y2 -1, 3*x1 + 2*x2 -3.5,x1^2 + y1^2 -1, x2^2 + y2^2 - 1}
I1 = interval(.90,.96)
I2 = interval(.31,.33)
I3 = interval(-.33,-.27)
I4 = interval(.9,1)
o = intervalOptionList apply({x1 => I1, x2 => I2, y1 => I3, y2 => I4}, i -> intervalOption i)
krawczykMethod(f,o)
///




beginDocumentation()
load ("./NumericalCertification/doc.m2")
end





restart
check "NumericalCertification"
uninstallAllPackages()
installPackage "NumericalCertification"
debug needsPackage("NumericalCertification", Configuration => {"ALPHACERTIFIEDexec" => "~/alphaCertifiedLinux64/"})
needsPackage("NumericalCertification", Configuration => {"ALPHACERTIFIEDexec" => "~/alphaCertifiedLinux64/"})
viewHelp NumericalCertification


restart
installPackage "NumericalCertification"
viewHelp NumericalCertification
