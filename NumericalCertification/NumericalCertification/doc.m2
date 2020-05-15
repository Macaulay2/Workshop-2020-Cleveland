-- Documents for Numerical Certification.



-- These are methods/functions only used as a mechanism. (will not be used by users)
undocumented{(inverseMat, IntervalMatrix), (net, Interval),
    (substitute, Interval, IntervalOptionList), (substitute, Interval, IntervalOption),
    (substitute, RingElement, IntervalOptionList), (substitute, Number, IntervalOption),
    (substitute, Number, IntervalOptionList), (substitute, RingElement, IntervalOption),
    (krawczykOper, Matrix, IntervalMatrix, PolySystem, IntervalOptionList),
    ingredientsForKoper, (ingredientsForKoper, PolySystem, IntervalOptionList),
    intervalJacMat, (intervalJacMat, PolySystem, IntervalOptionList), inverseMat,
    sqabsForGaussianRational, (sqabsForGaussianRational, RingElement),
    conjugateGaussian, (conjugateGaussian, RingElement),
    conjugateGaussianRationalMatrix, (conjugateGaussianRationalMatrix, Matrix),
    subOnMonomial, (subOnMonomial, Number, IntervalOption), (subOnMonomial,RingElement, IntervalOption)}


-- These are already documented as methods.
undocumented{mInterval, wInterval, intervalNorm} 



-- These interval arithmetic methods are documented in the documents of its classes.
undocumented{(symbol +, Interval, Interval), (symbol *, Interval, RingElement), 
    (symbol *, Interval, Interval), (symbol *, RingElement, Interval),
    (symbol *, Number, Interval), (symbol ^, Interval, Number),
    (symbol ^, Number, Interval), (symbol *, IntervalMatrix, IntervalMatrix),
    (symbol -, Interval, Interval), (symbol /, Interval, Interval)}



doc ///
    	Key
	    	NumericalCertification
	Headline
	    	certify a numerical solution for a square system
	Description
	    	Text
		    	This package provides symbolic-numeric approaches to certify roots for a square polynomial system.
			
			For regular roots, the package has two different approaches.
		      	The first is Smale's alpha theory and the second is Krawczyk method via interval arithmetic.
			Both methods are based on Newton's method and they all describe the specific region containing a unique root of the system.
			
			In the case of alpha theory, this package follows the algorithms of alpha theory established in @HREF("https://arxiv.org/abs/1011.1091","\"alphaCertified: certifying solutions to polynomial systems\" (2012)")@.
			In the case of Krawczyk method, this package follows the theory introduced in @HREF("https://epubs.siam.org/doi/book/10.1137/1.9780898717716","\"Introduction to Interval Analysis\" (2009)")@. 
			These two methods also support not only floating-point arithmetic over the real and complex numbers, but also the exact computation with inputs of rational numbers.
			
			Moreover, the package has a function certifying regular roots via a software 'alphaCertified' @HREF("https://www.math.tamu.edu/~sottile/research/stories/alphaCertified/")@.
			
			For multiple roots, the concept of a local separation bound for a simple multiple root established in @HREF("https://arxiv.org/abs/1904.07937")@ is implemented. 
			The package checks if a given numerical approximation is a simple multiple root with its lower bound of the multiplicity and a region containing the root.
			
			
			
			    
		Text
		    	{\bf Regular Root Ceritification Methods:}
			
			    $\bullet$ @TO "certifyRegularSolution"@
			    
			    $\bullet$ @TO "krawczykMethod"@
			    
			{\bf Examples}
			
		            The following example shows how to certify the roots of solutions for the square polynomial system.
			    This example is suggested in @HREF("https://www3.nd.edu/~jhauenst/preprints/hlPolyExp.pdf", 
				"\"Certifying solutions to square systems of polynomial-exponential equations\" (2017)")@
			    
			    
			{\bf    $\bullet$ alpha theory}    
		Text
		    A set of points for certification should be given in advance using other system solvers.
		Example
		    R = RR[x1,x2,y1,y2];
		    f = polySystem {3*y1 + 2*y2 -1, 3*x1 + 2*x2 -3.5, x1^2 + y1^2 -1, x2^2 + y2^2 -1};
		    p1 = point{{.95, .32, -.30, .95}};
		    p2 = point{{.9, .3, -.3, 1}}; -- poorly approximated solution
		Text
		    It shows the results of the certification.
		Example
		    certifyRegularSolution(f,p1)
		    certifyRegularSolution(f,p2) -- not an approximate solution
		    
		Text
		    Also, if we have other solutions of the system, alpha theory suggests an algorithm for distinguishing these solutions.
		Example
		    p1 = point{{.95,.32,-.30,.95}};
		    p2 = point{{.65,.77,.76,-.64}};
		    certifyDistinctSolutions(f,p1,p2)
		Text
		    In the case of real polynomial system, we can certify that a given solution is real or not.
		Example
		    p = point{{.954379, .318431, -.298633, .947949}};
		    certifyRealSolution(f,p)
		
		Text
		    {\bf    $\bullet$ Krawczyk method}
		Text
		    Intervals for certification should be given in advance using other system solvers.
		Example
		    R = RR[x1,x2,y1,y2];
		    f = polySystem {3*y1 + 2*y2 -1, 3*x1 + 2*x2 -3.5, x1^2 + y1^2 -1, x2^2 + y2^2 -1};
		    (I1, I2, I3, I4) = (interval(.94,.96), interval(.31,.33), interval(-.31,-.29), interval(.94,.96));
		Text
		    We set the relationships between variables and intervals using the function @TO "intervalOptionList"@.
		Example
		    o = intervalOptionList apply({x1 => I1, x2 => I2, y1 => I3, y2 => I4}, i -> intervalOption i);
    	    	    krawczykOper(f,o)
		Text
		    The function @TO "krawczykMethod"@ automatically checks whether the Krawczyk operator is contained in the input interval box.
		Example
		    krawczykMethod(f,o)
		

		Text
		    	{\bf Multiple Root Ceritification Method:}

			    
			    $\bullet$ @TO "certifyRootMultiplicityBound"@

		
///




	       
	       
doc ///
    	Key
    	    computeConstants
	    (computeConstants, PolySystem, Point)
	    "(computeConstants, PolySystem, Point)"
	Headline
	    compute the square of the auxilary quantities related to alpha theory
	Usage
	    (alpha, beta, gamma) = computeConstants(PS, P)
	Inputs
            PS:PolySystem
	    P:Point
	Description
	    Text
    	    	alpha theory uses three auxilary quantities related to the input polynomial system and point.

		Beta value is defined by the length of the Newton step and gamma value is the quantity which is inversely propotional to the length between exact solution and the given point.

		Alpha value is defined by the multiplication of beta and gamma. When it is smaller than  $0.157671$, then the input point is an approximate solution to the system. The function @TO "certifyRegularSolution"@ does this process.
	    Example
	        R = RR[x1,x2,y1,y2];
		f = polySystem {3*y1 + 2*y2 -1, 3*x1 + 2*x2 -3.5,x1^2 + y1^2 -1, x2^2 + y2^2 - 1};
		p = point{{.95,.32,-.30,.95}};
    	    	(a, b, g) = computeConstants(f,p)
///		


	       
doc ///
    	Key
    	    certifyRegularSolution
	    (certifyRegularSolution, PolySystem, Point)
	    (certifyRegularSolution, PolySystem, Matrix)
	    (certifyRegularSolution, PolySystem, List)
	    "(certifyRegularSolution, PolySystem, Point)"
	    "(certifyRegularSolution, PolySystem, Matrix)"
	    "(certifyRegularSolution, PolySystem, List)"
	Headline
	    certify whether a given point is an approximate solution to the system
	Usage
	    alpha = certifyRegularSolution(PS, P)
	Inputs
            PS:PolySystem
	    P:Point
	Description
	    Text
    	    	This function executes the alpha test based on the value computed by @TO "computeConstants"@.
	    Example
	        R = RR[x1,x2,y1,y2];
		f = polySystem {3*y1 + 2*y2 -1, 3*x1 + 2*x2 -3.5,x1^2 + y1^2 -1, x2^2 + y2^2 - 1};
	    Text
	    	Input can be a @TO "Point"@ or @TO "Matrix"@ representing coordinates or a list of points or matrices.
	    Example
		p1 = point{{.95,.32,-.30,.95}};
    	    	certifyRegularSolution(f,p1)
		p2 = point{{.65,.77,.76,-.64}};
    	    	certifyRegularSolution(f, {p1,p2})
///		



doc ///
    	Key
    	    certifyDistinctSolutions
	    (certifyDistinctSolutions, PolySystem, Point, Point)
	    "(certifyDistinctSolutions, PolySystem, Point, Point)"
	Headline
	    determine whether given points are distinct approximate solutions to the system
	Usage
	    certifyDistinctSolutions(PS, P1, P2)
	Inputs
            PS:PolySystem
	    P1:Point
	    P2:Point
	Description
	    Text
    	    	This function executes the gamma test based on the value computed by @TO "computeConstants"@, and determine whether given points are distinct or not.
	    Example
	        R = RR[x1,x2,y1,y2];
		f = polySystem {3*y1 + 2*y2 -1, 3*x1 + 2*x2 -3.5,x1^2 + y1^2 -1, x2^2 + y2^2 - 1};
		p1 = point{{.95,.32,-.30,.95}};
		p2 = point{{.65,.77,.76,-.64}};
    	    	certifyDistinctSolutions(f,p1,p2)
	    Text
	    	However, if two solutions are too close, it concludes that inputs are not disticnt.
	    Example
		p1 = point{{.6525,.7712,.7577,-.6366}};
		p2 = point{{.653,.771,.758,-.637}};
    	    	certifyDistinctSolutions(f,p1,p2)
	    Text
	    	Even worse, if two solutions are close enough and both have alpha value which are bigger than $0.03$, it gives indecisive comments.
		
		In this case, user should apply @TO "newtonOper"@ to the point to get more precise approximation.
	    Example
		p1 = point{{.95,.32,-.30,.95}};
		p2 = point{{.95,.32,-.301,.95}};
    	    	certifyDistinctSolutions(f,p1,p2)
///		



doc ///
    	Key
    	    certifyRealSolution
	    (certifyRealSolution, PolySystem, Point)
	    "(certifyRealSolution, PolySystem, Point)"
	Headline
	    determine whether a given point is an real approximate solution to the system
	Usage
	    certifyRealSolution(PS, P)
	Inputs
            PS:PolySystem
	    P:Point
	Description
	    Text
    	    	When the system is real (or rational) polynomial system, this function executes the gamma test based on the value computed by @TO "computeConstants"@, and determine whether a given point is a real approximate solution  or not.
	    Example
	        R = RR[x1,x2,y1,y2];
		f = polySystem {3*y1 + 2*y2 -1, 3*x1 + 2*x2 -3.5,x1^2 + y1^2 -1, x2^2 + y2^2 - 1};
		p = point{{.954379,.318431,-.298633,.947949}};
    	    	certifyRealSolution(f,p)
	    Text
	    	However, an input point is poorly approximated, it gives false even if the point is real.
		In this case, user should apply @TO "newtonOper"@ to the point to get more precise approximation.
	    Example
		p = point{{.65,.77,.75,-.64}};  -- poorly approximated solution
    	    	certifyRealSolution(f,p)
///		



doc ///
    	Key
    	    alphaTheoryCertification
	    (alphaTheoryCertification, PolySystem, List)
	    "(alphaTheoryCertification, PolySystem, List)"
	Headline
    	    executes alpha-certification on a given system and list of points
	Usage
	    (D, R, CS, C) = alphaTheoryCertification(PS, P)
	Inputs
            PS:PolySystem
	    P:Point
	Outputs
	    D:List
	    	a list of certified distinct solutions
	    R:List
	    	a list of certified real solutions
	    CS:List
	    	a list of certified solutions
	    C:List
	    	a list of constants for certified solutions
	Description
	    Text
	    	When the system solved by solver has lots of points, this function does all procedures of @TO "certifyRegularSolution"@, @TO "certifyDistinctSolutions"@ and @TO "certifyRealSolution"@ at once.
	    Example
	        R = RR[x1,x2,y1,y2];
		f = polySystem {3*y1 + 2*y2 -1, 3*x1 + 2*x2 -3.5,x1^2 + y1^2 -1, x2^2 + y2^2 - 1};
		p1 = point{{.954379,.318431,-.298633,.947949}}; p2 = point{{.95, .32, -.30, .95}}; p3 = point{{.652567, .77115, .757776, -.636663}}; p4 = point{{.65, .77, .76, -.64}}; 
		p5 = point{{.31, .30, .72, -.60}}; -- poorly approximated solution
		P = {p1, p2, p3, p4, p5}
    	        alphaTheoryCertification(f,P)
///		




doc ///
    	Key
	    Interval
	Headline
	    a class of all intervals
	Description
	    Text
	    	This type is a new type of @TO "List"@. The function @TO "interval"@ can be used to access an @TO "Interval"@.
	    Example
	    	I = interval(.5,.8)
	    Text	
	    	Users can make an interval which has polynomials as entries.
	    Example
	    	R = RR[x];
		J = interval(5,3*x)
	    Text
	    	@TO "NumericalCertification"@ supports some basic interval arithmetics.
	    Example
	    	I1 = interval(.5,.8);
		I2 = interval(.6,.9);
		I1 + I2
		I1 - I2
		I1 * I2
		I1 / I2
		I1 ^ 3
	    Text
	        Also, @TO "Interval"@ can be defined for complex number inputs.
	    Example
	    	I1 = interval(3-ii, 2+2*ii)
		I2 = interval(-1+3*ii, 1+ii)
	    Text
	    	We define the multiplication of complex-valued intervals as : 
		$([a_1,b_1]+i[c_1,d_1])([a_2,b_2]+i[c_2,d_2])=([a_1,b_1][a_2,b_2]-[c_1,d_1][c_2,d_2])+i([a_1,b_1][c_2,d_2]+[a_2,b_2][c_1,d_1])$. 
	    Example
		I1 * I2

///

doc ///
    	Key
	    IntervalMatrix
	Headline
	    a class of all interval matrices
	Description
	    Text
	    	This type is a new type of @TO "List"@, and it works as a matrix with @TO "interval"@ entries.
    	    	
		The function @TO "intervalMatrix"@ can be used to access this type.
	    Example
	    	m = intervalMatrix {{interval(1,2), interval(2,3)},{interval(3,4),interval(1,3)}}
	    Text
	    	@TO "NumericalCertification"@ supports the multiplication of interval matrices.
	    Example
	    	n = intervalMatrix {{interval(1,2), interval(.2,.5)},{interval(2,3),interval(-2,-1)}};
		m*n
///



doc ///
    	Key
	    IntervalOption
	Headline
	    a class of an option assigning an interval to a variable
	Description
	    Text
	    	This type is a new type of @TO "Option"@, and it works when @TO "krawczykOper"@ and @TO "krawczykMethod"@ assign an interval to a variable in a function.

		The function @TO "intervalOption"@ should be used to convert a @TO "Option"@ type object into @TO "IntervalOption"@.
	    Example
                R = RR[x];
		I = interval(.94,.96);
    	    	intervalOption(x => I)
///


doc ///
    	Key
	    IntervalOptionList
	Headline
	    a class of lists for options related to intervals
	Description
	    Text
	    	This type is a new type of @TO "List"@, and it works when @TO "krawczykOper"@ and @TO "krawczykMethod"@ assign intervals to variables in the system.
		
		@TO "krawczykOper"@ substitute given intervals into variables in the system as the way @TO "IntervalOptionList"@ suggests.
    	    	
    	    	@TO "krawczykOper"@ and @TO "krawczykMethod"@ doesn't work with @TO "List"@ type input. Thus, users should change the list of options into @TO "IntervalOptionList"@.
		
		The function @TO "intervalOptionList"@ can be used to convert a @TO "List"@ type object into @TO "IntervalOptionList"@.
	    Example
                R = RR[x1,x2,y1,y2];
		f = polySystem {3*y1 + 2*y2 -1, 3*x1 + 2*x2 -3.5, x1^2 + y1^2 -1, x2^2 + y2^2 -1};
		(I1, I2, I3, I4) = (interval(.94,.96), interval(.31,.33), interval(-.31,-.29), interval(.94,.96));
	       	intervalOptionList {intervalOption(x1 => I1), intervalOption(x2 => I2), intervalOption(y1 => I3), intervalOption(y2 => I4)}
///

		

doc ///
    	Key
	    interval
	    (interval, Number, Number)
	    (interval, Number, RingElement)
	    (interval, RingElement, Number)
	    (interval, RingElement, RingElement)
	    (interval, RingElement, Interval)
	    (interval, Interval)
	Headline
	    construct an interval
	Description
	    Text
	        This function is used to access a type @TO "Interval"@.
	    Example
	    	J = interval(3)
	        I = interval(.5,.8)
	    Text	
	    	Users can make an interval which has polynomials as entries.
	    Example
	    	R = RR[x];
		J = interval(5,3*x)
    	    Text
	    	The type @TO "Interval"@ can also be an input for the @TO "interval"@.
	    Example
	        I = interval(.5,.8)
	    	J = interval I
///


doc ///
    	Key
	    intervalMatrix
	    (intervalMatrix, List)
	Headline
	    construct an interval matrix from the given list
	Description
	    Text
	        This function is used to access a type @TO "IntervalMatrix"@ from the @TO "List"@.
	    Example
	    	l = {{interval(1,2), interval(2,3)},{interval(3,4),interval(1,3)}}
	    	m = intervalMatrix l
///



doc ///
    	Key
	    intervalOption
	    (intervalOption, Option)
	Headline
	    convert an Option to an IntervalOption
	Description
	    Text
	    	This function converts an @TO "Option"@ to an @TO "IntervalOption"@ type object.

    	    	First, assume that we have the following ring and interval. 
	    Example
                R = RR[x];
		I = interval(.94,.96);
    	    Text
	    	We want to plug in "I" into "x".
		
		Then, write an @TO "Option"@ object as the way we want.
	    Example
    	    	option = x => I
	    Text
	    	Then, use @TO "intervalOption"@ function to convert the type of "option" to @TO "IntervalOption"@.
	    Example
	       	intervalOption option 
///



doc ///
    	Key
	    intervalOptionList
	    (intervalOptionList, List)
	Headline
	    convert a list of IntervalOption to list of options for intervals
	Description
	    Text
	    	This function converts a @TO "List"@ of @TO "IntervalOption"@ to a @TO "IntervalOptionList"@ type object.

    	    	First, assume that we have the following ring, polynomial system, and interval. 
	    Example
                R = RR[x1,x2,y1,y2];
		f = polySystem {3*y1 + 2*y2 -1, 3*x1 + 2*x2 -3.5, x1^2 + y1^2 -1, x2^2 + y2^2 -1};
		(I1, I2, I3, I4) = (interval(.94,.96), interval(.31,.33), interval(-.31,-.29), interval(.94,.96));
    	    Text
	    	We want to plug in "I1" into "x1", "I2" into "x2", "I3" into "y1" and "I4" into "y2".
		
		Then, write a @TO "List"@ object as the way we want.
	    Example
    	    	l = {intervalOption(x1 => I1), intervalOption(x2 => I2), intervalOption(y1 => I3), intervalOption(y2 => I4)}
	    Text
	    	Then, use @TO "intervalOptionList"@ function to convert the type of "l" to @TO "IntervalOptionList"@.
	    Example
	       	intervalOptionList l 
///


	    
	    
	    
doc ///
    	Key
	    krawczykMethodOptions
	    InvertibleMatrix
	    [krawczykOper, InvertibleMatrix]
	    [krawczykMethod, InvertibleMatrix]
      	Headline
	    invertible matrix for computing Krawczyk operator (option for "krawczykOper" and "krawczykMethod")
	Description
	    Example
	    	options krawczykMethod
	    Text
	    	This is an option for @TO "krawczykOper"@ and @TO "krawczykMethod"@. By default, these functions uses the inverse of the matrix obtained by evaluating the system at the midpoint of the input interval.
       	       	
		Input for this option have to be an invertible matrix.
	    Example
	    	R = RR[x1,x2,y1,y2];
		f = polySystem {3*y1 + 2*y2 -1, 3*x1 + 2*x2 - 3.5,x1^2 + y1^2 -1, x2^2 + y2^2 - 1};
	        (I1, I2, I3, I4) = (interval(.94,.96), interval(.31,.33), interval(-.31,-.29), interval(.94,.96));
		o = intervalOptionList apply({x1 => I1, x2 => I2, y1 => I3, y2 => I4}, i -> intervalOption i);
		Y = matrix {{.095, .032, .476, -.100},{-.143, .452, -.714, .150},{.301,.101,-.160, -.317},{.048,-.152,.240,.476}};
    	    	krawczykMethod(f,o,InvertibleMatrix => Y)		
///    

doc ///
    	Key
	    krawczykOper
	    (krawczykOper, PolySystem, IntervalOptionList)
	Headline
	    compute the Krawczyk operator
	Description
	    Text
	    	For given interval and polynomial system, this function computes the Krawczyk operator.
	    Example
	    	R = RR[x1,x2,y1,y2];
		f = polySystem {3*y1 + 2*y2 -1, 3*x1 + 2*x2 -3.5,x1^2 + y1^2 -1, x2^2 + y2^2 - 1};
	        (I1, I2, I3, I4) = (interval(.94,.96), interval(.31,.33), interval(-.31,-.29), interval(.94,.96));
	    Text
	        Intervals for certification should be given in advance using other system solvers.
	        After that we set the relationships between variables and intervals.
	    Example
		o = intervalOptionList apply({x1 => I1, x2 => I2, y1 => I3, y2 => I4}, i -> intervalOption i);
    	    Text
	    	If the Krawczyk operator is contained in the input interval, then we conclude that the input interval (or the Krawczyk operator) contains a unique root of the system.
	    Example
    	    	krawczykOper(f,o)
    	    Text
		The function @TO "krawczykMethod"@ checks this criterion automatically.

    	        By default, these functions uses the inverse of the matrix obtained by evaluating the system at the midpoint of the input interval.
		
		However, users can choose an invertible matrix by themselves. (See @TO "InvertibleMatrix"@.)
	    Example
	    	Y = matrix {{.095, .032, .476, -.100},{-.143, .452, -.714, .150},{.301,.101,-.160, -.317},{.048,-.152,.240,.476}};
    	    	krawczykOper(f,o,InvertibleMatrix => Y)	
		
///


doc ///
    	Key
	    krawczykMethod
	    (krawczykMethod, PolySystem, IntervalOptionList)
	Headline
	    certify the interval box for square polynomial system
	Description
	    Text
	    	For given interval and polynomial system, this function computes the Krawczyk operator and check that the operator is contained in the input interval.
	    Example
	    	R = RR[x1,x2,y1,y2];
		f = polySystem {3*y1 + 2*y2 -1, 3*x1 + 2*x2 -3.5,x1^2 + y1^2 -1, x2^2 + y2^2 - 1};
	        (I1, I2, I3, I4) = (interval(.94,.96), interval(.31,.33), interval(-.31,-.29), interval(.94,.96));
	    Text
	        Intervals for certification should be given in advance using other system solvers.
	        After that we set the relationships between variables and intervals.
	    Example
		o = intervalOptionList apply({x1 => I1, x2 => I2, y1 => I3, y2 => I4}, i -> intervalOption i);
	    Text
	    	If the Krawczyk operator is contained in the input interval, then the function returns the result that the input interval (or the Krawczyk operator) contains a unique root of the system.
	    Example
    	    	krawczykMethod(f,o)
    	    Text
    	        By default, these functions uses the inverse of the matrix obtained by evaluating the system at the midpoint of the input interval.
		
		However, users can choose an invertible matrix by themselves. (See @TO "InvertibleMatrix"@.)
	    Example
	    	Y = matrix {{.095, .032, .476, -.100},{-.143, .452, -.714, .150},{.301,.101,-.160, -.317},{.048,-.152,.240,.476}};
    	    	krawczykMethod(f,o,InvertibleMatrix => Y)	
		

		
///



