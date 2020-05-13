export{"sendra"}

sendra = method()
sendra (Ring) := kk -> (
	(x,y) := (symbol x, symbol y);
	R := kk[x,y];
	{ -270*x^4*y^3-314*x*y^4-689*x*y^3+1428,
	36*x^7+417*x^6*y-422*x^5*y^2-270*x^4*y^3+1428*x^3*y^4-1475*x^2*y^5+510*x*y^6-200*x^6-174*x^5*y-966*x^4*y^2+529*x^3*y^3+269*x^2*y^4+49*x*y^5-267*y^6+529*x^4*y+1303*x^2*y^3-314*x*y^4+262*y^5+36*x^4-788*x^2*y^2-689*x*y^3+177*y^4 } )

beginDocumentation()

doc /// 
    Key
    	sendra
	(sendra,Ring)
    Headline
    	the system sendra
    Usage
	sendra(kk)
    Inputs
	kk:Ring
		the coefficient ring
    Outputs
	:List
		of polynomials in the system
    Description
    	Text
	    The Bezout bound is 49. 
	    
	    Reference: PoSSo test suite.
	    
	    See also: http://homepages.math.uic.edu/~jan/Demo/sendra.html.
	Example
	    F = sendra(QQ)
	    time sols = solveSystem F;
	    #sols
    ///
