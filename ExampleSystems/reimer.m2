export {"reimer"}

reimer = method(Options => {CoefficientRing => ZZ/32003, MonomialOrder => GRevLex})
reimer ZZ := Ideal => opts -> n -> (
    R := (opts.CoefficientRing)[vars(0..n-1), MonomialOrder => opts.MonomialOrder];
    F := apply(2..n+1, d -> sum(0..n-1, i -> (-1)^i * 2 * R_i^d) - 1);
    ideal F
    )

beginDocumentation()

doc /// 
    Key
    	reimer
	(reimer, ZZ)
    Headline
    	the Reimer system
    Usage
    	reimer n
    Inputs
    	n:ZZ
	    the number of variables
    Outputs
    	:Ideal
	    the ideal of the system
    Description
    	Text
	    Reference: http://invo.jinr.ru/examples.phtml
	Example
	    reimer 5
    ///
