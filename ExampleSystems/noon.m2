export {"noon"}

noon = method(Options => {CoefficientRing => ZZ/32003, MonomialOrder => GRevLex})
noon ZZ := Ideal => opts -> n -> (
    R := (opts.CoefficientRing)[vars(0..n-1), MonomialOrder => opts.MonomialOrder];
    F := apply(0..n-1, i -> 10 * R_i * (sum(0..n-1, j -> R_j^2) - R_i^2) - 11 * R_i + 10);
    ideal F
    )

beginDocumentation()

doc /// 
    Key
    	noon
	(noon, ZZ)
    Headline
    	a neural network model
    Usage
    	noon n
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
	    noon 5
    ///
