export {"eco"}

eco = method(Options => {CoefficientRing => ZZ/32003, MonomialOrder => GRevLex})
eco ZZ := Ideal => opts -> n -> (
    R := (opts.CoefficientRing)[vars(0..n-1), MonomialOrder => opts.MonomialOrder];
    F := toList apply(0..n-2, k -> R_(n-1) * (R_k + sum(0..n-k-3, i -> R_i * R_(i+k+1))) - k - 1)
         | {sum(0..n-2, i -> R_i) + 1};
    ideal F
    )

beginDocumentation()

doc /// 
    Key
    	eco
	(eco, ZZ)
    Headline
        an economics problem
    Usage
    	eco n
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
	    eco 8
    ///
