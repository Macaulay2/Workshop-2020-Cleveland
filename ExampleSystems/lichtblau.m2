export {"lichtblau"}

lichtblau = method(Options => {CoefficientRing => ZZ/32003, MonomialOrder => GRevLex})
installMethod(lichtblau, Ideal => opts -> () -> (
    R := (opts.CoefficientRing)[vars(0..2), MonomialOrder => opts.MonomialOrder];
    ideal "b-110a2+495a3-1320a4+2772a5-5082a6+7590a7-8085a8+5555a9-2189a10+374a11,
           c-22a+110a2-330a3+1848a5-3696a6+3300a7-1650a8+550a9-88a10-22a11"
    ))

beginDocumentation()

doc /// 
    Key
    	lichtblau
    Headline
    	the lichtblau system
    Usage
    	lichtblau()
    Outputs
    	:Ideal
	    the ideal of the system
    Description
    	Text
	    Reference: https://github.com/ederc/singular-benchmarks
	Example
	    lichtblau()
    ///
