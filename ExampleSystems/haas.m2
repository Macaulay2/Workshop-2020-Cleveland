export {"haas"}

haas = method(Options => {CoefficientRing => ZZ/32003, MonomialOrder => GRevLex})
installMethod(haas, Ideal => opts -> () -> (
    R := (opts.CoefficientRing)[vars(0..3), MonomialOrder => opts.MonomialOrder];
    ideal"b8+dc4-c,
          c8+ab4-b,
	  64b7c7-16b3c3da+4c3d+4b3a-1"
    ))

beginDocumentation()

doc /// 
    Key
        haas
    Headline
    	the haas system
    Usage
    	haas()
    Outputs
    	:Ideal	
	    the ideal of the system
    Description
    	Text
	    Reference: Hashemi, Efficient algorithms for computing Noether normalization
	Example
	    haas()
    ///
