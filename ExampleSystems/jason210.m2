export {"jason210"}

jason210 = method(Options => {CoefficientRing => ZZ/32003, MonomialOrder => GRevLex})
installMethod(jason210, Ideal => opts -> () -> (
    R := (opts.CoefficientRing)[vars(0..7), MonomialOrder => opts.MonomialOrder];
    ideal "a6,
           b6,
           a2c4+b2d4+abc2e2+abd2f2+abcdeg+abcdfh"
    ))

beginDocumentation()

doc /// 
    Key
    	jason210
    Headline
    	the jason210 ideal
    Usage
    	jason210()
    Outputs
    	:Ideal
	    the ideal of the system
    Description
    	Text
	    Reference: http://www.broune.com/papers/issac2012.html
	Example
	    jason210()
    ///
