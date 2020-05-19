export {"kotsireas"}

kotsireas = method(Options => {CoefficientRing => ZZ/32003, MonomialOrder => GRevLex})
installMethod(kotsireas, Ideal => opts -> () -> (
    R := (opts.CoefficientRing)[vars(0..6), MonomialOrder => opts.MonomialOrder];
    ideal "ba-bd-ae+ed-2f+2,
           ba+bd-2bf-ae-2a-ed+2ef+2d,
           b2-2be-2b+e2-2e+g+1,
           b3a2-1,
           e3d2-1,
           g3f2-1"
    ))

beginDocumentation()

doc ///
    Key
    	kotsireas
    Headline
    	the kotsireas system
    Usage
    	kotsireas
    Outputs
    	:Ideal
	    the ideal of the system
    Description
    	Text
	    Reference: http://invo.jinr.ru/examples.phtml
	Example
	    kotsireas()
    ///
