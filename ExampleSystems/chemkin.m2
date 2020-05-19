export {"chemkin"}

chemkin = method(Options => {CoefficientRing => ZZ/32003, MonomialOrder => GRevLex})
installMethod(chemkin, Ideal => opts -> () -> (
    R := (opts.CoefficientRing)[vars(0..10), MonomialOrder => opts.MonomialOrder];
    ideal "-4ad+9d2+h,
           b2+e2+i2-1,
	   c2+f2+j2-1,
	   9g2+9k2-8,
	   -6abd+3b+3de+3hi-1,
	   3bc+3ef+3ij-1,
	   c+3fg+3jk-1,
	   -6a+3b+3c+8,
	   9d+9e+9f+9g+8,
	   h+i+j+k,
	   a2-2"
    ))

beginDocumentation()

doc /// 
    Key
        chemkin
    Headline
        a chemical kinematics problem
    Usage
    	chemkin()
    Outputs
    	:Ideal
	    the ideal of the system
    Description
    	Text
	    Reference: http://invo.jinr.ru/examples.phtml
	Example
	    chemkin()
    ///
