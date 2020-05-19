export {"commats"}

commats = method(Options => {CoefficientRing => ZZ/32003, MonomialOrder => GRevLex})
commats ZZ := Ideal => opts -> n -> (
    R := (opts.CoefficientRing)(monoid[vars(0..2*n*n-1), MonomialOrder => opts.MonomialOrder]);
    A := genericMatrix(R, R_0, n, n);
    B := genericMatrix(R, R_(n*n), n, n);
    ideal flatten entries (A*B - B*A)
    )

beginDocumentation()

doc /// 
    Key
    	commats
	(commats, ZZ)
    Headline
    	the ideal formed by commuting square matrices
    Usage
    	commats n
    Inputs
    	n:ZZ
	    the size of the matrices
    Outputs
    	:Ideal
	    of the ideal of the system
    Description
    	Text
	    The equations are the conditions under which two generic matrices will commute.
	Example
	    commats 4
    ///
