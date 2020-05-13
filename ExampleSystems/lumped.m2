export{"lumped"}

lumped = method()
lumped (Ring) := kk -> (
    x := symbol x;
    R := kk[x_1..x_4];
   { ( 7.67718790000000E-01 + 3.28202780000000E-01*i)*x_1*x_3+( 7.67718790000000E-01 + 3.28202780000000E-01*i)*x_1*x_4
       +(-1.76771879000000E+00 - 3.28202780000000E-01*i)*x_1+( 5.48909490000000E-01 + 1.09394900000000E-01*i)*x_3
       +( 4.79608000000000E-02 + 8.88686780000000E-01*i),
       ( 3.30100210000000E-01 + 8.90584170000000E-01*i)*x_2*x_3
       +( 3.30100210000000E-01 + 8.90584170000000E-01*i)*x_2*x_4
       +(-1.33010021000000E+00 - 8.90584170000000E-01*i)*x_2
       +( 1.11290920000000E-01 + 6.71774920000000E-01*i)*x_4
       +( 8.29151510000000E-01 + 6.69877470000000E-01*i),
       (-7.67718790000000E-01 - 3.28202780000000E-01*i)*x_1*x_3
       +(-7.67718790000000E-01 - 3.28202780000000E-01*i)*x_1*x_4
       +(-8.92481630000000E-01 - 4.52965620000000E-01*i)*x_3*x_4
       +( 7.67718790000000E-01 + 3.28202780000000E-01*i)*x_1
       +(-5.48909490000000E-01 - 1.09394900000000E-01*i)*x_3,
       (-3.30100210000000E-01 - 8.90584170000000E-01*i)*x_2*x_3
       +(-3.30100210000000E-01 - 8.90584170000000E-01*i)*x_2*x_4
       +(-8.92481630000000E-01 - 4.52965620000000E-01*i)*x_3*x_4
       +( 3.30100210000000E-01 + 8.90584170000000E-01*i)*x_2
       +(-1.11290920000000E-01 - 6.71774920000000E-01*i)*x_4
        }
 )

   beginDocumentation()

doc /// 
    Key
    	lumped
	(lumped,Ring)
    Headline
    	lumped parameter chemically reacting system
    Usage
    	lumped(kk)
    Inputs
    	kk:Ring
            the coefficient ring
    Outputs
    	:List
            of solutions
    Description
    	Text
	    The Bezout bound is 16.
	    
	    Reference: "Solving deficient polynomial systems with homotopies which keep 
	    the subschemes at infinity invariant" by T.Y. Li and X. Wang (pages 693-710).
	    
	    See also: http://homepages.math.uic.edu/~jan/Demo/lumped.html.
	Example
	    F = lumped(RR_53)
    	    time sols = solveSystem F;
    	    #sols
    /// 
