export {"des183"}

des183 = method();
des183(Ring) := kk -> (
    (a,b,c) := (symbol a, symbol b, symbol c);
    R := kk[a,b_0..b_2,c_0..c_3];
    {  6*c_3*a*b_0 + 10*b_2*a*c_1 + 8*c_2*a*b_1 - 162*a^2*b_1 + 16*b_1*c_0 + 14*c_1*b_0 + 48*a*c_0,
       15*c_3*a*b_1 - 162*a^2*b_2 - 312*a*b_0 + 24*a*c_0 + 27*c_1*b_1 + 24*c_2*b_0 + 18*b_2*a*c_2 + 30*b_2*c_0 + 84*c_1*a,
       -240*a + 420*c_3 - 64*b_2 + 112*c_2,
       180*c_3*a - 284*b_2*a - 162*a^2 + 60*b_2*c_2 + 50*c_2*a + 70*c_0 + 55*c_3*b_1 + 260*c_1 - 112*b_0,
       66*c_3*a + 336*c_2 + 90*c_1 + 78*b_2*c_3 - 1056*a - 90*b_1,
       136*c_3 - 136,
       4*b_2*a*c_0 + 2*c_2*a*b_0 + 6*b_0*c_0 - 162*a^2*b_0 + 3*c_1*b_1*a,
       28*b_2*a*c_3 + 192*c_0 + 128*c_2*a + 36*c_1*b_0 + 36*c_3*b_0 - 300*a*b_1 + 40*c_2*b_1 - 648*a^2 + 44*b_2*c_1
       }
)

beginDocumentation()

doc /// 
    Key
    	des183
	(des183,Ring)
    Headline
    	
    Usage
    	des183(kk)
    Inputs
    	kk:Ring
	    the coefficient ring
    Outputs
    	:List	
	    of the polynomials in the system
    Description
    	Text
	   This system was solved in May 2020, using @TO solveSystem@ in Macaulay2 v1.15
	     with an Intel(R) Core(TM) i5-4258U CPU at 2.40GHz.
	   
	    There were 46 solutions found in 1.58463 seconds (with a Bezout bound of 324).
	    
	    Reference: 
	    
	    
	    
	    See also: http://homepages.math.uic.edu/~jan/Demo/des18_3.html
	Example
	    des183(QQ)
    ///
