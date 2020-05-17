export {"d1"}

d1 = method();
d1(Ring) := kk -> (
    x := symbol x;
    R := kk[x_1..x_12];
    { x_1^2  + x_2^2 - 1,
      x_3^2  + x_4^2 - 1,
      x_5^2  + x_6^2 - 1,
      x_7^2  + x_8^2 - 1,
      x_9^2  + x_10^2 - 1,
      x_11^2 + x_12^2 - 1,
      3*x_3 + 2*x_5 + x_7 - 3.9701,
      3*x_1*x_4 + 2*x_1*x_6 + x_1*x_8 - 1.7172,
      3*x_2*x_4 + 2*x_2*x_6 + x_2*x_8 - 4.0616,
      x_3*x_9 + x_5*x_9 + x_7*x_9 - 1.9791,
      x_2*x_4*x_9 + x_2*x_6*x_9 + x_2*x_8*x_9 + x_1*x_10 - 1.9115,
      - x_3*x_10*x_11 - x_5*x_10*x_11 - x_7*x_10*x_11 + x_4*x_12 + x_6*x_12 + x_8*x_12 - 0.4077
      }
)

beginDocumentation()

doc /// 
    Key
    	d1
	(d1,Ring)
    Headline
    	a sparse system, known as benchmark D1
    Usage
    	d1(kk)
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
	   
	    There were 48 solutions found in 87.5181 seconds (with a Bezout bound of 4608).
	    
	    Reference: 
	    H. Hong and V. Stahl.
	    "Safe Starting Regions by Fixed Points and Tightening",
	    Computing 53(3-4): 322-335, 1995.
	    
	    See also: http://homepages.math.uic.edu/~jan/Demo/d1.html	    
	Example
	    d1(RR_53)
    ///
