export {"sparse5"}

sparse5 = method();
sparse5(Ring) := kk -> (
    x := symbol x;
    R := kk[x_1..x_5];
    { x_1^2*x_2^2*x_3^2*x_4^2*x_5^2 + 3*x_1^2 + x_2^2 + x_3^2 + x_4^2 + x_5^2 + x_1*x_2*x_3*x_4*x_5 + 5,
      x_1^2*x_2^2*x_3^2*x_4^2*x_5^2 + x_1^2 + 3*x_2^2 + x_3^2 + x_4^2 + x_5^2 + x_1*x_2*x_3*x_4*x_5 + 5,
      x_1^2*x_2^2*x_3^2*x_4^2*x_5^2 + x_1^2 + x_2^2 + 3*x_3^2 + x_4^2 + x_5^2 + x_1*x_2*x_3*x_4*x_5 + 5,
      x_1^2*x_2^2*x_3^2*x_4^2*x_5^2 + x_1^2 + x_2^2 + x_3^2 + 3*x_4^2 + x_5^2 + x_1*x_2*x_3*x_4*x_5 + 5,
      x_1^2*x_2^2*x_3^2*x_4^2*x_5^2 + x_1^2 + x_2^2 + x_3^2 + x_4^2 + 3*x_5^2 + x_1*x_2*x_3*x_4*x_5 + 5	
       }
)

beginDocumentation()

doc /// 
    Key
    	sparse5
	(sparse5,Ring)
    Headline
    	a 5-dimensional sparse symmetric polynomial system
    Usage
    	sparse5(kk)
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
	   
	    There were 100,000 solutions found in 4096.28 seconds (with a Bezout bound of 160).
	    
	    Reference: 
	    Jan Verschelde and Karin Gatermann:
	    "Symmetric Newton Polytopes for Solving Sparse Polynomial Systems",
	    Adv. Appl. Math., 16(1): 95-127, 1995.	    
	    
	    See also: http://homepages.math.uic.edu/~jan/Demo/sparse5.html
	Example
	    sparse5(QQ)
    ///
