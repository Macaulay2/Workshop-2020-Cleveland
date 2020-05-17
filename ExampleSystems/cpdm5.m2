export {"cpdm5"}

cpdm5 = method();
cpdm5(Ring) := kk -> (
    x := symbol x;
    R := kk[x_1..x_5];
    { 4*x_1^3+ 3*x_1^2*x_2+ 3*x_1^2*x_3+ 3*x_1^2*x_4+ 3*x_1^2*x_5+ 3*x_1*x_2^2+ 3*x_1*x_3^2+ 3*x_1*x_4^2+ 3*x_1*x_5^2+x_2^3+x_3^3+x_4^3+x_5^3+ 2*x_1^2+ 3*x_1*x_2+ 3*x_1*x_3+ 3*x_1*x_4+ 3*x_1*x_5-x_2^2-x_3^2-x_4^2-x_5^2-6*x_1,
      x_1^3+ 3*x_1^2*x_2+ 3*x_1*x_2^2+ 4*x_2^3+ 3*x_2^2*x_3+ 3*x_2^2*x_4+ 3*x_2^2*x_5+ 3*x_2*x_3^2+ 3*x_2*x_4^2+ 3*x_2*x_5^2+x_3^3+x_4^3+x_5^3-x_1^2+ 3*x_1*x_2+ 2*x_2^2+ 3*x_2*x_3+ 3*x_2*x_4+ 3*x_2*x_5-x_3^2-x_4^2-x_5^2-6*x_2,
      x_1^3+ 3*x_1^2*x_3+ 3*x_1*x_3^2+x_2^3+ 3*x_2^2*x_3+ 3*x_2*x_3^2+ 4*x_3^3+ 3*x_3^2*x_4+ 3*x_3^2*x_5+ 3*x_3*x_4^2+ 3*x_3*x_5^2+x_4^3+x_5^3-x_1^2+ 3*x_1*x_3-x_2^2+ 3*x_2*x_3+ 2*x_3^2+ 3*x_3*x_4+ 3*x_3*x_5-x_4^2-x_5^2-6*x_3,
      x_1^3+ 3*x_1^2*x_4+ 3*x_1*x_4^2+x_2^3+ 3*x_2^2*x_4+ 3*x_2*x_4^2+x_3^3+ 3*x_3^2*x_4+ 3*x_3*x_4^2+ 4*x_4^3+ 3*x_4^2*x_5+ 3*x_4*x_5^2+x_5^3-x_1^2+ 3*x_1*x_4-x_2^2+ 3*x_2*x_4-x_3^2+ 3*x_3*x_4+ 2*x_4^2+ 3*x_4*x_5-x_5^2-6*x_4,
      x_1^3+ 3*x_1^2*x_5+ 3*x_1*x_5^2+x_2^3+ 3*x_2^2*x_5+ 3*x_2*x_5^2+x_3^3+ 3*x_3^2*x_5+ 3*x_3*x_5^2+x_4^3+ 3*x_4^2*x_5+ 3*x_4*x_5^2+ 4*x_5^3-x_1^2+ 3*x_1*x_5-x_2^2+ 3*x_2*x_5-x_3^2+ 3*x_3*x_5-x_4^2+ 3*x_4*x_5+ 2*x_5^2-6*x_5
       }
)

beginDocumentation()

doc /// 
    Key
    	cpdm5
	(cpdm5,Ring)
    Headline
    	put headline description here
    Usage
    	cpdm5(kk)
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
	   
	    There were 213 solutions found in 1.07843 seconds (with a Bezout bound of 243).
	    
	    Reference: 
	    
	    
	Example
	    cpdm5(QQ)
    ///
