export {"speer"}

speer = method();
speer(Ring) := kk -> (
    x := symbol x;
    R := kk[x_1..x_4];
    { ( 6.57958984375e-1 - 1.87652587890625e-1*ii) * (( 9.3768310546875e-1 - 2.88299560546875e-1*ii) + 2*(x_1+x_2+x_3+x_4) - 8*x_1 ) * ( x_1*x_2*x_3*x_4 - x_1*x_2 - x_2*x_3 - x_3*x_4 - x_4*x_1 ) - x_2*x_3*x_4 + x_2 + x_4,
    ( 6.57958984375e-1 - 1.87652587890625e-1*ii) * (( 9.3768310546875e-1 - 2.88299560546875e-1*ii) + 2*(x_1+x_2+x_3+x_4) - 8*x_3 ) * ( x_1*x_2*x_3*x_4 - x_1*x_2 - x_2*x_3 - x_3*x_4 - x_4*x_1)  - x_2*x_1*x_4 + x_2 + x_4,
    ( 6.57958984375e-1 - 1.87652587890625e-1*ii) * (( 9.3768310546875e-1 - 2.88299560546875e-1*ii) + 2*(x_1+x_2+x_3+x_4) - 8*x_2 ) * ( x_1*x_2*x_3*x_4 - x_1*x_2 - x_2*x_3 - x_3*x_4 - x_4*x_1) - x_1*x_3*x_4 + x_1 + x_3,
    ( 6.57958984375e-1 - 1.87652587890625e-1*ii) * (( 9.3768310546875e-1 - 2.88299560546875e-1*ii) + 2*(x_1+x_2+x_3+x_4) - 8*x_4 ) * ( x_1*x_2*x_3*x_4 - x_1*x_2 - x_2*x_3 - x_3*x_4 - x_4*x_1) - x_1*x_3*x_2 + x_1 + x_3
    }
)

beginDocumentation()

doc /// 
    Key
    	speer
	(speer,Ring)
    Headline
    	the system of E.R. Speer
    Usage
    	speer(kk)
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
	   
	    There were 72 solutions found in 11.9958 seconds (with a Bezout bound of 625).
	    
	    Reference: 
	    Karin Gatermann.
	    "Symbolic solution of polynomial equation systems with symmetry",
	    Proceedings of ISSAC-90, pp 112-119, ACM New York, 1990.
	    
	Example
	    speer(CC_53)
    ///
