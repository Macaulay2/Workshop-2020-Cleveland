export {"conform1"}

conform1 = method();
conform1(Ring) := kk -> (
    t := symbol t;
    R := kk[t_1..t_3];
    {  -9 - t_2^2 - t_3^2 - 3*t_2^2*t_3^2 + 8*t_2*t_3,
       -9 - t_3^2 - t_1^2 - 3*t_3^2*t_1^2 + 8*t_3*t_1,
       -9 - t_1^2 - t_2^2 - 3*t_1^2*t_2^2 + 8*t_1*t_2
	       }
)

beginDocumentation()

doc /// 
    Key
    	conform1
	(conform1,Ring)
    Headline
    	conformal analysis of cyclic molecules, first instance
    Usage
    	conform1(kk)
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
	   
	    There were 16 solutions found in 0.369193 seconds (with a Bezout bound of 64).
	    
	    Reference: 
	    Ioannis Z. Emiris.
	    "Sparse Elimination and Application in Kinematics:
	    PhD Thesis, Computer Science, University of California at Berkeley, 1994.

            Ioannis Z. Emiris.
	    "A general Solver Based on Sparse Resultants: Numerical Issues and Kinematic Applications",
	    INRIA Rapport de Recherche no 3110, January 1997, 29 pages
	    Available via anonymous ftp to ftp.inria.fr
	    
	    See also: http://homepages.math.uic.edu/~jan/Demo/conform1.html
	Example
	    conform1(QQ)
    ///
