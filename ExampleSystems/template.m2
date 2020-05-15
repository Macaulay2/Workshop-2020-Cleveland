export {"example-name"}

example-name = method();
example-name(Ring) := kk -> (
    (x,y,z,t) := (symbol x, symbol y, symbol z, symbol t);
    R := kk[x,y,z,t];
    { -- put polynomials here
	
       }
)

beginDocumentation()

doc /// 
    Key
    	example-name
	(example-name,Ring)
    Headline
    	put headline description here
    Usage
    	example-name(kk)
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
	   
	    There were x solutions found in y seconds (with a Bezout bound of z).
	    
	    Reference: 
	    
	    
	Example
	    example-name(QQ)
    ///
