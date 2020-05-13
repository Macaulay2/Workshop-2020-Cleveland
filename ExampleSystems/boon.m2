export {"boon"}

boon = method()
boon(Ring) := kk -> (
    (s,g,C) := (symbol s, symbol g, symbol C);
    R := kk[s_1,s_2,g_1,g_2,C_1,C_2];
    {s_1^2 + g_1^2 - 1,
      s_2^2 + g_2^2 - 1,
      C_1*g_1^3 + C_2*g_2^3 - 6/5,
      C_1*s_1^3 + C_2*s_2^3 - 6/5,
      C_1*g_1^2*s_1 + C_2*g_2^2*s_2 - 7/10,
      C_1*g_1*s_1^2 + C_2*g_2*s_2^2 - 7/10
      }
  )

beginDocumentation()

doc /// 
    Key
    	boon
	(boon,Ring)
    Headline
    	a neurophysiology problem posted by Sjirk Boon
    Usage
    	boon(kk)
    Inputs
    	kk:Ring
	    the coefficient ring
    Outputs
    	:List	
	    of the polynomials in the system
    Description
    	Text
	    The Bezout bound is 1024.
	    
	    Reference: 
	    P. Van Hentenryck, D. McAllester and D. Kapur:
	    "Solving Polynomial Systems Using a Branch and Prune Approach"
	    SIAM J. Numerical Analysis, Vol. 34, No. 2, pp 797-827, 1997.
	    
	    See also: post to sci.math.num-analysis by Sjirk Boon
	    
	    See also: http://homepages.math.uic.edu/~jan/Demo/reimer5.html.	    
	Example
	    F = boon(QQ)
	    time sols = solveSystem F;
	    #sols
    ///
     
-----------------------------------------------------------
----------------------------------------------------------- 
end
-----------------------------------------------------------
-----------------------------------------------------------  
-- Here place M2 code that you find useful while developing this
-- package.  None of it will be executed when the file is loaded,
-- because loading stops when the symbol "end" is encountered.
-----------------------------------------------------------
-----------------------------------------------------------  

restart
path = {"~/Workshop-2020-Cleveland/ExampleSystems"}|path
path = {"~/Workshop-2020-Cleveland/"}|path
needsPackage"ExampleSystems"
load "boon.m2"

F = boon(QQ)
time sols = solveSystem F;  -- used 10.7427 seconds
#sols == 8
product(F/degree/first) == 1024

