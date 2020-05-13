-----------------------------------------------------------
-- Example for inclusion in the ExampleSystems package
-----------------------------------------------------------

export {
    -- methods
    "boon"
    }

-----------------------------------------------------------
-- Methods
-----------------------------------------------------------

boon = method()
boon(Ring) := kk -> (
    local R; local s; local g; local C;
    (s,g,C) = (symbol s, symbol g, symbol C);
    R = kk[s_1,s_2,g_1,g_2,C_1,C_2];
    {s_1^2 + g_1^2 - 1,
      s_2^2 + g_2^2 - 1,
      C_1*g_1^3 + C_2*g_2^3 - 6/5,
      C_1*s_1^3 + C_2*s_2^3 - 6/5,
      C_1*g_1^2*s_1 + C_2*g_2^2*s_2 - 7/10,
      C_1*g_1*s_1^2 + C_2*g_2*s_2^2 - 7/10
      }   			
)

-----------------------------------------------------------
-- Tests
-----------------------------------------------------------
TEST ///

///


-----------------------------------------------------------
-- Documentation
-----------------------------------------------------------
beginDocumentation()

doc /// 
    Key
    	boon
	(boon,Ring)
    Headline
    	a neurophysiology problem posted by Sjirk Boon
    Usage
    	boon(R)
    Inputs
    	R:Ring
	    the coefficient ring
    Outputs
    	:List	
	    a list of the polynomials in Boon's example
    Description
    	Text
	    The Bezout bound is 1024 and the actual root count is . 
	    -- can I put a comment here?  
	    -- Not sure what information should be in the description.
	    
	    Reference: 
	    P. Van Hentenryck, D. McAllester and D. Kapur:
	    "Solving Polynomial Systems Using a Branch and Prune Approach"
	    SIAM J. Numerical Analysis, Vol. 34, No. 2, pp 797-827, 1997.
	    
	    See also: post to sci.math.num-analysis by Sjirk Boon
	    
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


-----------------------------------------------------------
-----------------------------------------------------------  
-- Here place M2 code that you find useful while developing this
-- package.  None of it will be executed when the file is loaded,
-- because loading stops when the symbol "end" is encountered.
-----------------------------------------------------------
-----------------------------------------------------------  

restart
path = {"~/Workshop-2020-Cleveland/ExampleSystems"}|path
needsPackage"ExampleSystems"
load "boon.m2"

L = boon(QQ)
time sols = solveSystem L;  -- used 10.7427 seconds
#sols == 8


