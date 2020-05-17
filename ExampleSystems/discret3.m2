export {"discret3"}

discret3 = method();
discret3(Ring) := kk -> (
    (a,b,y,z,s,t,u,v) := (symbol a, symbol b, symbol y, symbol z, 
	symbol s, symbol t, symbol u, symbol v );
    R := kk[a,b,y,z,s,t,u,v];
    { -1.37539569915948e-1*y^2-9.16930466106320e-2*y*z-6.87697849579740e-2*y*t-5.50158279663792e-2*y*u-4.58465233053160e-2*y*v-3.92970199759852e-2*y*s-3.43848924789870e-2*y*a+ 4.12618709747844*y-4.40126623731034,
      -1.78264047725719e-1*y*z-1.33698035794289e-1*z^2-1.06958428635431e-1*z*t-8.91320238628593e-2*z*u-7.63988775967365e-2*z*v-6.68490178971445e-2*z*s-5.94213492419062e-2*z*a+ 4.01094107382867*z-4.27833714541725,
      -1.96868164299851e-1*y*t-1.57494531439881e-1*z*t-1.31245442866567e-1*t^2-1.12496093885629e-1*t*u-9.84340821499253e-2*t*v-8.74969619110448e-2*t*s-7.87472657199403e-2*t*a+ 3.93736328599701*t-4.19985417173015,
      -2.07217047148772e-1*y*u-1.72680872623977e-1*z*u-1.48012176534837e-1*t*u-1.29510654467983e-1*u^2-1.15120581749318e-1*u*v-1.03608523574386e-1*u*s-9.41895668858055e-2*u*a+ 3.88531963403948*u-4.14434094297544,
      -2.13678947124996e-1*y*v-1.83153383249996e-1*z*v-1.60259210343747e-1*t*v-1.42452631416664e-1*u*v-1.28207368274997e-1*v^2-1.16552152977270e-1*v*s-1.06839473562498e-1*v*a+ 3.84622104824992*v-4.10263578479991,
      -2.18035916725452e-1*y*s-1.90781427134770e-1*z*s-1.69583490786463e-1*t*s-1.52625141707816e-1*u*s-1.38750128825288e-1*v*s-1.27187618089847e-1*s^2-1.17403955159859e-1*s*a+ 3.81562854269541*s-4.07000377887510,
      -2.21139931193274e-1*y*a-1.96568827727354e-1*z*a-1.76911944954619e-1*t*a-1.60829040867835e-1*u*a-1.47426620795516e-1*v*a-1.36086111503553e-1*s*a-1.26365674967585e-1*a^2+ 3.79097024902755*a-4.04370159896272,
      -2.23445119966269e-1*y*b-2.01100607969642e-1*z*b-1.82818734517856e-1*t*b-1.67583839974702e-1*u*b-1.54692775361263e-1*v*b-1.43643291406887e-1*s*b-1.34067071979761e-1*a*b+ 3.77063639943078*b-4.02201215939284	
      }
)
-- check this out.  Has fewer solutions than in the database it came from

beginDocumentation()

doc /// 
    Key
    	discret3
	(discret3,Ring)
    Headline
    	system discret3, every equation divided by average coefficient
    Usage
    	discret3(kk)
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
	   
	    There were 49 solutions found in 1.86936 seconds (with a Bezout bound of 256).
	    
	    Reference: 
	    From POSSO via e-mail, on the occasion of the state-of-the-art workshop in Toulouse, December 1994.
	    
	    See also: http://homepages.math.uic.edu/~jan/Demo/discret3.html
	Example
	    discret3(QQ)
    ///
