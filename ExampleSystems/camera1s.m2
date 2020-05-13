export {"camera1s"}

camera1s = method();
camera1s(Ring) := kk -> (
    (d,r) := (symbol d, symbol q);
    R := kk[d_1..d_3,q_1..q_3];
    {  - d_1*q_1 - d_2*q_2 - d_3*q_3 + 1,
       - 36*d_1*q_1 + 41*d_1*q_2 + 20*d_1*q_3 + 1*d_1 + 41*d_2*q_1 + 18*d_2*q_2 + 37*d_2*q_3 - 2*d_2 + 20*d_3*q_1 + 37*d_3*q_2 - 40*d_3*q_3 + 3*d_3 + 1*q_1 - 2*q_2 + 3*q_3 + 58,
       - 2140796*d_1*q_1 - 3998792*d_1*q_2 + 3715992*d_1*q_3 - 282800*d_1 - 3998792*d_2*q_1 - 1575196*d_2*q_2 - 3998792*d_2*q_3 + 3715992*d_3*q_1 - 3998792*d_3*q_2 - 2140796*d_3*q_3 + 282800*d_3 - 282800*q_1 + 282800*q_3 + 5856788,
       346400*d_1*q_1 + 173200*d_1*q_2 - 5999648*d_1*q_3 - 173200*d_1 + 173200*d_2*q_1 - 5999648*d_2*q_2 - 173200*d_2*q_3 + 346400*d_2 - 5999648*d_3*q_1 - 173200*d_3*q_2 - 346400*d_3*q_3 - 173200*d_3 - 173200*q_1 + 346400*q_2 - 173200*q_3 + 5999648,
       - 57013*d_1*q_1 - 29*d_1*q_2 + 37967*d_1*q_3 - 19027*d_1 - 29*d_2*q_1 - 56987*d_2*q_2 + 18973*d_2*q_3 + 38033*d_2 + 37967*d_3*q_1 + 18973*d_3*q_2 + 57031*d_3*q_3 + 7*d_3 - 19027*q_1 + 38033*q_2 + 7*q_3 + 56969,
       - 68*d_1*q_1 - 32*d_1*q_2 + 13*d_1*q_3 + 51*d_1 - 32*d_2*q_1 - 48*d_2*q_2 - 7*d_2*q_3 - 71*d_2 + 13*d_3*q_1 - 7*d_3*q_2 + 90*d_3*q_3 - d_3 + 51*q_1 - 71*q_2 - q_3 + 26
       }
)
-- multiplied by powers of 10 as needed to get rid of decimals.

beginDocumentation()

doc /// 
    Key
    	camera1s
	(camera1s,Ring)
    Headline
    	a system for camera displacement between two positions, with scaled first frame.
    Usage
    	camera1s(kk)
    Inputs
    	kk:Ring
	    the coefficient ring
    Outputs
    	:List	
	    of the polynomials in the system
    Description
    	Text
	    The Bezout bound is 64. 
	    
	    Reference: 
	    
	    Ioannis Z. Emiris.
	    "Sparse Elimination and Application in Kinematics".
	    PhD Thesis, Computer Science, University of California at Berkeley, 1994.	 
    	    
	    Ioannis Z. Emiris.
	    "A general Solver Based on Sparse Resultants:
 	    Numerical Issues and Kinematic Applications",
	    INRIA Rapport de Recherche no 3110, January 1997, 29 pages.
	    Available via anonymous ftp to ftp.inria.fr
	    
	    See also: http://homepages.math.uic.edu/~jan/Demo/camera1s.html
	Example
	    F = camera1s(QQ)
    ///
