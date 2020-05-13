-- -*- coding: utf-8 -*-
newPackage(
	"RandomRationalPoints",
    	Version => "1.0", 
    	Date => "April 28, 2005",
    	Authors => {
	     {Name => "Jane Doe", Email => "doe@math.uiuc.edu"}
	     },
    	HomePage => "http://www.math.uiuc.edu/~doe/",
    	Headline => "an example Macaulay2 package",
	AuxiliaryFiles => false -- set to true if package comes with auxiliary files
    	)

-- Any symbols or functions that the user is to have access to
-- must be placed in one of the following two lists
export {"randomPoint", "fieldElements", "firstFunction", "secondFunction", "MyOption", "GenericProjection", "NumPointsToCheck"}
exportMutable {}

randomPoint = method(Options => {NumPointsToCheck => 10, GenericProjection => false})

randomPoint(Ideal) := opts -> (I1) -> (
	gensList := first entries gens I1;
	elementList := fieldElements(coefficientRing(ring I1));
	i := 0;
	flag := false; --this flag gets set if we found a point
	local randomPt; --this is a list of values in our field
	while (i < opts.NumPointsToCheck) do (
		--do some checking to see if some random point is actually in the variety.
		i = i+1;	
	);
	if (flag == true) then
	(
		return randomPoint;
	)
	else (
		return null;
	);
);


--this function was taken directly from an internal function in RationalPoints.m2 by Nathaniel Stapleton
fieldElements = (k) -> (
     J := ideal k;
     p := char k;
     els := {};
     galoisfield := class k === GaloisField;     	       
     if galoisfield then (
	  x := k.PrimitiveElement; --sometimes k_0 is not the primitive element ie. GF 9
	  e := 1;
	  b := 0;
	  els = els|{0};
	  while b != 1 do (
	       b = x^e;
	       e = e+1;
	       els = els | {b};
	       );
	  );
     if not galoisfield and char ring J != 0 then ( 
     	  d := (degree((flatten entries gens J)_0))_0;
     	  a := (gens k)_0;
          coeffs := toList ((set toList (0..p-1)) ^** (d));
     	  for i to # coeffs - 1 do (
	       x := 0;
	       for j to d-1 do (
	       	    x = x+coeffs_i_j*a^j;
	       	    );
	       els = els | {x};
	       );
	  );
     if not galoisfield and char ring J == 0 then els = toList (0..p-1);     
     return els;
     );

firstFunction = method(TypicalValue => String)
firstFunction ZZ := String => n -> (
	if n == 1
	then "Hello, World!"
	else "D'oh!"	
	)
    
  --Function to create a random point 
   createRandomPoints=(I1)->(
    noVar := #generators ring I1;
    K:=coefficientRing ring (I1);
   return toList apply(noVar, i ->random(K) )
   ) 

--Function to check if random point is in the variety
evaluate= method( Options=>{});






evaluate(Ideal) :=opts->(I1)->
(genList:= first entries gens I1;
K:=coefficientRing ring I1;point:=createRandomPoints(I);
eval:= map(K,ring I1,point);
  j:=0;while(j< #genList) do (
          tempEval:=eval(genList_j);
          if not (tempEval==0) then return false else 
               j=j+1);
          if (tempEval ==0) then 
   return point  else return false;
   )
 
 evaluate(ZZ,Ideal):=opts->(n1,I1)->(
     j:=0;
     local point;
      while( j<n1) do (
	    point=evaluate(I1);
	    if not (point===false ) then return point 
	  else    j=j+1;
	   );
       return false;)
	      
 )
  
   
-- A function with an optional argument
secondFunction = method(
     TypicalValue => ZZ,
     Options => {MyOption => 0}
     )
secondFunction(ZZ,ZZ) := o -> (m,n) -> (
     if not instance(o.MyOption,ZZ)
     then error "The optional MyOption argument must be an integer";
     m + n + o.MyOption
     )
secondFunction(ZZ,List) := o -> (m,n) -> (
     if not instance(o.MyOption,ZZ)
     then error "The optional MyOption argument must be an integer";
     m + #n + o.MyOption
     )

beginDocumentation()

doc ///
    Key
        createRandomPoints
	(createRandomPoints, Ideal)
    Headline
        prototype: This function is provided by the package  TO create a random point.
    Usage
        createRandomPoints(I)
    Inputs
    I: Ideal inside a polynomial ring 
    Outputs
        :A random List of elements which will provid a random point in the affine plane.
	    
    Description
        --Text  
       	   -- Some words to say things. You can even use LaTeX $R = k[x,y,z]$. 
--
        Example
            R = QQ[x,y]
     	    I= ideal(random(2,R),random(3,R))
	    createRandomPoint I
	    
	   
        --Text
       	   -- More words, but don't forget to indent. 
	   
   -- SeeAlso
    
    Caveat
    
///

doc ///
    Key
        evaluate
	(evaluate, Ideal)
	(evaluate,ZZ,Ideal)
    Headline
        prototype: This function in  the package will  will and tell if some random point is in the variety or not.
    Usage
        evaluate(I)
    Inputs
    I: Ideal inside a polynomial ring. 
    Outputs
        :A random point if it is in the variety otherwise False.
	    
    Description
        --Text  
       	   -- Some words to say things. You can even use LaTeX $R = k[x,y,z]$. 
--
        Example
            R = QQ[x,y]
     	    I= ideal(random(2,R),random(3,R))
	    evaluate I
	    
	   
        --Text
       	   -- More words, but don't forget to indent. 
	   
   -- SeeAlso
    
    Caveat
    
///

document { 
	Key => RandomRationalPoints,
	Headline => "an example Macaulay2 package",
	EM "RandomRationalPoints", " is an example package which can
	be used as a template for user packages."
	}
document {
	Key => {firstFunction, (firstFunction,ZZ)},
	Headline => "a silly first function",
	Usage => "firstFunction n",
	Inputs => {
		"n" => ZZ => {}
		},
	Outputs => {
		String => {}
		},
	"This function is provided by the package ", TO RandomRationalPoints, ".",
	EXAMPLE {
		"firstFunction 1",
		"firstFunction 0"
		}
	}
document {
	Key => secondFunction,
	Headline => "a silly second function",
	"This function is provided by the package ", TO RandomRationalPoints, "."
	}
document {
	Key => (secondFunction,ZZ,ZZ),
	Headline => "a silly second function",
	Usage => "secondFunction(m,n)",
	Inputs => {
	     "m" => {},
	     "n" => {}
	     },
	Outputs => {
	     {"The sum of ", TT "m", ", and ", TT "n", 
	     ", and "}
	},
	EXAMPLE {
		"secondFunction(1,3)",
		"secondFunction(23213123,445326264, MyOption=>213)"
		}
	}
document {
     Key => MyOption,
     Headline => "optional argument specifying a level",
     TT "MyOption", " -- an optional argument used to specify a level",
     PARA{},
     "This symbol is provided by the package ", TO RandomRationalPoints, "."
     }
document {
     Key => [secondFunction,MyOption],
     Headline => "add level to result",
     Usage => "secondFunction(...,MyOption=>n)",
     Inputs => {
	  "n" => ZZ => "the level to use"
	  },
     Consequences => {
	  {"The value ", TT "n", " is added to the result"}
	  },
     "Any more description can go ", BOLD "here", ".",
     EXAMPLE {
	  "secondFunction(4,6,MyOption=>3)"
	  },
     SeeAlso => {
	  "firstFunction"
	  }
     }
TEST ///
  assert(firstFunction 1 === "Hello, World!")
  assert(secondFunction(1,3) === 4)
  assert(secondFunction(1,3,MyOption=>5) === 9)
///
  
 --Need help to write this part 
  TEST///
R=QQ[t_1..t_3];
I = ideal(t_1,t_2+t_3);
assert(#(createRandomPoints(I))==3)
   ///
   
 TEST///
 R=QQ[t_1..t_3];
I = ideal(t_1,t_2+t_3, t_1-1);
assert(evaluate(I)===false); 
 ///   
       
end

-- Here place M2 code that you find useful while developing this
-- package.  None of it will be executed when the file is loaded,
-- because loading stops when the symbol "end" is encountered.

installPackage "RandomRationalPoints"
installPackage("RandomRationalPoints", RemakeAllDocumentation=>true)
check RandomRationalPoints

-- Local Variables:
-- compile-command: "make -C $M2BUILDDIR/Macaulay2/packages PACKAGES=RandomRationalPoints pre-install"
-- End: