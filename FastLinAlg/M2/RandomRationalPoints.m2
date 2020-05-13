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

randomRatPt = I -> (
	R:=ring I;
	if char R == 0 then error "expected a finite ground field";
	if not class R === PolynomialRing then error "expected an ideal in a polynomial ring";
	if not isHomogeneous I then error "expected a homogenous ideal";
	n:=dim I;
	if n<=1 then error "expected a positive dimensional scheme";
	c:=codim I;
	Rs:=R;
	Re:=R;
	f:=I;
	if not c==1 then (
		-- projection onto a hypersurface
		parametersystem:=ideal apply(n,i->R_(i+c));
		if not dim(I+parametersystem)== 0 then return print "make coordinate change";
		kk:=coefficientRing R;
		Re=kk(monoid[apply(dim R,i->R_i),MonomialOrder => Eliminate (c-1)]);
		rs:=(entries selectInSubring(1,vars Re))_0;
		Rs=kk(monoid[rs]);
		f=ideal substitute(selectInSubring(1, generators gb substitute(I,Re)),Rs);
		if not degree I == degree f then return print "make coordinate change"
		);
	H:=0;pts:=0;pts1:=0;trial:=1;pt:=0;ok:=false;
	while (
		H=ideal random(Rs^1,Rs^{dim Rs-2:-1});
		pts=decompose (f+H);
		pts1=select(pts,pt-> degree pt==1 and dim pt ==1);
		ok=( #pts1>0); 
		if ok then (pt=saturate(substitute(pts1_0,R)+I);ok==(degree pt==1 and dim pt==0));
		not ok) do (trial=trial+1);
	pt
)


--Function to check if random point is in the variety
randomPoint = method( Options=>{});

randomPoint(Ideal) :=opts->(I1)->(
	genList:= first entries gens I1;
	K:=coefficientRing ring I1;point:=createRandomPoints(I1);
	eval:= map(K,ring I1,point);
	j:=0;
	while(j< #genList) do (
        tempEval:=eval(genList_j);
        if not (tempEval==0) then return false;
		j=j+1
	);
    if (tempEval ==0) then return point else return false;
)
 
randomPoint(ZZ,Ideal):=opts->(n1,I1)->(
    j:=0;
    local point;
    while( j<n1) do (
		point=randomPoint(I1);
	    if not (point===false ) then return point; 
	  	j=j+1;
	);
    return false;
);
  
   
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

document { 
	Key => RandomRationalPoints,
	Headline => "an example Macaulay2 package",
	EM "RandomRationalPoints", " is an example package which can be used as a template for user packages."
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