-- -*- coding: utf-8 -*-
newPackage(
	"RandomRationalPoints",
    	Version => "1.0", 
    	Date => "April 28, 2005",
    	Authors => {
	     {Name => "Sankhaneel Bisui", Email => "sbisu@tulane.edu"},
	     {Name=> "Thai Nguyen", Email =>"tnguyen11@tulane.edu"}
	     },
    	HomePage => "http://www.math.uiuc.edu/~doe/",
    	Headline => "an example Macaulay2 package",
	AuxiliaryFiles => false -- set to true if package comes with auxiliary files
    	)

-- Any symbols or functions that the user is to have access to
-- must be placed in one of the following two lists
export {"randomPoint", "fieldElements","createRandomPoints", "GenericProjection"}
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


    
  --Function to create a random point 
createRandomPoints= method(TypicalValue => List, Options => {})
createRandomPoints(Ideal):=List => opts->(I1) ->(
    noVar := #generators ring I1;
    K:=coefficientRing ring (I1);
    L:=toList apply(noVar, i ->random(K));
    return L )


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

randomPoint(Ideal) := List => opts->(I1)->(
	genList:= first entries gens I1;
	K:=coefficientRing ring I1;point:=createRandomPoints(I1);
	eval:= map(K,ring I1,point);
	j:=0;
	while(j< #genList) do (
        tempEval:=eval(genList_j);
        if not (tempEval==0) then return false;
		j=j+1
	);
        if (tempEval ==0) then return point else return "Failed to  find";
)
 
randomPoint(ZZ,Ideal):=List => opts->(n1,I1)->(
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


beginDocumentation()
document { 
	Key => RandomRationalPoints,
	Headline => "Give a random point in a variety",
	EM "RandomRationalPoints", "Give a random point inside a affine space that lies inside a variety ."
}
    

doc ///
    Key
        createRandomPoints
	(createRandomPoints, Ideal)
    Headline
        Finds a Random Point
    Usage
        createRandomPoints(I)
    Inputs
        I:Ideal 
	    ideal inside a polynomial Ring
    Outputs
        :List
         --   Point in affine space.
    Description
       Text
         Give a random point in the ambient space of the V(I).  
       	 
	    
	Example
	  
--	    
--	Text
	    --This function is a fix for that. See following example

      --  Example
           -- K2 = GF(8, Variable=>b); L2 = GF(64, Variable=>c);
	   -- fieldExtension(L2, K2)
	    
	   
       -- Text
       	  -- The function is implemented by composing the isomorphism $K_2\cong K_1$, the natural embedding $K_1\to L_1$ and the isomorphism $L_1\cong L_2$.
	   
   --SeeAlso
    
   -- Caveat
       -- The function depends on the implementation of map(GaloisField,GaloisField).
    
///
doc ///
    Key
        randomPoint
	(randomPoint, Ideal)
    Headline
        a function to check if  a random point is  in a variety
    Usage
        randomPoint(I)
    Inputs
	I:Ideal
	   Ideal inside a polynomial ring
    --Outputs
        :List
	   -- ($T$ ,$f$) where $T = R  \otimes_L K$ is the base-changed ring, $f:R\to T$ is the ring map $R\otimes_L L\to R\otimes_L K$ induced from $L\to K$.
   -- Description
        --Text  
       	   -- Some words to say things. You can even use LaTeX $R = k[x,y,z]$. 
--
      --  Example
           -- R=ZZ/5[t_1..t_3];
           -- I = ideal(t_1,t_2+t_3^2);
	  -- randomPoint(I)
        --Text
       	   -- More words, but don't forget to indent. 
	   
    --SeeAlso
    
    --Caveat
    
///


doc ///
    Key
        randomPoint
	(randomPoint,ZZ,Ideal)
    Headline
        a function to find  a random point  in a variety upto a given number of trials
    Usage
        randomPoint(n,I)
    Inputs
	I:Ideal
	   Ideal inside a polynomial ring
        n: ZZ
            An integer 
    Outputs
        :List
	-- False   -- ($T$ ,$f$) where $T = R  \otimes_L K$ is the base-changed ring, $f:R\to T$ is the ring map $R\otimes_L L\to R\otimes_L K$ induced from $L\to K$.
    Description
        Text  
       	   Gives a point in a variety V(I), after n trials. 
--
        Example
           R=ZZ/5[t_1..t_3];
           I = ideal(t_1,t_2+t_3);
	   randomPoint(1000,I)
	   
        --Text
       	   -- More words, but don't forget to indent. 
	   
    SeeAlso
         fieldElements 
        
          
    
    
    
///
 ----- TESTS -----   

TEST///
 R=QQ[t_1..t_3];
 I = ideal(t_1,t_2+t_3);
 assert(#(createRandomPoints(I))===3)
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