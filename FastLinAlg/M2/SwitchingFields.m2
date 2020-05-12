-- -*- coding: utf-8 -*-
newPackage(
	"SwitchingFields",
    	Version => "0.1", 
    	Date => "May 11, 2020",
    	Authors => {
	     {Name => "Zhan Jiang", Email => "zoeng@umich.edu", HomePage => "http://www-personal.umich.edu/~zoeng/"},
	     {Name => "Sarasij Maitra", Email => "sm3vg@virginia.edu", HomePage => "https://people.virginia.edu/~sm3vg"}
	     },
    	Headline => "an example Macaulay2 package",
	AuxiliaryFiles => false -- set to true if package comes with auxiliary files
    	)

-- Any symbols or functions that the user is to have access to
-- must be placed in one of the following two lists
export {"fieldExtension", "switchFieldMap", "MyOption"}
exportMutable {}

fieldExtension = method(TypicalValue => Sequence, Options => {})
fieldExtension(Ring, GaloisField) := (Ring, RingMap) => opts -> (r1, k1) -> (
    if char r1 != char k1 
    then error "There is no field extension between fields of different positive characteristics";
    
    -- r1 = s1 / i1  = l1 [ s1.gens ] / i1
    s1 := ambient r1; 
    l1 := coefficientRing s1;
    i1 := ideal r1;
    
    try map(k1, l1) 
    then f1 := map(k1, l1)
    else error "The base field of R is not a subfield of K";
    
    s2 := k1(monoid s1);
    f2 := map(s2, s1, append(s2.gens, f1(l1_0)));
    
    t1 := s2 / f2(i1);
    
    return (t1, map(t1, r1, append(t1.gens, f1(l1_0))))
)

   
-- A function with an optional argument
switchFieldMap = method(TypicalValue => RingMap, Options => {})
switchFieldMap(Ring, Ring, List) := RingMap => opts -> (r1, r2, k1) ->(
    (T1,f1) := fieldExtension(r2, coefficientRing r1);
         g1 := map(r1,T1,k1);
	 g2 := g1*f1;
	 return g2;
	 )
    


beginDocumentation()
document { 
    Key => SwitchingFields,
    Headline => "a Macaulay2 package",
    EM "SwitchingFields", " is an example package which can
	be used as a template for user packages."
}

doc ///
    Key
        fieldExtension
	(fieldExtension, Ring, GaloisField)
    Headline
        prototype: This function is provided by the package  TO SwitchingFields.
    Usage
        fieldExtension(R, K)
    Inputs
	R:Ring
	    a ring with a GaloisField L as its coefficientRing
	K:GaloisField
	    a field extension of L
    Outputs
        :Sequence
	    a ring R  otimes L K and a ring map R -> R otimes L K
    Description
        Text  
       	    Some words to say things. You can even use LaTeX $R = k[x,y,z]$. 

        Example
            R = GF(8)[x,y,z]/(x*y-z^2)
     	    K = GF(64)
	    fieldExtension(R,K)
	   
        Text
       	    More words, but don't forget to indent. 
	   
    SeeAlso
    
    Caveat
    
///

doc ///
    Key
        switchFieldMap
	(switchFieldMap, Ring, Ring, List)
    Headline
        prototype: This function is provided by the package  TO SwitchingFields.
    Usage
        switchFieldMap(R, S, L)
    Inputs
	R:Ring
	    a ring with a GaloisField X as its coefficientRing
	S:Ring
	    a ring with a GaloisField Y as its coefficientRing
	L:List
	    a list which is used to map from S to R
    Outputs
        :RingMap
	    the natural ring map from S to R
    Description
        Text  
       	    Some words to say things. You can even use LaTeX $R = k[x,y,z]$. 

        Example
            R = GF(64)[x,y,z]/(x*y-z^2)
     	    S = GF(8)[a]
	    L = {x}
	    switchFieldMap(R,S,L)
	   
        Text
       	    More words, but don't forget to indent. 
	   
    SeeAlso
    
    Caveat
    
///



TEST ///
(T,f) := fieldExtension(GF(8)[y], GF(64))
g := switchFieldMap(GF(64)[x,y,z]/(x*y-z^2), GF(8)[a],{x})
///
  
       
end

-- Here place M2 code that you find useful while developing this
-- package.  None of it will be executed when the file is loaded,
-- because loading stops when the symbol "end" is encountered.

installPackage "SwitchingFields"
installPackage("SwitchingFields", RemakeAllDocumentation=>true)
check SwitchingFields

-- Local Variables:
-- compile-command: "make -C $M2BUILDDIR/Macaulay2/packages PACKAGES=SwitchingFields pre-install"
-- End: