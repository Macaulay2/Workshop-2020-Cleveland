-- -*- coding: utf-8 -*-
newPackage(
	"SwitchingFields",
    	Version => "0.1", 
    	Date => "May 12, 2020",
    	Authors => {
	     {Name => "Zhan Jiang", Email => "zoeng@umich.edu", HomePage => "http://www-personal.umich.edu/~zoeng/"},
	     {Name => "Sarasij Maitra", Email => "sm3vg@virginia.edu", HomePage => "https://people.virginia.edu/~sm3vg"}
	     },
    	Headline => "Switch Base Fields and Obtain Natural Maps",
	AuxiliaryFiles => false -- set to true if package comes with auxiliary files
    	)

-- Any symbols or functions that the user is to have access to
-- must be placed in one of the following two lists
export {"fieldExtension", "fieldBaseChange", "switchFieldMap"}
exportMutable {}

fieldExtension = method(TypicalValue => RingMap, Options => {})
fieldExtension(GaloisField, GaloisField) := RingMap => opts -> (l1, k1) -> (
    if char l1 != char k1 
    then error "fieldExtension: there is no field extension between fields of different positive characteristics";
    
    
    p1 := char l1;
    getDeg := k -> (degree (ideal ambient k)_0)#0;
    degK := getDeg(k1);
    degL := getDeg(l1);
    if degL % degK != 0
    then error "fieldExtension: there is no extension between these two fields";
    
    tempK := GF(p1, degK);
    tempL := GF(p1, degL);
    
    tempG := map(tempK, k1, {tempK_0});
    tempF := map(tempL, tempK);
    tempH := map(l1, tempL, {l1_0});
    
    
    return tempH * tempF * tempG
)

fieldBaseChange = method(TypicalValue => Sequence, Options => {})
fieldBaseChange(Ring, GaloisField) := (Ring, RingMap) => opts -> (r1, k1) -> (
    if char r1 != char k1 
    then error "fieldBaseChange: there is no field extension between fields of different positive characteristics";
    
    -- r1 = s1 / i1  = l1 [ s1.gens ] / i1
    s1 := ambient r1; 
    l1 := coefficientRing s1;
    i1 := ideal r1;
    
    try fieldExtension(k1, l1) 
    then f1 := fieldExtension(k1, l1)
    else error "fieldBaseChange: the base field of R is not a subfield of K";
    
    s2 := k1(monoid s1);
    f2 := map(s2, s1, append(s2.gens, f1(l1_0)));
    
    t1 := s2 / f2(i1);
    
    return (t1, map(t1, r1, append(t1.gens, f1(l1_0))))
)

   
-- A function with an optional argument
switchFieldMap = method(TypicalValue => RingMap, Options => {})
switchFieldMap(Ring, Ring, List) := RingMap => opts -> (r1, r2, k1) ->(
    (T1,f1) := fieldBaseChange(r2, coefficientRing r1);
         g1 := map(r1,T1,k1);
	 g2 := g1*f1;
	 return g2;
	 )
    


beginDocumentation()
document { 
    Key => SwitchingFields,
    Headline => "Switch Base Fields and Obtain Natural Maps",
    EM "SwitchingFields", " is a package that helps to switch the field of 
    coefficients of a given ring, to another given field via 
    the ", EM "natural", " map between these fields.
	"
}

doc ///
    Key
        fieldExtension
	(fieldExtension, GaloisField, GaloisField)
    Headline
        prototype: This function is provided by the package  TO SwitchingFields.
    Usage
        fieldExtension(L, K)
    Inputs
    	K:GaloisField
	    a finite field
	L:GaloisField
	    a field extension of K
    Outputs
        :RingMap
	    the natural ring map K -> L
    Description
        --Text  
       	   -- Some words to say things. You can even use LaTeX $R = k[x,y,z]$. 
--
        Example
            K = GF(8)
     	    L = GF(64)
	    fieldExtension(L,K)
	    
	   
        --Text
       	   -- More words, but don't forget to indent. 
	   
   -- SeeAlso
    
    Caveat
    
///

doc ///
    Key
        fieldBaseChange
	(fieldBaseChange, Ring, GaloisField)
    Headline
        prototype: This function is provided by the package  TO SwitchingFields.
    Usage
        fieldBaseChange(R, K)
    Inputs
	R:Ring
	    a ring with a GaloisField L as its coefficientRing
	K:GaloisField
	    a field extension of L
    Outputs
        :Sequence
	    a ring R  otimes L K and a ring map R -> R otimes L K
    Description
        --Text  
       	   -- Some words to say things. You can even use LaTeX $R = k[x,y,z]$. 
--
        Example
            R = GF(8)[x,y,z]/(x*y-z^2)
     	    K = GF(64)
	    fieldBaseChange(R,K)
	   
        --Text
       	   -- More words, but don't forget to indent. 
	   
    --SeeAlso
    
    --Caveat
    
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
	    a list defining the map  S -> R
    Outputs
        :RingMap
	    the natural ring map  S -> R
    Description
     -- Text  
       --   Some words to say things. You can even use LaTeX $R = k[x,y,z]$. 
--
        Example
            R = GF(64)[x,y,z]/(x*y-z^2)
     	    S = GF(8)[a]
	    L = {x}
	    switchFieldMap(R,S,L)
	    
	   
        --Text
       	   -- More words, but don't forget to indent. 
	   
    --SeeAlso
    
    --Caveat
    
///


----- TESTS -----
TEST ///
K=GF 64;
(T,f) = fieldBaseChange(GF(8)[y], K);
assert(coefficientRing T === K)
///

TEST ///
g := switchFieldMap(GF(64)[x,y,z]/(x*y-z^2), GF(8)[a],{x})
assert(true)
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