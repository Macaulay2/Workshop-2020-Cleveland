-- -*- coding: utf-8 -*-

newPackage(
        "InvariantRings",
        Version => "2.0", 
        Date => "May 13, 2020",
        Authors => {
	    {Name => "Luigi Ferraro", 
		 Email => "ferrarl@wfu.edu", 
		 HomePage => "http://users.wfu.edu/ferrarl/"
		 },
             {Name => "Federico Galetto", 
		 Email => "f.galetto@csuohio.edu", 
		 HomePage => "https://math.galetto.org"
		 },
             {Name => "Francesca Gandini", 
		 Email => "fra.gandi.phd@gmail.com", 
		 HomePage => "https://sites.google.com/a/umich.edu/gandini/home"
		 },
	     {Name => "Hang Huang", 
		 Email => "hhuang235@tamu.edu", 
		 HomePage => "https://math.tamu.edu/~hhuang"
		 },
	     {Name => "Matthew Mastroeni", 
		 Email => "mmastro@okstate.edu", 
		 HomePage => "https://mnmastro.github.io/"
		 },
             {Name => "Xianglong Ni", 
		 Email => "xlni@berkeley.edu", 
		 HomePage => "https://math.berkeley.edu/~xlni/"}
             },
        Headline => "invariants of group actions",
	AuxiliaryFiles => true,
        DebuggingMode => true
        )


-- TO DO: 1. Finish documenting all exported/overloaded functions.
--    	  2. Internally document with comments all unexported functions.
--    	  3. The function "weights" has 3 different documentation entries.
--    	     Merge them into a single entry.

-- Record any symbols or functions (except "net") used in each file below.
-- Comment out the name of the function/symbol if it is not exported.

-- Type names must be exported if they are used in the documentation
-- of an overloaded function.

export {
--InvariantRings.m2
    -- dim    	      	      	  -- overloaded, documented
    "GroupAction",    	      	  -- exported type name, documented
    -- ring    	       	       	  -- overloaded, documented

--FiniteGroups.m2 
    -- cyclicFactors	    	  -- unexported
    "finiteAction",    	       	  -- documented
    "FiniteGroupAction",    	  -- exported type name, documented
    -- generateGroup	    	  -- unexported, internally documented
    -- generators    	     	  -- overloaded, documented
    "group",	    	    	  -- documented
    "isAbelian",    	    	  -- documented
    -- numgens	      	      	  -- overloaded, documented
    "permutationMatrix",          -- documented
    -- relations    	    	  -- overloaded
    "schreierGraph",	    	  -- documented
    "words",    	       	  -- documented

--AbelianGroups.m2
    "cyclicFactors",
    -- degreesRings    	       	  -- overloaded
    "DiagonalAction",	     	  -- exported type name, documented
    "diagonalAction",	     	  -- documentation needs some work to explain different usages
    "equivariantHilbert",    	  -- cache table key
    -- equivariantHilbertPartial  -- unexported
    -- equivariantHilbertRational -- unexported
    "equivariantHilbertSeries",   -- documented   
    -- numgens	      	      	  -- overloaded, documented
    -- rank    	       	       	  -- overloaded
    "weights",	      	      	  -- documented

--LinearlyReductiveGroups.m2    
    "actionMatrix",    	       	  -- documented
    "groupIdeal",    	     	  -- documented
    "hilbertIdeal",    	       	  -- documented
    "linearlyReductiveAction",	  -- documented
    "LinearlyReductiveAction",	  -- exported type name
    
--Invariants.m2 
    "Abelian",	    	          -- Strategy option for isInvariant   
    "action",	     	     	  -- documented   
    -- ambient	      	      	  -- overloaded
    "definingIdeal",              -- documented
    "DegreeBound",    	      	  -- option for invariants
    -- generators    	     	  -- overloaded, documented
    -- hilbertSeries	    	  -- overloaded
    "invariants",    	     	  -- documented only for TorusAction, FiniteAbelianAction, LinearlyReductiveAction
    "invariantRing",	    	  -- documented
    "isInvariant",    	      	  -- documented
    -- manualTrim    	     	  -- unexported (why is this a method if it's not exported?)
    "Nonabelian",     	          -- Default strategy option for isInvariant
    -- presentation    	       	  -- overloaded
    "reynoldsOperator",	       	  -- documented   
    "LinearAlgebra",	       	  -- Option for invariants
    "RingOfInvariants",	       	  -- exported type name
    "UseNormaliz",    	      	  -- Strategy option for invariants 
    "UsePolyhedra",    	      	  -- Strategy option for invariants    	

--Hawes.m2    
    "molienSeries",    	       	  -- documented
    "primaryInvariants",    	  -- documented
    "secondaryInvariants",    	  -- documented
    "Dade",    	       	       	  -- option for primaryInvariants
    "DegreeVector",    	       	  -- option for primaryInvariants
    "PrintDegreePolynomial"    	  -- option for secondaryInvariants
    }
--exportMutable {}


needsPackage("Elimination")
needsPackage("Normaliz")
needsPackage("Polyhedra")

GroupAction = new Type of HashTable


-------------------------------------------
--- GroupAction methods -------------------
-------------------------------------------

ring GroupAction := Ring => G -> G.ring

dim GroupAction := ZZ => G -> dim ring G


-------------------------------------------
--- LOAD AUXILIARY FILES ------------------
-------------------------------------------

load "./InvariantRings/FiniteGroups.m2"

load "./InvariantRings/AbelianGroups.m2"

load "./InvariantRings/LinearlyReductiveGroups.m2"

load "./InvariantRings/Invariants.m2"

-- code ported from Hawes' version 1.1.0
load "./InvariantRings/Hawes.m2"

beginDocumentation()

load "./InvariantRings/InvariantRingsDoc.m2"

load "./InvariantRings/FiniteGroupsDoc.m2"

load "./InvariantRings/AbelianGroupsDoc.m2"

load "./InvariantRings/LinearlyReductiveGroupsDoc.m2"

load "./InvariantRings/InvariantsDoc.m2"

load "./InvariantRings/HawesDoc.m2"

-- TESTS

load "./InvariantRings/Tests.m2"


end


-- Here place M2 code that you find useful while developing this
-- package.  None of it will be executed when the file is loaded,
-- because loading stops when the symbol "end" is encountered.


restart
uninstallPackage "InvariantRings"
installPackage "InvariantRings"
check InvariantRings

B = QQ[a,b,c,d]
A = ideal(a*d - b*c - 1)
SL2std = matrix{{a,b},{c,d}}
R1 = QQ[x_1..x_2]

time V1 = linearlyReductiveAction(A,SL2std,R1)
time hilbertIdeal V1


restart
loadPackage "InvariantRings"
R1 = QQ[a_1..a_3]
W = matrix{{1,0,1},{0,1,1}}
L = {3,3}
T = finiteAbelianAction(L,W,R1)
R1^T
invariantRing T

S = QQ[z]
A = ideal(z^2 - 1)
M = matrix{{(1+z)/2, (1-z)/2},{(1-z)/2,(1+z)/2}}
R = QQ[a,b]
X = linearlyReductiveAction(A,M,R)
isInvariant(a,X)
