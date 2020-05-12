-- -*- coding: utf-8 -*-
newPackage(
	"CodingTheory",
    	Version => "1.0", 
    	Date => "May 11, 2020",
    	Authors => {
	     {Name => "Hiram Lopez", Email => "h.lopezvaldez@csuohio.edu"},
	     {Name => "Gwyn Whieldon", Email => "gwyn.whieldon@gmail.com"}
	     },
    	HomePage => "https://academic.csuohio.edu/h_lopez/",
    	Headline => "a package for coding theory in M2",
	AuxiliaryFiles => false, -- set to true if package comes with auxiliary files,
	Configuration => {},
        DebuggingMode => false,
	PackageImports => { },
        PackageExports => { }
	)

-- Any symbols or functions that the user is to have access to
-- must be placed in one of the following two lists

export {
    -- toy functions as examples
    "firstFunction",
    "secondFunction",
    "MyOption",
    -- Types and Constructors
    "LinearCode",
    "linearCode",
    "AmbientModule",
    "Generators",
    "Code",
    -- Methods
    "coefVec",
    "getGoppaParity"
    }
exportMutable {}

firstFunction = method(TypicalValue => String)
firstFunction ZZ := String => n -> (
	if n == 1
	then "Hello, World!"
	else "D'oh!"	
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

------------------------------------------
------------------------------------------
-- Data Types and Constructors
------------------------------------------
------------------------------------------

-- Use this section to add basic types and
-- constructors for error correcting codes
 
LinearCode = new Type of HashTable
linearCode = method(Options => {})


linearCode(Ring,ZZ,List) := LinearCode => opts -> (R,n,L) -> (
    -- sample (possible) constructor for a linear code
    -- input: ring, ambient dimension, list of generating codewords
    -- outputs: module given by span of elements in L
    
    -- ambient module R^n:
    S := R^n;
    
    
    new LinearCode from {
	symbol AmbientModule => S,
	symbol Generators => apply(L, v-> vector(v)),
	symbol Code => image transpose matrix apply(L, v-> vector(v))
	}
    
    )

linearCode(ZZ,ZZ,ZZ,List) := LinearCode => opts -> (p,q,n,L) -> (
    -- Constructor for codes over Galois fields
    -- input: prime p, exponent q, dimension n, list of generating codewords L
    -- output module given by span of elements in L
    
    -- Galois Field:
    R := GF(p,q);
    
    linearCode(R,n,L)
    
    )

net LinearCode := c -> (
     "Code: " | net c.Code
     )
toString LinearCode := c -> toString c.Generators
 
------------------------------------------
------------------------------------------
-- Methods
------------------------------------------
------------------------------------------


-- Returns the coefficient vector of a finite field element,
-- viewed as a polynomial in the primitive element.
coefVec = method(TypicalValue => List)
coefVec (RingElement) := elt -> (
    R := ring(elt);
    alpha := (ambient R)_0;
    p := char R;
    pows := for i from 0 to p list(alpha^i);
    (M,C) := coefficients(lift(elt, ambient R), Monomials => pows);
    return vector flatten entries C;
    )

-*
Generates a parity check matrix for the Goppa code given by goppaPoly and defSet. 
Based off of this implemenation from SageMath:
https://github.com/sagemath/sage/blob/6db1a26f5e25ac32752e1151514e3e38c7bde98c/src/sage/coding/goppa_code.py#L38

Example:  

R = GF(2^3)
a = (vars R)_(0,0)
L = {0_R}|(for i from 0 to q - 2 list(a^i))
G = a^2 + a + 1
getGoppaParity(G, L)
*-

getGoppaParity = method(TypicalValue => LinearCode)
getGoppaParity (RingElement, List) := (goppaPoly, defSet) -> (
                    
    n := length(defSet);
    R := ring(goppaPoly);
    G := lift(goppaPoly, ambient R);
    d := first degree G;
    alpha := first gens ring(G);
    D := defSet;

    for i from 0 to length defSet-1 do(
	if (sub(G, {alpha => defSet#i})) == 0_(ambient R) then(
	    error "defSet cannot contain zeroes of goppaPoly."
	    );
	);
    
    h := for i from 0 to n-1 list(
	val := (sub(G, {alpha => D#i}))^(-1);
	coefVec(val)
	);
    
    bottom := for t from 1 to d-1 list(
    	for i from 0 to n-1 list(
	    val := (sub(G, {alpha => D#i}))^(-1);
	    val = val*((D#i)^t);
	    coefVec(val)
	    )
    	);    
    
    mat := {h} | bottom;
    mat = apply(mat, block -> matrix block);
    mat = fold((a,b)-> a || b, mat);

    return new LinearCode from {
	symbol AmbientModule => R,
	symbol Generators => apply(entries mat, v-> vector(v)),
	symbol Code => image mat
	};
    );


-- Use this section to add methods that
-- act on codes. Should use this section for
-- writing methods to convert between 
-- different Types of codes
 

beginDocumentation()
document { 
	Key => CodingTheory,
	Headline => "a package for coding theory in M2",
	EM "CodingTheory", " is a package to provide both
	basic coding theory objects and routines, and methods
	for computing invariants of codes using commutative 
	algebra techniques.."
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
	"This function is provided by the package ", TO CodingTheory, ".",
	EXAMPLE {
		"firstFunction 1",
		"firstFunction 0"
		}
	}
document {
	Key => secondFunction,
	Headline => "a silly second function",
	"This function is provided by the package ", TO CodingTheory, "."
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
     "This symbol is provided by the package ", TO CodingTheory, "."
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
  
       
end

-- Here place M2 code that you find useful while developing this
-- package.  None of it will be executed when the file is loaded,
-- because loading stops when the symbol "end" is encountered.

installPackage "CodingTheory"
installPackage("CodingTheory", RemakeAllDocumentation=>true)
check CodingTheory

-- Local Variables:
-- compile-command: "make -C $M2BUILDDIR/Macaulay2/packages PACKAGES=CodingTheory pre-install"
-- End: