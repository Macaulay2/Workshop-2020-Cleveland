-- -*- coding: utf-8 -*-
newPackage(
	"CodingTheory",
    	Version => "1.0", 
    	Date => "May 11, 2020",
    	Authors => {
	     {Name => "Hiram Lopez", Email => "h.lopezvaldez@csuohio.edu"},
	     {Name => "Gwyn Whieldon", Email => "gwyn.whieldon@gmail.com"},
	     {Name => "Taylor Ball", Email => "trball13@gmail.com"}
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
    "BaseField",
    "Generators",
    "Code",
<<<<<<< HEAD
=======
    -- Families of Codes
    "cyclicMatrix",
    "quasiCyclicCode",
    "getGoppaParity",
    -- Methods
    "coefVec",
    "field",
    "vectorSpace",
    --"codeDim",
    --"codeLength",
    "ambientSpace",
    "informationRate",
    "dualCode",
    "alphabet",
    "generic"
>>>>>>> CodingTheory
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

linearCode(Module,List) := LinearCode => opts -> (S,L) -> (
    -- constructor for a linear code
    -- input: ambient vector space/module S, list of generating codewords
    -- outputs: code defined by submodule given by span of elements in L
    
    if not isField(S.ring) then print "Warning: Codes over non-fields unstable.";
    
    -- note: check that codewords can be coerced into the ambient module and
    -- have the correct dimensions:
    try {
	newL := apply(L, codeword -> apply(codeword, entry -> sub(entry,S.ring)));
	    } else {
	error "Elements in L do not live in base field of S.";
	    };
     
    new LinearCode from {
	symbol AmbientModule => S,
	symbol BaseField => S.ring,
	symbol Generators => newL,
	symbol Code => image matrix apply(newL, v-> vector(v)),
	symbol cache => {}
	}
    
    )

linearCode(GaloisField,ZZ,List) := LinearCode => opts -> (F,n,L) -> (
    -- input: field, ambient dimension, list of generating codewords
    -- outputs: code defined by module given by span of elements in L
    
    -- ambient module F^n:
    S := F^n;
    
    --verify all tuples in generating set L have same length:
    if not all(L, codeword -> #codeword == #L_0) then error "Codewords not of same length.";
     
    new LinearCode from {
	symbol AmbientModule => S,
	symbol BaseField => F,
	 -- need to coerce generators into *this* GF(p,q):
	symbol Generators => apply(L, codeword -> apply(codeword, entry -> sub(entry,F))),
	symbol Code => image matrix apply(L, v-> vector(v)),
	symbol cache => {}
	}
    
    )

linearCode(GaloisField,List) := LinearCode => opts -> (F,L) -> (
    -- input: field, list of generating codewords
    -- outputs: code defined by module given by span of elements in L
    
    -- calculate length of code via elements of L:
    n := # L_0;
        
    linearCode(F,n,L)
    
    )

linearCode(ZZ,ZZ,ZZ,List) := LinearCode => opts -> (p,q,n,L) -> (
    -- Constructor for codes over Galois fields
    -- input: prime p, exponent q, dimension n, list of generating codewords L
    -- output: code defined by module given by span of elements in L
    
    -- Galois Field:
    R := GF(p,q);
    
    linearCode(R,n,L)
    
    )


linearCode(Module,Module) := LinearCode => opts -> (S,V) -> (
    -- constructor for a linear code
    -- input: ambient vector space/module S, submodule V of S
    -- outputs: code defined by submodule V
    
    if not isField(S.ring) then print "Warning: Codes over non-fields unstable.";
     
    new LinearCode from {
	symbol AmbientModule => S,
	symbol BaseField => S.ring,
	symbol Generators => try V.gens then V.gens else gens V,
	symbol Code => V,
	symbol cache => {}
	}
    
    )

linearCode(Module) := LinearCode => opts -> V -> (
    -- constructor for a linear code
    -- input: some submodule V of S
    -- outputs: code defined by submodule V
    
    linearCode(ambient V, V)
    
    )

linearCode(Matrix) := LinearCode => opts -> M -> (
    -- constructor for a linear code
    -- input: a generating matrix for a code
    -- output: code defined by the columns of M
    
    new LinearCode from {
	symbol AmbientModule => M.target,
	symbol BaseField => M.ring,
	symbol Generators => entries transpose M,
	symbol Code => image M,
	symbol cache => {}
	}
    
    )

net LinearCode := c -> (
     "Code: " | net c.Code
     )
toString LinearCode := c -> toString c.Generators


------------------------------------------
------------------------------------------
-- Binary Operations
------------------------------------------
------------------------------------------

-- equality of linear codes
LinearCode == LinearCode := (C,D) -> ( C.Code == D.Code ) 




------------------------------------------
------------------------------------------
-- Families of Codes
------------------------------------------
------------------------------------------

-- Use this section to add methods that 
-- construct families of codes

------------------------------------------------------
-- Added helper functions to produce cyclic matrices:
------------------------------------------------------
cyclicMatrix = method(TypicalValue => Matrix)
cyclicMatrix(List) := Matrix => v -> (
    -- constructs the cyclic matrix with first
    -- row given by v
    
    -- calculate number of rows/columns:
    ndim := # v;
    
    -- produce cyclic matrix of right-shifts with
    -- first row given by v:
    matrix(apply(toList(0..ndim-1), i -> apply(toList(0..ndim-1),j -> v_((j-i)%ndim))))
    
    )

cyclicMatrix(GaloisField,List) := Matrix => (F,v) -> (
    -- constructs the cyclic matrix with first
    -- row given by v, coercing elements into F:
    
    try {
	-- attempt to coerce all entries into
	-- same field, if necessary:
	newV := apply(v, entry -> sub(entry,F));
	} else {
	-- otherwise, throw error:
	error "Elements of input cannot be coerced into same field.";
	}; 
    
    cyclicMatrix(newV) 
    
    )


quasiCyclicCode = method(TypicalValue => LinearCode)

quasiCyclicCode(GaloisField,List) := LinearCode => (F,V) -> (
        
    -- produce cyclic matrices with each v in V as first row:
    cyclicMatrixList := apply(V, v-> cyclicMatrix(F,v)); 
    
    -- vertically concatenate all of the codewords in blocks
    -- of our quasi-cyclic code:
    
    linearCode(fold((m1,m2) -> m1 || m2, cyclicMatrixList))
    
    )

quasiCyclicCode(List) := LinearCode => V -> (
    -- constructs a cyclic code from a 
    -- list of lists of  elements in some field F:
    
    -- check field that elements live over:
    baseField := class V_0_0;
    
    try quasiCyclicCode(baseField,V) else error "Entries not over a field."
    
    )
 

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

 
--input: A linear code C
--output: The field C is a code over
--description: Given a linear code, the function returns the field C is a code over
field = method(TypicalValue => Ring)
field LinearCode := Ring => C -> (
    return C.BaseField
    )
 

--input: A linear code C
--output: The vector space spanned by the generators of C
vectorSpace = method(TypicalValue => Module)
vectorSpace LinearCode := Module => C -> (
    return C.Code
    )

--input: A linear code C
--output: The ambient vector space the code is a subspace of
ambientSpace = method(TypicalValue => Module)
ambientSpace LinearCode := Module => C -> (
    return C.AmbientModule
    )

--input: A linear code C
--output: The vector space dimension of the ambient vector space 
--C is a subspace of
length LinearCode := ZZ  => C -> (
    return rank(C.AmbientModule)
    )

--input: A linear code C
--output: The vector space dimension of the subspace given by the
--span of the generators of C
dim LinearCode := ZZ => C -> (
    --return length C.Generators; (generating set may not be minimal)
    return rank generators C.Code
    )

--input: A linear code C
--output: The ratio (dim C)/(length C)
informationRate = method(TypicalValue => QQ)
informationRate LinearCode := QQ => C -> (
    return (dim C)/(length C);
    )

--input: A linear code C
--output: the number of codewords in C
size LinearCode := ZZ => C -> (
    return (dim C)^(C.BaseField.order)
    )


dualCode = method(TypicalValue => LinearCode)
dualCode(LinearCode) := LinearCode => C -> (
    -- creates dual code to code C
    -- defn: the dual C^ is the code given by all c'
    -- such that c'.c == 0 for all c in C.
    linearCode(dual cokernel gens C.Code)
    )

alphabet = method(TypicalValue => List)
alphabet(LinearCode) := List => C -> (
    -- "a" is the multiplicative generator of the
    -- field that code C is over
    a := C.BaseField.generators_0;
    
    -- take 0, and compute non-zero elements of C.BaseField:
    alphaB := {sub(0,C.BaseField)} | apply(toList(1..(C.BaseField.order-1)), i-> a^i);
    
    -- return this alphabet:
    alphaB    
    
    )

generic = method(TypicalValue => LinearCode)
generic(LinearCode) := LinearCode => C -> (
    linearCode(C.AmbientModule)
    )

parityCheck = method(TypicalValue => Matrix)

parityCheck(LinearCode) := Matrix => C -> (
    
    )



------------------------------------------
------------------------------------------
-- Tests
------------------------------------------
------------------------------------------

-- Equality Test
TEST ///
F = GF(2)
codeLen = 10
codeDim = 4
L = apply(toList(1..codeDim),j-> apply(toList(1..codeLen),i-> random(F)))
H = L|L
C = linearCode(F,codeLen,H)
D = linearCode(F,codeLen,L)
assert( C == D)
///



------------------------------------------
------------------------------------------
-- Documentation
------------------------------------------
------------------------------------------


beginDocumentation()
document { 
	Key => CodingTheory,
	Headline => "a package for coding theory in M2",
	PARA {
	    EM "CodingTheory", " is a package to provide both
	basic coding theory objects and routines, and methods
	for computing invariants of codes using commutative 
	algebra techniques.."
	},
        
	PARA { "This package currently provides constructors for
	linear codes, evaluation codes, and a few methods for each."
	}
	}
    
document {
    Key => {linearCode, (linearCode,Module), (linearCode,GaloisField,List), (linearCode,Module,List)},
    Headline => "linear code constructors",
    Usage => "linearCode(V)\nlinearCode(F,L)\nlinearCode(F,n,L)\nlinearCode(S,V)",
    "These constructors are provided by the package ", TO CodingTheory, ".",
    EXAMPLE {
	"F = GF(2,4);codeLen = 7;codeDim = 3;",
        "L = apply(toList(1..codeDim),j-> apply(toList(1..codeLen),i-> random(F))); VerticalList(L)",
	"C = linearCode(F,L)"
	}
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

