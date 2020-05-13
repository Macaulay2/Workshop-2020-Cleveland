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
    "GeneratorMatrix",
    "ParityCheck",
    "ParityCheckRows",
    "ParityCheckMatrix",
    "Code",
    -- Families of Codes
    "cyclicMatrix",
    "quasiCyclicCode",
    -- Methods
    "field",
    "vectorSpace",
    --"codeDim",
    --"codeLength",
    "ambientSpace",
    "informationRate",
    "dualCode",
    "alphabet",
    "generic",
    "bitflipDecode",
    "MaxIterations",
    "shorten"
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
 
LinearCode = new Type of MutableHashTable

-- internal function to validate inputs:
rawLinearCode = method()
rawLinearCode(List) := LinearCode => (inputVec) -> (
    -- use externally facing functions to create list:	
    -- { AmbientModule, BaseField, Generators, ParityCheckRows, Code}
    
    -- use this function to validate inputs and provide warnings:
    
    -- check if "baseField" is a field, throw warning otherwise:
    if not isField(inputVec_1) then print "Warning: Working over non-field.";
   
    if inputVec_2 != {} then {
	-- check that all generating codewords are of the same length:
	if not all(inputVec_2, codeword -> length(codeword) == length(inputVec_2)_0) then error "Codewords not of same length.";
	
	-- coerce generators and generator matrix into base field, if possible:
	try {
	    newGens := apply(inputVec_2, codeword -> apply(codeword, entry -> sub(entry, inputVec_1)));
	    newGenMat := matrix(newGens);
	    } else {
	    error "Elements do not live in base field/ring.";
	    };
    } else {
	-- if generators and generator matrix were undefined:
	newGens = {};
	newGenMat = matrix({newGens});
    };
    
    if inputVec_3 != {} then {
	-- check that all parity check rows are of the same length:
	if not all(inputVec_3, parityrow -> length(parityrow) == length(inputVec_3)_0) then error "Parity check row not of same length.";
	
	-- coerce parity check rows and parity check matrix into base field, if possible:
	try {
	    newParRow := apply(inputVec_3, codeword -> apply(codeword, entry -> sub(entry, inputVec_1)));
	    newParMat := matrix(newParRow);
	    } else {
	    error "Elements do not live in base field/ring.";
	    };
    } else {
	newParRow = {};
	newParMat = matrix({newParRow});
    };
    
    -- coerce code matrix into base field:
    codeSpace := sub(inputVec_4,inputVec_1);
    
    
    return new LinearCode from {
        symbol AmbientModule => inputVec_0,
	symbol BaseField => inputVec_1,
        symbol Generators => newGens,
	symbol GeneratorMatrix => newGenMat,
	symbol ParityCheckRows  => newParRow,
	symbol ParityCheckMatrix =>  newParMat,
	symbol Code => codeSpace,
	symbol cache => {}
	}
    
    )

-- by default, assume that inputs are generators or generating matrices
-- set ParityCheck => true to have inputs be rows of parity check matrix:
linearCode = method(Options => {symbol ParityCheck => false})

linearCode(Module,List) := LinearCode => opts -> (S,L) -> (
    -- constructor for a linear code
    -- input: ambient vector space/module S, list of generating codewords
    -- outputs: code defined by submodule given by span of elements in L


    -- { AmbientModule, BaseField, Generators, GeneratorMatrix, ParityCheckRows, ParityCheckMatrix, Code }
    if opts.ParityCheck then {
	outputVec := {S, S.ring, {}, L, kernel matrix L};
	} else {
	outputVec =  {S, S.ring, L , {}, image matrix L};
	};
    
    return rawLinearCode(outputVec)
    
    )

linearCode(GaloisField,ZZ,List) := LinearCode => opts -> (F,n,L) -> (
    -- input: field, ambient dimension, list of generating codewords
    -- outputs: code defined by module given by span of elements in L
    
    -- ambient module F^n:
    S := F^n;

    if opts.ParityCheck then {
	outputVec := {S, F, {}, L, kernel matrix L};
	} else {
	outputVec =  {S, F, L , {}, image matrix L};
	};    
    
    return rawLinearCode(outputVec)
    
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


-- input: An [n,k] linear code C and an iteger i such that 1 <= i <= n.
-- output: A new code from C by selecting only those codewords of C having a zero as their 
--     i-th component and deleting the i-th component from these codewords. Thus, the resulting 
--     code will have length n - 1. 

shorten = method(TypicalValue => LinearCode)
shorten ( LinearCode, ZZ ) := LinearCode => ( C, i ) -> (
    local newL;
        
    newL = delete(0,apply(C.Generators, c -> if c#i == 0 then c else 0 ));
    newL = entries submatrix' ( matrix newL, {i} );
            
    return linearCode ( C.BaseField , newL )    
    )


-- Given an [n, k] code C and a set S of distinct integers { i1, ..., ir}, each of which lies in 
-- the range [1, n], construct a new code from C by selecting only those codewords of C having 
-- zeros in each of the coordinate positions i1, ..., ir, and deleting these components. Thus, 
-- the resulting code will have length n - r. 
shorten ( LinearCode, List ) := LinearCode => ( C, i ) -> (

    -- Branden will write this tomorrow. 
            
    )


------------------------------------------
------------------------------------------
-- Binary Operations
------------------------------------------
------------------------------------------

-- equality of linear codes
LinearCode == LinearCode := (C,D) -> ( 
    MC := matrix apply(C.Generators, a -> vector a );
    MD := matrix apply(D.Generators, a -> vector a );
    image MC == image MD
    )




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
    -- produce canonical form of the generating matrix:
    G := transpose groebnerBasis generators C.Code;
    G
    
    )


-*

Bitflip decode the codeword v relative to the parity check matrix H.

Example:
R=GF(2);
H := matrix(R, {
	{1,1,0,0,0,0,0},
	{0,1,1,0,0,0,0},
	{0,1,1,1,1,0,0},
	{0,0,0,1,1,0,0},
	{0,0,0,0,1,1,0},
	{0,0,0,0,1,0,1}});
v := vector transpose matrix(R, {{0,1,0,0,1,0,0}});
print(bitflipDecode(H,v));

*-
bitflipDecode = method(TypicalValue => List, Options => {MaxIterations => 100})
bitflipDecode(Matrix, Vector) := opts -> (H, v) -> (
    w := v;
    if(H*w == 0_(target H)) then(
	return entries w;
	);
    
    for iteration from 0 to (opts.MaxIterations)-1 do(
    	n := rank target H;
    	fails := positions(entries (H*w), i -> i==1);
    	failsRows := select(pairs entries H, i -> member(first i, set(fails)));
    	-- matrix representing only the homogenous eqns that fail
    	failSubgraph := lift(matrix toList(apply(failsRows, i -> last i)),ZZ);
    	oneVec := vector apply(entries (0_(target failSubgraph)), i -> 1);
    	-- number of times each variable appears in a failing equation
    	numFails := entries (transpose(failSubgraph)*oneVec);
    	toFlip := positions(numFails, n -> n == (max numFails));
    	flipVec := sum apply(toFlip, i -> vector ((entries basis source H)#i));
    	w = flipVec+w;
    
	
	if(H*w == 0_(target H)) then(
	    return entries w;
	    );
    	);
    
    return {};
    );
    


------------------------------------------
------------------------------------------
-- Tests
------------------------------------------
------------------------------------------


TEST ///
-- Equality Test
F = GF(2)
codeLen = 10
codeDim = 4
L = apply(toList(1..codeDim),j-> apply(toList(1..codeLen),i-> random(F)))
H = L|L
C = linearCode(F,codeLen,H)
D = linearCode(F,codeLen,L)
assert( C == D)
///


TEST ///
-- bitflipDecode
-- Make sure that it only outputs codewords.
R := GF(2);
H := random(R^10, R^15)
for i from 1 to 50 do(
    v := vector (for i from 1 to 15 list(random(R)));
    w := bitflipDecode(H, v);
    if(w != {}) then (
    	assert(H*(vector w) == 0_(target H));
    );
);
///

TEST///
-- shorten test
F = GF(2)
codeLen = 10
codeDim = 4
L = {{0, 1, 0, 0, 0, 0, 0, 0, 0, 0}, {0, 0, 1, 0, 1, 1, 0, 1, 0, 0}, {1, 1, 0, 0, 0, 1, 0, 0, 1, 0}, {1, 0, 0, 1, 0, 0, 0, 1, 1, 1}}
H = L|L

C2 = linearCode(F,codeLen,H)
C3 = linearCode(F,codeLen,L)

shortL = {{0, 1, 0, 0, 0, 0, 0, 0, 0}, {0, 0, 1, 1, 1, 0, 1, 0, 0}, {1, 1, 0, 0, 1, 0, 0, 1, 0}}

assert( numColumns ( C2.GeneratorMatrix ) == numColumns (shorten( C2, 3)).GeneratorMatrix + 1 )
assert( numColumns ( C3.GeneratorMatrix ) == numColumns (shorten( C3, 3)).GeneratorMatrix + 1 )
assert( shorten( C2, 3 ) == linearCode(F, shortL) )
assert( shorten( C3, 3 ) == linearCode(F, shortL) )
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
    Key => {bitflipDecode, (bitflipDecode,Matrix, Vector)},
    Headline => "Uses the Gallager bit flip algorithm to decode a codeword given a parity check matrix.",
    Usage => "bitflipDecode(H,v)",
    Inputs => {
	"H" => Matrix => {"The parity check matrix."},
	"v" => Vector => {"The codeword to decode."}	
	},
    Outputs => {
	List => {}
	},
    "The matrix H and the vector v must have entries in GF(2). ",
    "Returns the empty list if MaxIterations is exceeded.",
    EXAMPLE {
	"R=GF(2);",
	"H := matrix(R, {{1,1,0,0,0,0,0},{0,1,1,0,0,0,0},{0,1,1,1,1,0,0},{0,0,0,1,1,0,0},{0,0,0,0,1,1,0},{0,0,0,0,1,0,1}});",
	"v := vector transpose matrix(R, {{1,0,0,1,0,1,1}});",
	"bitflipDecode(H,v)"
	}
    }
document {
    Key => MaxIterations,
    Headline => "Specifies the maximum amount of iterations before giving up. Default is 100.",
    TT "MaxIterations", " -- Specifies the max iterations.",
    PARA{},
    "This symbol is provided by the package ", TO CodingTheory, "."
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

