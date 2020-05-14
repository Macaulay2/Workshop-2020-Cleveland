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
    -- Types and Constructors
    "generatorToParityCheck",
    "parityCheckToGenerator",
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
    "HammingCode",
    -- LRC codes
    "TargetParameters",
    "targetParameters",
    "LRCencoding",
    "getEncodingPolynomial",
    "getCoefficientPolynomial",
    --"goodPolynomial",
    "getGroupAnnihilatorPolynomial",
    "Alphabet",
    "Length",
    "Dimension",
    "Locality",
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

------------------------------------------
------------------------------------------
-- Data Types and Constructors
------------------------------------------
------------------------------------------

------------------------------------------
-- Helper functions for constructors:
------------------------------------------

findPivots = method(TypicalValue => List)
findPivots(Matrix) := List => M -> (
    -- if the reduced basis for the code does NOT
    -- have an identity matrix on the right, 
    -- find positions of each column:
    
    colsOfM := entries transpose M;
    
    -- extract (ordered) positions of standard basis vectors:
    return apply(entries id_(M.target), col -> position(colsOfM, colM -> colM == col))
    
    )

permuteMatrixColumns = method(TypicalValue => Matrix)
permuteMatrixColumns(Matrix,List) := (M,P) -> (
    -- given a list P representing a permutation,
    -- permute the columns via P:

    return transpose matrix((entries transpose M)_P)
    
    
    
    )

permuteMatrixRows = method(TypicalValue => Matrix)
permuteMatrixRows(Matrix,List)  := (M,P) -> (
    -- given a list P representing a permutation,
    -- permute the columns via P:
    return matrix((entries M)_P)
    )


permuteToStandardForm = method()
permuteToStandardForm(Matrix) := M -> (
    -- input: matrix M
    -- output: matrix P*M (permuted to move pivots to right identity block) and permutation P used
    
    pivotPositions := findPivots(M);
    
    P := select(toList(0..rank M.source -1), i-> not member(i,pivotPositions)) | pivotPositions;
    
    return {permuteMatrixColumns(M,P),P}
    
    )




generatorToParityCheck = method(TypicalValue => Matrix)
generatorToParityCheck(Matrix) := Matrix => M -> (
    -- this function assumes M is of full rank:
    if rank M != min(rank M.source, rank M.target) then error "Matrix M is not of full rank.";
    
    -- produce canonical form of the generating matrix:
    G := transpose groebnerBasis transpose M;
    
    -- save permutation of G to standard form and permutation used:
    GandP := permuteToStandardForm(M);    
    
    -- update G to use this correct version, save P to variable:
    Gred  := GandP_0;
    P := GandP_1;
    
    
    -- this code assumes that generator matrix
    -- can be put into standard form without any
    -- swapping of columns:
    
    -- take (n-k) columns of standard generating matrix above:
    redG := Gred_{0..(rank Gred.source - rank Gred -1)};
    
    -- vertically concatenate an identity matrix of rank (n-k),
    -- then transpose :
    return permuteMatrixColumns(transpose (id_(redG.source) || -redG),inversePermutation(P))
    
    )



--The example @henry-chimal noted of a rank deficient code (a generator matrix with repeats) is corrected by this. The user inputted generator or parity check matrix will not be altered UNLESS the matrix is rank deficient, in which case a reduced presentation will be computed and returned.

parityCheckToGenerator = method(TypicalValue => Matrix)
parityCheckToGenerator(Matrix) := Matrix => M -> (
    return(transpose generators kernel M)
    )

-- If generator or parity check is not full rank, 
-- choose a subset of rows that are generators:
reduceMatrix = method(TypicalValue => Matrix)
reduceMatrix(Matrix) := Matrix => M -> (
    return transpose groebnerBasis transpose M
    )

reduceRankDeficientMatrix = method(TypicalValue => Matrix)
reduceRankDeficientMatrix(Matrix) := Matrix => M -> (
    -- check if matrix is of full rank, otherwise return reduced:
    if (rank M == min(rank M.source,rank M.target)) then {
	return M
	} else return reduceMatrix(M)
    )



-- Use this section to add basic types and
-- constructors for error correcting codes
 
LinearCode = new Type of HashTable

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
	print("in parity check case");
    } else {
	newParMat = generatorToParityCheck(reduceMatrix(newGenMat));
	newParRow = entries newParMat ;
    };

    -- compute generating matrix from parity check matrix, if not already set:
    if newGens == {} then {
        newGenMat = parityCheckToGenerator(newParMat);
	newGens = entries newGenMat;
    };
    
    -- coerce code matrix into base field:
    codeSpace := if (reduceMatrix(generators inputVec_4) == generators inputVec_4) then sub(inputVec_4,inputVec_1) else image groebnerBasis inputVec_4;
    
    
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
	outputVec =  {S, S.ring, L , {}, image transpose matrix L};
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
	outputVec =  {S, F, L , {}, image transpose matrix L};
	};
    
    return rawLinearCode(outputVec)
    
    )

linearCode(GaloisField,List) := LinearCode => opts -> (F,L) -> (
    -- input: field, list of generating codewords
    -- outputs: code defined by module given by span of elements in L
    
    -- calculate length of code via elements of L:
    n := # L_0;
        
    linearCode(F,n,L,opts)
    
    )

linearCode(ZZ,ZZ,ZZ,List) := LinearCode => opts -> (p,q,n,L) -> (
    -- Constructor for codes over Galois fields
    -- input: prime p, exponent q, dimension n, list of generating codewords L
    -- output: code defined by module given by span of elements in L
    
    -- Galois Field:
    R := GF(p,q);
    
    linearCode(R,n,L)
    
    )


linearCode(Module) := LinearCode => opts -> V -> (
    -- constructor for a linear code
    -- input: some submodule V of S
    -- outputs: code defined by submodule V
    
    -- produce a set of generators for the specified submodule V:
    generatorMatrix := transpose generators V;
    
    outputVec := {generatorMatrix.source, generatorMatrix.ring, entries generatorMatrix, {}, V};
    
    rawLinearCode(outputVec)
    
    )

linearCode(Matrix) := LinearCode => opts -> M -> (
    -- constructor for a linear code
    -- input: a generating matrix for a code
    -- output: if ParityCheck => true then code defined by kernel of M
    --         if ParityCheck => false then code defined by rows of M
    

    if opts.ParityCheck then {
	outputVec := {M.source, M.ring, {}, entries M, kernel M};
	} else {
	outputVec =  {M.target, M.ring, entries M, {}, image transpose M};
	};
    
    rawLinearCode(outputVec)
      
    )

net LinearCode := c -> (
     "Code with Generator Matrix: " | net c.GeneratorMatrix
     )
toString LinearCode := c -> toString c.Generators



------------------------------------------
------------------------------------------
-- Binary Operations
------------------------------------------
------------------------------------------

-- mathematical equality of linear codes
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

HammingCode = method(TypicalValue => LinearCode)

HammingCode(ZZ,ZZ) := LinearCode => (q,r) -> (
        
    -- produce Hamming code
    -- q is the size of the field
    -- r is the dimension of the dual
    K:=GF(q);
    -- setK is the set that contains all the elements of the field
    setK:=set(  {0}| apply(toList(1..q-1),i -> K_1^i));
    -- C is the transpose of the parity check matrix of the code. Its rows are the the points of the
    -- projective space P(r-1,q)
    j:=1;
    C:= matrix(apply(toList(1..q^(r-j)), i -> apply(toList(1..1),j -> 1))) | matrix apply(toList(toList setK^**(r-j)/deepSplice),i->toList i);
    for j from 2 to r do C=C|| matrix(apply(toList(1..q^(r-j)), i -> apply(toList(1..(j-1)),j -> 0))) | matrix(apply(toList(1..q^(r-j)), i -> apply(toList(1..1),j -> 1))) | matrix apply(toList(toList setK^**(r-j)/deepSplice),i->toList i);
	
    -- The Hamming code is defined by its parity check matrix
    linearCode(transpose C, ParityCheck => true)
    )

-*
Example:
HammingCode(2,3)
ParityCheckMatrix => | 1 1 1 1 0 0 0 |
                     | 0 1 0 1 1 1 0 |
                     | 0 1 1 0 0 1 1 |
*-



------------------    Matt
----------------------------------------------------------
-- Use this section to add basic types and constructors
--  for             LRC CODES
----------------------------------------------------------

TargetParameters = new Type of HashTable

targetParameters = method(Options => {})
targetParameters (ZZ,ZZ,ZZ,ZZ) := TargetParameters => opts -> (q,n,k,r) -> (
    -- contructor for the target parameters of an LRC code over a finite field
    -- input:   alphabet size q, target code length n, dimension k, and locality r
    -- output:  a hashtable containing the target parameters of the LRC code to be constructed
     -- note: check that n less than or equal to q and if the symbols of A lie in F
    if not n<=q then print "Warning: construction requires that target length <= field size.";
    
    
    --verify that target dimension is divisible by locality
    if not k%r==0 then error "target dimension is not divisible by target locality";
    
    new TargetParameters from {
	symbol Alphabet => toList(0..q-1),
	symbol Length => n,
	symbol Dimension => k,
	symbol Locality => r,
	symbol cache => {}
	}
    )


------------------------ -------------
--     Helper functions for constructing 
--             LRC CODES
-------------------------------

 
LRCencoding = method(TypicalValue => Module)
LRCencoding(TargetParameters,List,RingElement) := Module => (p,A,g) -> (
    -- generates an LRC code
    -- input:   the target parameters p, a partition of n symbols from the alphabet, and a good 
    --                     polynomial for the partition
    -- output:  an LRC with the desired target parameters as a module
    
    -- we need a set of generators for the Ambient Space containing our information vectors that will,
    --   be encoded, and then we generate their encoding polynomials
    x:=symbol x;
    R:=GF(#p.Alphabet);
    Anew:=apply(A,i->apply(i,j->sub(j,R)));
    generatorS:=apply((entries gens (R)^(p.Dimension),i->apply(i,j->sub(j,R))));
    encodingPolynomials:=apply(generatorS,i->(getEncodingPolynomial(p,i,g)));
    informationSymbols:=flatten Anew;
    
    
    -- we evaluate each encoding polynomial at each of the symbols in A
    listOfGens:=apply(encodingPolynomials,i->apply(informationSymbols,j->sub(i[j],R)));
    
    --should check that the evaluation of each generator in listOfGens over the entries of each codeword 
    -- returns the same number of distinct images as there are subsets in the partition A.
    setSizes:=apply(listOfGens,i-># set apply(i, j-> sub(sub(g[j],R),ZZ)));
    if not all (setSizes, Sizes-> Sizes<=#Anew) then error "Something went wrong";
    
    linearCode((GF(#p.Alphabet)),(p.Length),apply(listOfGens,i->apply(i,j->lift(j,ZZ))))
    
    )


---------------------------------------------
--   ENCODING POLYNOMIALS FOR LRC CODES    --
---------------------------------------------

getEncodingPolynomial = method(TypicalValue => RingElement)
getEncodingPolynomial (TargetParameters,List,RingElement) := RingElement => (p,infVec,g) -> (
      -- generates the encoding polynomial for an LRC code
      -- input:    the TargetParameters hash table p, a list infVec in F^k, a good polynomial g
      --               in the ring F[x]
      -- output:   the encoding polynomial for an information vector in F^k 
      x:= symbol x;
      R:=GF(#p.Alphabet)[x];
      i:=toList(0..(p.Locality-1));
      coeffs:=apply(i,l->getCoefficientPolynomial(p,infVec,g,l));
      polynoms:=apply(i,l->x^l);
      sum apply(i,k->((coeffs_k) * (polynoms_k)) ) -- still getting an error about incompatibility here
     )

getCoefficientPolynomial = method(TypicalValue => RingElement)
getCoefficientPolynomial(TargetParameters,List,RingElement,ZZ) := RingElement => (p,infVec,g,i) -> (
     -- generates the coefficient polynomial for an LRC code
      -- input:    the TargetParameters hash table p, a list infVec in F^k, a good polynomial g
      --               in the ring F[x], an increment i
      -- output:   the coefficient polynomial for an information vector in F^k  
      j:=toList(0..(p.Dimension//p.Locality-1));
      coeffs:=flatten apply(j,l->(infVec_{i*2+l}));
      polynoms:=apply(j,l->g^l);
      sum apply(j,k->((coeffs_k) * (polynoms_k)) ) -- still getting an error about incompatibility here
     )
 
 


----------------------------------------------------------
--           Good Polynomials for Partitions of symbols
--                (group theoretical constructions
----------------------------------------------------------


--goodPolynomial = method(Options=>{})
--goodPolynomial(ZZ,List) := RingElement -> (q,A) -> (
    -- generates a good polynomial for a partition of symbols in finite field F=F_q
    -- by utilizing the multiplicative group structure of F\0
    -- input:    field size q a prime, partition A of symbols in F\0
    -- output:   a polynomial function f such that the image of each point in a given 
    --          subset in A is the same.
    
    
    -- Needs work
--)

getGroupAnnihilatorPolynomial = method(TypicalValue => RingElement)
getGroupAnnihilatorPolynomial(List,ZZ) := RingElement => (G,q) -> (
    x:=symbol x;
    i:=toList(0..(#G-1));
    product(apply(i,inc->((sub(x,GF(q)[x])-G_inc))))
    )


--------------------------------------------- Test example
--   restart
--  
--   p = targetParameters(13,9,4,2)
--   A = { {1,3,9}, {2,6,5}, {4,12,10} }
--   use GF(#p.Alphabet)[x]
--   g = x^3
--   LRCencoding(p,A,g)

-------------------------   END   MATT
--------------------------------------------





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



shorten = method(TypicalValue => LinearCode)
-- input: An [n,k] linear code C and a set S of distinct integers { i1, ..., ir} such that 1 <= ik <= n.
-- output: A new code from C by selecting only those codewords of C having a zeros in each of the coordinate 
--     positions i1, ..., ir, and deleting these components. Thus, the resulting 
--     code will have length n - r. 
shorten ( LinearCode, List ) := LinearCode => ( C, L ) -> (
    local newL; local codeGens;
    
    codeGens = C.Generators;
    newL = delete(0, apply( codeGens, c -> (
	if sum apply( L, l -> c#l ) == 0
	then c
	else 0
	)));
    
    if newL == {} then return C else (
	newL = entries submatrix' ( matrix newL, L );
	return linearCode ( C.BaseField , newL );
	)
    )


-- input: An [n,k] linear code C and an iteger i such that 1 <= i <= n.
-- output: A new code from C by selecting only those codewords of C having a zero as their 
--     i-th component and deleting the i-th component from these codewords. Thus, the resulting 
--     code will have length n - 1. 
shorten ( LinearCode, ZZ ) := LinearCode => ( C, i ) -> (
    
    return shorten(C, {i})
    
    )



-- input: A module as the base field/ring, an integer n as the code length, and an integer
--    k as the code dimension.
-- output: a random codeword with AmbientModule M^n of dimension k

--random (Module, ZZ, ZZ) := LinearCode => (M, n, k) -> (
--    linearCode( M, apply(toList(1..n),j-> apply(toList(1..k),i-> random(M))) )
--    )

random (GaloisField, ZZ, ZZ) := LinearCode => opts -> (F, n, k) -> (
    linearCode( F, apply(toList(1..n),j-> apply(toList(1..k),i-> random(F, opts)) ) )
    )
    
    
    
-----------------------Generalized functions in coding theory---------------------
--------------------------------------------------------------
 --================= v-number function ========================
 
 fungen = method();
 fungen (Ideal,ZZ) := (I,n) -> (
 L:=ass I;
 flatten flatten degrees mingens(quotient(I,L#n)/I)
 )
 
-- pp_grobner = method();
-- pp_grobner (Ideal,ZZ) := (I,n) -> (
-- L:=ass I;
-- gens gb ideal(flatten mingens(quotient(I,L#n)/I))
 --)
 
 ggfun = method();
 ggfun (List) := (a) -> (
 toList(set a-set{0}) 
 )
 
 vnumber = method();
  vnumber (Ideal) := (I) ->
    (
      L:=ass I;     
      N:=apply(apply(0..#L-1,i->fungen(I,i)),i->ggfun(i));
      min flatten N 
    )
    
   
 -----------------------------------------------------------
 --****************** Footprint Function ********************
 
 msetfunc = method();
 msetfunc (Ideal,Ideal) := (I,x) -> (
 if not quotient(ideal(leadTerm gens gb I),x)==ideal(leadTerm gens gb I) then 
    degree coker gens gb ideal(ideal(leadTerm gens gb I),x) 
 else 0 
 )
 
 maxdegree = method();
 maxdegree (ZZ,ZZ,Ideal) := (d,r,I) -> (
 max apply(apply(apply(subsets(flatten entries basis(d,coker gens gb I),r),toSequence),ideal),i->msetfunc(I,i))
 )
 
 footPrint = method();
 footPrint (ZZ,ZZ,Ideal) := (d,r,I) ->(
 degree coker gens gb I - maxdegree(d,r,I)
 )
    
    
 
-----------------------------------------------------------
 --****************** GMD Function ********************
 
 elem = method();
 elem (ZZ,ZZ,Ideal) := (q,d,I) ->(
 apply(toList (set(0..q-1))^**(hilbertFunction(d,coker gens gb I))-(set{0})^**(hilbertFunction(d,coker gens gb I)),toList)
 )
 
 elemBas = method();
 elemBas (ZZ,ZZ,Ideal) := (q,d,I) ->(
 apply(elem(q,d,I),x -> basis(d,coker gens gb I)*vector deepSplice x)
 )
 
 setBas = method();
 setBas (ZZ,ZZ,ZZ,Ideal) := (q,d,r,I) ->(
 subsets(apply(elemBas(q,d,I),z->ideal(flatten entries z)),r)
 )
 
 --------------------------------------------------------
 --=====================hyp function======================
 
 hypFunction = method();
 hypFunction (ZZ,ZZ,ZZ,Ideal) := (q,d,r,I) ->(
 max apply(
 apply(
 setBas(q,d,r,I),ideal),
 x -> if #set flatten entries mingens ideal(leadTerm gens x)==r and not quotient(I,x)==I
         then degree(I+x)
      else 0
)
 )
 
 --------------------------------------------------------
 
 gMdFunction = method();
 gMdFunction (ZZ,ZZ,ZZ,Ideal) := (q,d,r,I) ->(
 degree(coker gens gb I)-hypFunction(q,d,r,I)
 )
 
 
 
 
 --------------------------------------------------------------
 --===================== Vasconcelos Function ================
 
 
 vasFunction = method();
 vasFunction (ZZ,ZZ,ZZ,Ideal) := (q,d,r,I) ->(
     min apply(
         apply(setBas(q,d,r,I),ideal), x -> if (#set flatten entries mingens ideal(leadTerm gens x)==r and not quotient(I,x)==I) then {
             degree(coker gens gb quotient(I,x))
         } else {
             degree(coker gens gb I)
         };
    )
)



----------------------------------------------------------------------------------


   

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
-- Mathematical Equality Test
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
-- shorten test, integer
F = GF(2)
codeLen = 10
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

TEST///
-- shorten test, list
F = GF(2)
codeLen = 10
codeDim = 4
L = {{0, 1, 0, 0, 0, 0, 0, 0, 0, 0}, {0, 0, 1, 0, 1, 1, 0, 1, 0, 0}, {1, 1, 0, 0, 0, 1, 0, 0, 1, 0}, {1, 0, 0, 1, 0, 0, 0, 1, 1, 1}}
H = L|L

C2 = linearCode(F,codeLen,H)
C3 = linearCode(F,codeLen,L)
K = {3,6,8,9}

shortL = {{0, 1, 0, 0, 0, 0}, {0, 0, 1, 1, 1, 1}}

assert( numColumns ( C2.GeneratorMatrix ) == numColumns (shorten( C2, K)).GeneratorMatrix + 4 )
assert( numColumns ( C3.GeneratorMatrix ) == numColumns (shorten( C3, K)).GeneratorMatrix + 4 )
assert( shorten( C2, K ) == linearCode(F, shortL) )
assert( shorten( C3, K ) == linearCode(F, shortL) )
///


TEST ///
-- random test
F = GF(2, 4)
n = 3
k = 5
C = random ( F , n, k )

assert( length C == k )
assert( dim C == 3 )

F = GF 2
n = 3
k = 5
C = random ( F , n, k )

assert( length C == k )
assert( dim C == 3 )
///

TEST ///
-- Hamming code over GF(2) and dimension of the dual 3
C1= HammingCode(2,3)
C1.ParityCheckMatrix
///

TEST ///
-- Hamming code over GF(2) and dimension of the dual 4
C2= HammingCode(2,4)
C2.ParityCheckMatrix
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
    Key => {HammingCode, (HammingCode,ZZ,ZZ)},
    Headline => "Generates the Hamming code over GF(q) and dimension of the dual r.",
    Usage => "HammingCode(q,r)",
    Inputs => {
	"q" => ZZ => {"Size of the field."},
	"r" => Vector => {"Dimension of the dual of the Hamming code."}	
	},
    Outputs => {
	"C" => LinearCode => {"Hamming code."}
	},
    "q and r and integers",
    "Returns the Hamming code over GF(q) and dimensino of the dual r.",
    EXAMPLE {
	"C1= HammingCode(2,3);",
	"C1.ParityCheckMatrix",
	"C2= HammingCode(2,3);",
	"C2.ParityCheckMatrix"
	}
    }

document {
    Key => MaxIterations,
    Headline => "Specifies the maximum amount of iterations before giving up. Default is 100.",
    TT "MaxIterations", " -- Specifies the max iterations.",
    PARA{},
    "This symbol is provided by the package ", TO CodingTheory, "."
    }

doc ///
   Key
       shorten
       (shorten, LinearCode, List)
       (shorten, LinearCode, ZZ)
   Headline
       shortens a linear code 
   Usage
       shorten(LinearCode, List)
       shorten(LindearCode, ZZ)
   Inputs
        C:LinearCode
	    a codeword of length $n$.
	L:List
	    a list of coordinate positions.
	i:ZZ
	    an integer representing a single coordinate position.
   Outputs
       :LinearCode
           a shortened linear code. 
   Description
       Text  
       	   A new code from $C$ by selecting only those codewords of $C$ 
	   having a zeros in each of the coordinate positions in the list $L$ (or the integer $i$) and deleting these 
	   components. Thus, the resulting code will have length $n - r$, where $r$ is the number
	   of elements in $L$ (or 1 when the integer $i$ is used). 

       Example
           F = GF(2)
	   codeLen = 10
	   L = {{0, 1, 0, 0, 0, 0, 0, 0, 0, 0}, {0, 0, 1, 0, 1, 1, 0, 1, 0, 0}, {1, 1, 0, 0, 0, 1, 0, 0, 1, 0}, {1, 0, 0, 1, 0, 0, 0, 1, 1, 1}}
	   C = linearCode(F,codeLen,L)
	   shorten(C, {3,6,8,9})
	   shorten(C, 3)
	   
///
	   
--   SeeAlso
       --codim
       --assPrimesHeight
--   Caveat
--       myDegree is was Problem 2 in the tutorial yesterday.

doc ///
   Key
       (random, GaloisField, ZZ, ZZ)
   Headline
       a random linear code 
   Usage
       random(GaloisField, ZZ, ZZ)
   Inputs
        F:GaloisField
	n:ZZ
	    an integer $n$ as the code length. 
	k:ZZ
	    an integer $k$ as the code dimension.
	    
   Outputs
       :LinearCode
           a random linear code of length $n$ and dimension $k$. 
   Description
       Example
       	   F = GF(2, 4)
	   C = random ( F , 3, 5 )
///

doc ///
   Key
       (symbol ==,LinearCode,LinearCode)
   Headline
       determines if two linear codes are equal
   Usage
       LinearCode == LinearCode
   Inputs
        C1:LinearCode
	    a linear code
	C2:LinearCode
	    a linear code
   Outputs
       :Boolean
           whether two codes define the same subspace
   Description
       Text  
       	   Given linear codes C1 and C2, this code determines if they
	   define the same subspace over the same field or ring.
       Example
           F = GF(3,4)
           codeLen = 7; codeDim = 3;
           L = apply(toList(1..codeDim),j-> apply(toList(1..codeLen),i-> random(F)))
           C1 = linearCode(F,L)
	   C2 = linearCode(matrix L)
	   C1 == C2
       
///

       
end

-- Here place M2 code that you find useful while developing this
-- package.  None of it will be executed when the file is loaded,
-- because loading stops when the symbol "end" is encountered.

restart
uninstallPackage "CodingTheory"
installPackage "CodingTheory"
installPackage("CodingTheory", RemakeAllDocumentation=>true)
check CodingTheory
viewHelp CodingTheory

-----------------------------------------------------
-- Codes from Generator Matrices (as lists):
-----------------------------------------------------
F = GF(3,4)
codeLen = 7
codeDim = 3
L = apply(toList(1..codeDim),j-> apply(toList(1..codeLen),i-> random(F)))
C = linearCode(F,L)
peek C
-- check that dimension and length are correct:
dim C
length C
-- check that G*H^t = 0:
C.GeneratorMatrix * (transpose C.ParityCheckMatrix)

-----------------------------------------------------
-- Codes from Parity Check Matrices (as a matrix):
-----------------------------------------------------
F = GF(2)
L = {{1,0,1,0,0,0,1,1,0,0},{0,1,0,0,0,0,0,1,1,0},{0,0,1,0,1,0,0,0,1,1},{1,0,0,1,0,1,0,0,0,1},{0,1,0,0,1,1,1,0,0,0}}
C = linearCode(F,L,ParityCheck => true)
peek C


-----------------------------------------------------
-- Codes with Rank Deficient Matrices:
-----------------------------------------------------
R=GF 4
M=R^4
C = linearCode(R,{{1,0,1,0},{1,0,1,0}})
peek C


-- Local Variables:
-- compile-command: "make -C $M2BUILDDIR/Macaulay2/packages PACKAGES=CodingTheory pre-install"
-- End:


