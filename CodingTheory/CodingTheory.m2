-- -*- coding: utf-8 -*-
newPackage(
	"CodingTheory",
    	Version => "1.0", 
    	Date => "May 11, 2020",
    	Authors => {
	     {Name => "Hiram Lopez", Email => "h.lopezvaldez@csuohio.edu"},
	     {Name => "Gwyn Whieldon", Email => "gwyn.whieldon@gmail.com"},
	     {Name => "Taylor Ball", Email => "trball13@gmail.com"},
	     {Name => "Nathan Nichols", Email => "nathannichols454@gmail.com"}
	     },
    	HomePage => "https://academic.csuohio.edu/h_lopez/",
    	Headline => "a package for coding theory in M2",
	AuxiliaryFiles => false, -- set to true if package comes with auxiliary files,
	Configuration => {},
        DebuggingMode => false,
	PackageImports => {
	    "SRdeformations",
	    "Polyhedra",
	    "Graphs",
	    "NAGtypes",
	    "RationalPoints" },
        PackageExports => {
	    "SRdeformations",
	    "Polyhedra",
	    "Graphs",
	    "NAGtypes",
	    "RationalPoints" 
	    }
	)

-- Any symbols or functions that the user is to have access to
-- must be placed in one of the following two lists

export {
    -- helper/conversion methods
    "generatorToParityCheck",
    "parityCheckToGenerator",
    "reduceMatrix",
    
    -- Linear Code
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
    
    -- Evaluation Code
    -- Types and Constructors
    "EvaluationCode",
    "VanishingIdeal",
    "PolynomialSet",
    "ExponentsMatrix",
    "AmbientSpace",
    "IncidenceMatrix",
    "Sets",
    "evaluationCode",
    "toricCode",
    "evCodeGraph",
    "codeGraph",
    "codeGraphInc",
    "cartesianCode",
    "RMCode",
    "orderCode",
    "RSCode",
    
    
    -- Families of Codes
    "zeroCode",
    "universeCode",
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
    "ambientSpace",
    "informationRate",
    "dualCode",
    "alphabet",
    "messages",
    "codewords",
    "genericCode",
    "bitflipDecode",
    "MaxIterations",
    "shorten",
    "vNumber",
    "footPrint",
    "hYpFunction",
    "gMdFunction",
    "vasFunction",
    "tannerGraph"
    }

exportMutable {}

------------------------------------------
------------------------------------------
-- Linear Code Data Types and Constructors
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
    
    -- take (n-k) columns of standard generating matrix above:
    redG := Gred_{0..(rank Gred.source - rank Gred -1)};
    
    -- vertically concatenate an identity matrix of rank (n-k),
    -- then transpose :
    return permuteMatrixColumns(transpose (id_(redG.source) || -redG),inversePermutation(P))
    
    )

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

 
-- internal function to validate user's input
wellDefinedInput  = method(TypicalValue => List)

wellDefinedInput(List) :=  UserInput -> (
    -- user's input is used to create a list
    -- UserInput={GaloisField or Ring, lengthCode, ListGenerators}
    -- or UserInput = {GaloisField or Ring, lengthCode,ListParityCheckRows}
    
    -- check if "baseField" is a Galois field, throw an error otherwise:
    if not isField UserInput_0 then  "Warning: Codes over non-fields may not unstable.";
    
    if UserInput_2 != {} then {
    	-- check that the length of all generating codewords equals the rank of AmbienModule:
    	if not all(UserInput_2,codeword -> (length codeword) == UserInput_1) then {
	    error "Expected codewords all to be the same length and equal to the rank of the Module";
	    } 
	else {
	    -- coerce generators into base field, if possible:
	    return try apply(UserInput_2, codeword -> apply(codeword, entry -> sub(entry, UserInput_0)))
	     else {
	    error "Entries of codewords do not live in base field/ring.";
	    }
	   }
	} else {
	return  UserInput_2
	};
  )


------------------------------------------
-- Linear Code Type and constructors:
------------------------------------------

-- Use this section to add basic types and
-- constructors for error correcting codes
 
LinearCode = new Type of HashTable

-- internal function to validate inputs:
rawLinearCode = method()
rawLinearCode(List) := LinearCode => (inputVec) -> (
    -- use externally facing functions to create list:	
    -- { AmbientModule, BaseField, Generators, ParityCheckRows, Code}
    
    
    -- check if "baseField" is a field, throw warning otherwise:
    if not isField(inputVec_1) then print "Warning: Working over non-field.";    
   
    if inputVec_2 != {} then {
	-- validate inputs and coerce into base field:
	newGens := wellDefinedInput({inputVec_1,rank inputVec_0,inputVec_2});
	newGenMat := matrix(newGens);
    } else {
	-- if generators and generator matrix were undefined:
	newGens = {};
	newGenMat = matrix({newGens});
    };
    
    if inputVec_3 != {} then {
	-- validate inputs and coerce into base field:
	newParRow := wellDefinedInput({inputVec_1, rank inputVec_0, inputVec_3});
	newParMat := matrix(newParRow);	
	
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
    codeSpace := if (reduceMatrix(generators inputVec_4) == generators inputVec_4) then sub(inputVec_4,inputVec_1) else image groebnerBasis sub(inputVec_4,inputVec_1);
    
    
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
	outputVec =  {M.source, M.ring, entries M, {}, image transpose M};
	};
    
    rawLinearCode(outputVec)
      
    )

net LinearCode := c -> (
     "Code with Generator Matrix: " | net c.GeneratorMatrix
     )
toString LinearCode := c -> toString c.Generators

-----------------------------------------------
-----------------------------------------------
-- Evaluation Code Data Types and Constructors
-----------------------------------------------
-----------------------------------------------

-*
    new EvaluationCode from{
	symbol Points => P, --- a set of points of F^m
	symbol VanishingIdeal => I, --the vanishing ideal of polynomials in m variables
	symbol ExponentsMatrix => LL, -- the matrix of exponents, exponent vectors are rows
	symbol IncidenceMatrix => M, -- the incidence matrix of a graph
	symbol PolynomialSet => S,  --- a set of polynomials 
	symbol LinearCode => linearCode(G), -- the linear code associated with the evaluation code
	symbol Sets => S, -- the collection of subsets used for constracting a Cartesian code
	symbol AmbientSpace => F^(#P),  --- the ambient space for an evaluation code
	symbol cache => {}
	}
*-

EvaluationCode = new Type of HashTable

evaluationCode = method(Options => {})

evaluationCode(Ring,List,List) := EvaluationCode => opts -> (F,P,S) -> (
    -- constructor for the evaluation code
    -- input: a field F, a list of points in F^m, a set of polynomials over F in m variables.
    -- outputs: The list of points, the list of polynomials, the vanishing ideal and the linear code, the linear code.
    
    m := # P#0;
    if class(ring ideal S) === PolynomialRing then R:=(ring ideal S) else (t := getSymbol "t", R=F[t_1..t_m], S=apply(S,i->promote(i,R)));
    I := intersect apply(P,i->ideal apply(numgens R,j->R_j-i#j)); -- Vanishing ideal of the set of points.
    G := transpose matrix apply(P,i->flatten entries sub(matrix(R,{S}),matrix(F,{i}))); -- Evaluate the elements in S over the elements on P.
    return new EvaluationCode from{
	symbol VanishingIdeal => I, 
	symbol Points => P,
	symbol PolynomialSet => S,
	symbol LinearCode => linearCode G, -- the linear code produced by the evaluation code construction
	symbol cache => {}
	}
    )

evaluationCode(Ring,List,Matrix) := EvaluationCode => opts -> (F,P,M) -> (
    -- Constructor for a evaluation (monomial) code.
    -- inputs: a field, a list of points (as a tuples) of the same length and a matrix of exponents.
    -- outputs: a F-module.    
    -- We should check if all the points of P are in the same F-vector space.
    m := numgens image M; -- number of monomials.
    t := getSymbol "t";
    R := F[t_0..t_(m-1)];
    S := apply(entries M, i -> vectorToMonomial(vector i,R));    
    evaluationCode(F,P,S)
    )

net EvaluationCode := c -> (
    c.LinearCode
    )

------------------------------------------
-- Evaluation Code constructors:
------------------------------------------

toricCode = method(Options => {})
toricCode(Ring,Matrix) := EvaluationCode => opts -> (F,M) -> (
    -- Constructor for a toric code.
    -- inputs: a Galois field, an integer matrix 
    -- outputs: the evaluation code defined by evaluating all monomials corresponding to integer 
    ---         points in the convex hull (lattice polytope) of the columns of M at the points of the algebraic torus (F*)^n
    
    z:=F_0;  --- define the primitive element of the field
    q:=F.order; --- define the size of the field
    s:=set apply(q-1,i->z^i); -- set of non-zero elements in the field
    m:=numgens target M; --- the length of the exponent vectors, i.e. number of variables for monomials, i.e.the dim of the ambient space containing the polytope
    ss:=s; 
    for i from 1 to m-1 do (
    	ss=set toList ss/splice**s;  
    );
    P:=toList ss/splice;   -- the loop above creates the list of all m-tuples of non-zero elements of F, i.e. the list of points in the algebraic torus (F*)^m
    Polytop:=convexHull M; -- the convex hull of the columns of M
    L:=latticePoints Polytop; -- the list of lattice points in Polytop
    LL:=matrix apply(L, i-> first entries transpose i); --converts the list of lattice points to a matrix of exponents
    G:=matrix apply(entries LL,i->apply(P,j->product apply(m,k->(j#k)^(i#k)))); -- the matrix of generators; rows form a generating set of codewords
    
    t := getSymbol "t";
    
    R:=F[t_1..t_m]; --- defines the ring containing monomials corresponding to exponents
    I := ideal apply(m,j->R_j^(q-1)-1); --  the vanishing ideal of (F*)^m
    
    new EvaluationCode from{
	symbol Points => P, --- the points of (F*)^m
	symbol VanishingIdeal => I, --the vanishing ideal of (F*)^m
	symbol ExponentsMatrix => LL, -- the matrix of exponents, exponent vectors are rows
	symbol LinearCode => linearCode(G), -- the linear code
	symbol cache => {}
	}
) 

----------Reed–Muller-type code of degree d over a graph using our the algorithm of evaluationCode
evCodeGraph  = method(Options => {});

evCodeGraph (Ring,Matrix,List) := evCodeGraph  => opts -> (F,M,S) -> (
    -- input: a field, Incidence matrix of the graph , a set of polynomials.
    -- outputs: a monomial code over the list of points.    
    -- We should check if all the points live in the same F-vector space.
    -- Should we check if all the monomials live in the same ring?
    
    P := entries transpose M;
    R := ring S#0;  --- MAY NOT WORK if the first element of S is a constant polynomial!
    I := intersect apply(P,i->ideal apply(numgens R-1,j->R_j-i#j)); -- Vanishing ideal of the set of points.
    S = toList apply(apply(S,i->promote(i,R/I)),j->lift(j,R))-set{0*S#0}; -- Drop the elements in S that was already in I.
    G := matrix apply(P,i->flatten entries sub(matrix(R,{S}),matrix(F,{i}))); -- Evaluate the elements in S over the elements on P.    
    
    new EvaluationCode from{
	symbol AmbientSpace => F^(#P),
	symbol Points => P,
	symbol VanishingIdeal => I,
	symbol PolynomialSet => S,
	symbol LinearCode => linearCode(G),
	symbol cache => {}
	}
    )


-------Reed–Muller-type code of degree d over a graph using the function evaluate from package "NAGtypes"---------------


codeGraph  = method(TypicalValue => Module);

codeGraph (Matrix,ZZ,ZZ) := (M,d,p)->(
    K:=ZZ/p;
    tMatInc:=transpose M;
    X:=entries tMatInc;    
    t := getSymbol "t";
    R:=K[t_(0)..t_(numgens target M-1)];    
    SetPoly:=flatten entries basis(d,R);
    SetPolySys:=apply(0..length SetPoly-1, x->polySystem{SetPoly#x});
    XX:=apply(X,x->point{x});
    C:=apply(apply(SetPolySys,y->apply(0..length XX -1,x->(flatten entries evaluate(y,XX#x))#0)),toList);
    G:=transpose matrix{C};
    
    new EvaluationCode from{
	symbol AmbientSpace => K^(#X),
	symbol IncidenceMatrix => M,
	symbol LinearCode => linearCode(G),
	symbol cache => {}
	}
    
)


codeGraphInc = method(TypicalValue => Module);
-- M is the incidence matrix of the Graph G
--inputs: The incidence matrix of a Graph G, a prime number  
-- outputs: K-module

codeGraphInc (Matrix,ZZ):= (M,p)->(
    K:=ZZ/p;
    tInc:=transpose M;
    X:=entries tInc;    
    t := getSymbol "t";
    R:=K[t_(0)..t_(numgens target M-1)];    
    SetPol:=flatten entries basis(1,R);
    SetPolSys:=apply(0..length SetPol-1, x->polySystem{SetPol#x});
    XX:=apply(X,x->point{x});
    C:=apply(apply(SetPolSys,y->apply(0..length XX -1,x->(flatten entries evaluate(y,XX#x))#0)),toList);
    G:=transpose matrix{C};

    new EvaluationCode from{
	symbol AmbientSpace => K^(#X),
	symbol IncidenceMatrix => M,
	symbol LinearCode => linearCode(G),
	symbol cache => {}
	}
)


cartesianCode = method(Options => {})

cartesianCode(Ring,List,List) := EvaluationCode => opts -> (F,S,M) -> (
    --constructor for a cartesian code
    --input: a field, a list of subsets of F and a list of polynomials.
    --outputs: The evaluation code using the cartesian product of the elements in S and the polynomials in M.
    
    m := #S;
    if class(ring ideal M) === PolynomialRing then R:=(ring ideal M) else (t := getSymbol "t", R=F[t_1..t_m], M=apply(M,i->promote(i,R)));
    I := ideal apply(m,i->product apply(S#i,j->R_i-j));
    P := set S#0;
    for i from 1 to m-1 do P=P**set S#i;
    if m==1 then {P = apply(toList(P/deepSplice),i->{i})} else
    {P = apply(toList(P/deepSplice),i->toList i)};
    G := transpose matrix apply(P,i->flatten entries sub(matrix(R,{M}),matrix(F,{i})));
    
    new EvaluationCode from{
	symbol Sets => S,
	symbol Points => P,
	symbol VanishingIdeal => I,
	symbol PolynomialSet => M,
	symbol LinearCode => linearCode(G),
	symbol cache => {}
	}
    )

cartesianCode(Ring,List,ZZ) := EvaluationCode => opts -> (F,S,d) -> (
    -- Constructor for cartesian codes.
    -- inputs: A field F, a set of tuples representing the subsets of F and the degree d.
    -- outputs: the cartesian code of degree d.
    m:=#S;
    t := getSymbol "t";
    R:=F[t_0..t_(m-1)];
    M:=apply(flatten entries basis(R/monomialIdeal basis(d+1,R)),i->lift(i,R));
    cartesianCode(F,S,M)
    )
   
cartesianCode(Ring,List,Matrix) := EvaluationCode => opts -> (F,S,M) -> (
    -- constructor for a monomial cartesian code.
    -- inputs: a field, a list of sets, a matrix representing as rows the exponents of the variables
    -- outputs: a cartesian code evaluated with monomials
    
    -- Should we add a second version of this function with a third argument an ideal? For the case of decreasing monomial codes.
    
    m := #S;
    
    t := getSymbol "t";
    R := F[t_0..t_(m-1)];
    T := apply(entries M,i->vectorToMonomial(vector i,R));
    
    cartesianCode(F,S,T)
    )


RMCode = method(TypicalValue => EvaluationCode)
RMCode(ZZ,ZZ,ZZ) := EvaluationCode => (q,m,d) -> (
    -- Contructor for a Reed-Muller code.
    -- Inputs: A prime power q (the order of the finite field), m the number of variables in the defining ring  and an integer d (the degree of the code).
    -- outputs: The cartesian code of the GRM code.
    F := GF(q);
    S := apply(q-1, i->F_0^i)|{0*F_0};
    S = apply(m, i->S);
    cartesianCode(F,S,d)
    )


RSCode = method(TypicalValue => EvaluationCode)
RSCode(Ring,List,ZZ) := EvaluationCode => (F,S,d) -> (
    -- Contructor for a Reed-Solomon code.
    -- Inputs: Field, subset of the field and an integer d (polynomials of degree less than d will be evaluated).
    cartesianCode(F,{S},d-1)
    )


orderCode = method(Options => {})

orderCode(Ring,List,List,ZZ) := EvaluationCode => opts -> (F,P,G,l) -> (
    -- Order codes are defined through a set of points and a numerical semigroup.
    -- Inputs: A field, a list of points P, the minimal generating set of the semigroup (where G_1<G_2<...) of the order function, a bound l.
    -- Outputs: the evaluation code evaluated in P by the polynomials with weight less or equal than l.    
    -- We should add a check to way if all the points are of the same length.
    
    m := length P#0;
    t := getSymbol "t";
    R := F[t_0..t_(m-1), Degrees=>G];
    M := matrix apply(toList sum apply(l+1, i -> set flatten entries basis(i,R)),j->first exponents j);

    evaluationCode(F,P,M)
    )

orderCode(Ideal,List,List,ZZ) := EvaluationCode => opts -> (I,P,G,l) -> (
    -- If we know the defining ideal of the finite algebra associated to the order function, we can obtain the generating matrix.
    -- Inputs: The ideal I that defines the finite algebra of the order function, the points to evaluate over, the minimal generating set of the semigroups associated to the order function and the bound.
    -- Outpus: an evaluation code.
    
    m := #flatten entries basis(1,I.ring);    
    t := getSymbol "t";
    R := (coefficientRing I.ring)[t_1..t_m, Degrees=>G, MonomialOrder => (reverse apply(flatten entries basis(1,I.ring),i -> Weights => first exponents i))];
    J := sub(I,matrix{gens R});
    S := R/J;
    M := matrix apply(toList sum apply(l+1,i->set flatten entries basis(i,S)),i->first exponents i);
    
    evaluationCode(coefficientRing I.ring, P, M)
    )

orderCode(Ideal,List,ZZ) := EvaluationCode => opts -> (I,G,l) -> (
    -- The same as before, but taking P as the rational points of I.

    P := rationalPoints I;
    orderCode(I,P,G,l)
    )



------------------------------------------
------------------------------------------
-- Basic Code Types
------------------------------------------
------------------------------------------

zeroCode = method()
zeroCode(GaloisField,ZZ) := LinearCode =>(F,n)->(
    -- Generates the zero code in F^n
    -- check n is positive
    
    if n >0 then {    
    	GenMat := matrix {apply(toList(0..n-1),i->0)};
    	GenRow := {{}};
    	ParMat := generators F^n;
    	ParRows := entries ParMat;
    	return new LinearCode from {
            symbol AmbientModule => F^n,
	    symbol BaseField => F,
            symbol Generators => GenRow,
	    symbol GeneratorMatrix => GenMat,
	    symbol ParityCheckMatrix =>  ParMat,
	    symbol ParityCheckRows  => ParRows,
	    symbol cache => {}
	    }
    } else {
    error "The length of the code should be positive."
    };
  )

universeCode = method()
universeCode(GaloisField,ZZ) := LinearCode => (F,n) -> (
    -- construct the universe code F^n
    -- check n is positive
    if n>0 then {
	GenMat := generators F^n;
    	GenRow := entries GenMat;
    	ParMat := matrix {apply(toList(0..n-1),i->0)};
    	ParRows := {{}};
    	return new LinearCode from {
            symbol AmbientModule => F^n,
	    symbol BaseField => F,
            symbol Generators => GenRow,
	    symbol GeneratorMatrix => GenMat,
	    symbol ParityCheckMatrix =>  ParMat,
	    symbol ParityCheckRows  => ParRows,
	    symbol cache => {}
	    }	
	} else {
	error "The length of the code should be positive."
	};    
    )


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
    K := GF(q);
    -- setK is the set that contains all the elements of the field
    setK := set(  {0}| apply(toList(1..q-1),i -> K_1^i));
    -- C is the transpose of the parity check matrix of the code. Its rows are the the points of the
    -- projective space P(r-1,q)
    j := 1;
    C := matrix(apply(toList(1..q^(r-j)), i -> apply(toList(1..1),j -> 1))) | matrix apply(toList(toList setK^**(r-j)/deepSplice),i->toList i);
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
-- Linear Code Methods
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
    
    -- check if "base ring" is ZZ/q:
    if C.BaseField.baseRings === {ZZ} then {
	a := sub(1,C.BaseField);
	-- generate elements additively:
	alphaB := apply(toList(1..(C.BaseField.order)), i-> i*a)
	} else {
	a = C.BaseField.generators_0;
 	-- take 0, and compute non-zero elements of C.BaseField:
	alphaB = {sub(0,C.BaseField)} | apply(toList(1..(C.BaseField.order-1)), i-> a^i);
	};
    
    -- return this alphabet:
    alphaB    
    
    )

genericCode = method(TypicalValue => LinearCode)
genericCode(LinearCode) := LinearCode => C -> (
    linearCode(C.AmbientModule)
    )

-- method to generate all message words in code:
messages = method(TypicalValue => List)
messages(LinearCode) := List => C -> (
    k := dim C ;
    A := alphabet C;
    messageSpace := apply(toList((set A)^**k) / deepSplice, c -> toList(c));
    return messageSpace
    )

-- method to compute the set of 2^k codewords in an [n,k]-code:
codewords = method(TypicalValue => List)
codewords(LinearCode) := List => C -> (
    -- save generator matrix as G:
    G := C.GeneratorMatrix;
    
    -- convert message vectors as lists into matrices:
    M := apply(messages C, m-> matrix({m}));
    
    -- map m -> mG to compute codewords:
    return flatten apply(M, m -> entries (m*G))
    )




shorten = method(TypicalValue => LinearCode)
-- input: An [n,k] linear code C and a set S of distinct integers { i1, ..., ir} such that 1 <= ik <= n.
-- output: A new code from C by selecting only those codewords of C having a zeros in each of the coordinate 
--     positions i1, ..., ir, and deleting these components. Thus, the resulting 
--     code will have length n - r. 
shorten ( LinearCode, List ) := LinearCode => ( C, L ) -> (
    local newL; local codeGens; local F;
    
    F = C.BaseField;
    codeGens = C.Generators;
    
    newL = delete(0, apply( codeGens, c -> (
	if sum apply( L, l -> if c#l == 0_F then 0_ZZ else 1_ZZ ) == 0_ZZ
	then c
	else 0
	)));

    if newL == {} then return C else (
	newL = entries submatrix' ( matrix newL, L );
	return linearCode ( C.BaseField , newL );
	)
    )

-*
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
*-

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
    linearCode(F, n, apply(toList(1..k), j-> apply(toList(1..n),i-> random(F, opts))))
    )

random (QuotientRing, ZZ, ZZ) := LinearCode => opts -> (R, n, k) -> (
    linearCode(matrix apply(toList(1..k), j-> apply(toList(1..n),i-> random(R, opts))))
    )

    
-----------------------Generalized functions in coding theory---------------------
--------------------------------------------------------------
 --================= v-number function ========================
 

  vNumber = method(TypicalValue => ZZ);
  vNumber (Ideal) := (I) ->
    (
      L:=ass I;  
      G:=apply(0..#L-1,i->flatten flatten degrees mingens(quotient(I,L#i)/I)); 
      N:=apply(G,i->toList(set i-set{0}));
      min flatten N 
    )

 
      
 
 
   
 -----------------------------------------------------------
 --****************** Footprint Function ********************
 footPrint = method(TypicalValue => ZZ);
 footPrint (ZZ,ZZ,Ideal) := (d,r,I) ->(
 mD:=max apply(apply(apply(subsets(flatten entries basis(d,coker gens gb I),r),toSequence),ideal),x->if not quotient(ideal(leadTerm gens gb I),x)==ideal(leadTerm gens gb I) then 
    degree coker gens gb ideal(ideal(leadTerm gens gb I),x) 
 else 0 );
 degree coker gens gb I - mD
 )
 
 
-----------------------------------------------------------
 --****************** GMD Functions ********************
 
 --------------------------------------------------------
 --=====================hyp function======================
 hYpFunction = method(TypicalValue => ZZ);
 hYpFunction (ZZ,ZZ,Ideal) := (d,r,I) ->(
 max apply(apply(subsets(apply(apply(apply(toList (set(0..char ring I-1))^**(hilbertFunction(d,coker gens gb I))-(set{0})^**(hilbertFunction(d,coker gens gb I)),toList),x -> basis(d,coker gens gb I)*vector deepSplice x),z->ideal(flatten entries z)),r)
,ideal),
 x -> if #set flatten entries mingens ideal(leadTerm gens x)==r and not quotient(I,x)==I
         then degree(I+x)
      else 0
)
 )
  
 ------------------------GMD Function--------------------------------
 
 gMdFunction = method(TypicalValue => ZZ);
 gMdFunction (ZZ,ZZ,Ideal) := (d,r,I) ->(
 degree(coker gens gb I)-hYpFunction(d,r,I)
 )

 
  
 --------------------------------------------------------------
 --===================== Vasconcelos Function ================
 
 
 vasFunction = method(TypicalValue => ZZ);
 vasFunction (ZZ,ZZ,Ideal) := (d,r,I) ->(
 min apply(apply(subsets(apply(apply(apply(toList (set(0..char ring I-1))^**(hilbertFunction(d,coker gens gb I))-(set{0})^**(hilbertFunction(d,coker gens gb I)),toList),x -> basis(d,coker gens gb I)*vector deepSplice x),z->ideal(flatten entries z)),r)
,ideal),
 x -> if #set flatten entries mingens ideal(leadTerm gens x)==r and not quotient(I,x)==I
         then degree(coker gens gb quotient(I,x))
      else degree(coker gens gb I)
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
    

tannerGraph = method(TypicalValue => Graphs$Graph)
tannerGraph(Matrix) := H -> (
    R := ring(H);
    cSym := getSymbol "c";
    rSym := getSymbol "r";
    symsA := toList (cSym_0..cSym_((numgens source H)-1)); 
    symsB := toList (rSym_0..rSym_((numgens target H)-1));
    
    -- The vertex sets of the bipartite graph.
    tannerEdges := for i from 0 to (numgens source H)-1 list(
    	for j from 0 to (numgens target H)-1 list(
    	if H_(j,i) != 0 then(
	    {symsA#i, symsB#j}
	    )else(
	    continue;
	    )
	)
    );
    Graphs$graph(symsA|symsB, flatten tannerEdges)    
);

------------------------------------------
------------------------------------------
-- Tests
------------------------------------------
------------------------------------------

-----------------------------------------------
-----------------------------------------------
-- Use this section for LinearCode tests:
-----------------------------------------------
-----------------------------------------------

TEST ///
-- tannerGraph test
R := GF(2);
for i from 1 to 20 do(
    H := random(R^10, R^10);
    G := tannerGraph H;
    -- Edges correspond 1:1 with ones in H.
    assert(length (Graphs$edges G) == sum flatten entries (lift(H,ZZ)));  
);
///


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
-- vNumner of the ideal I=ideal(t1*t2^2-t1^2*t2,t1*t3^3-t1^3t3,t2*t3^3-t2^3*t3)
K=ZZ/3
R=K[t3,t2,t1,MonomialOrder=>Lex]
I=ideal(t1*t2^2-t1^2*t2,t1*t3^3-t1^3*t3,t2*t3^3-t2^3*t3)
vNumber(I)
assert(vNumber(I)==regularity coker gens gb I-1)
///

TEST ///
-- footPrint function of the ideal I=ideal(t1^3,t2*t3) with parameters d=2, r=3
K=QQ
R=K[t1,t2,t3]
I=ideal(t1^3,t2*t3)
footPrint(3,4,I)
assert(footPrint(3,4,I)==4)
///

TEST ///
-- hYpFunction of the ideal I=ideal(t1*t6-t3*t4,t2*t6-t3*t5) with parameters d=1, r=1
K=ZZ/3
R=K[t1,t2,t3,t4,t5,t6]
I=ideal(t1*t6-t3*t4,t2*t6-t3*t5)
hYpFunction(1,1,I)
assert(hYpFunction(1,1,I)==1)
///


TEST ///
-- gMdFunction of the ideal I=ideal(t1*t6-t3*t4,t2*t6-t3*t5) with parameters d=1, r=1
K=ZZ/3
R=K[t1,t2,t3,t4,t5,t6]
I=ideal(t1*t6-t3*t4,t2*t6-t3*t5)
gMdFunction(1,1,I)
assert(gMdFunction(1,1,I)==3)
///


TEST ///
 -- vasFunction of the ideal I=ideal(t1^2,t1*t2,t2^2) with parameters d=1, r=1
K=ZZ/3
R=K[t1,t2]
I=ideal(t1^2,t1*t2,t2^2)
vasFunction(1,1,I)
assert(vasFunction(1,1,I)==1)
///


TEST /// 
-- random test
F = GF(2, 4)
n = 5
k = 3
C = random ( F , n, k )

assert( length C == 5 )
assert( dim C == 3 )

F = GF 2
n = 5
k = 3
C = random ( F , n, k )

assert( length C == n)
assert( dim C == k )
///


TEST ///
-- Hamming code over GF(2) and dimension of the dual 3
C1= HammingCode(2,3)
assert( length C1 == 7)
///

TEST ///
-- Hamming code over GF(2) and dimension of the dual 4
C2= HammingCode(2,4)
assert( length C2 == 15)
///

-----------------------------------------------
-----------------------------------------------
-- Use this section for Evaluation Code Tests
-----------------------------------------------
-----------------------------------------------

TEST ///
-- Evaluation code
F=GF(4);
R=F[x,y,z];
P={{0,0,0},{1,0,0},{0,1,0},{0,0,1},{1,1,1},{a,a,a}};
S={x+y+z,a+y*z^2,z^2,x+y+z+z^2};
C=evaluationCode(F,P,S);
assert(length C.LinearCode == 6)
assert(dim C.LinearCode == 3)
///

TEST ///
-- Toric code
M=matrix{{1,2,10},{4,5,6}} -- martrix of exponent vectors definind the polytope P, exponents vectors are columns
T=toricCode(GF 4,M) --- a toric code over F_4 with polytope P
assert(length T.LinearCode == 9)
assert(dim T.LinearCode == 5)
///

TEST ///
-- Cartesian code
F=GF(4);
R=F[x,y];
C=cartesianCode(F,{{0,1,a},{0,1,a}},{1+x+y,x*y})
assert(length C.LinearCode == 9)
assert(dim C.LinearCode == 2)
///

TEST ///
-- Cartesian codes
C=cartesianCode(ZZ/11,{{1,2,3},{2,6,8}},3)
assert( length C.LinearCode == 9)
///

TEST ///
-- Reed-Muller codes
C=RMCode(3,3,4);
assert( length C.LinearCode == 27)
///

TEST ///
-- Reed-Solomon codes
C=RSCode(ZZ/11,{1,2,3},3);
assert( length C.LinearCode == 3)
///

TEST ///
-- Reed-Solomon codes
C=RSCode(ZZ/17,{0,1,2,3,7,11},4)
dim C.LinearCode
assert( dim C.LinearCode == 4)
///

TEST ///
-- Order codes
F=GF(4);
R=F[x,y];
I=ideal(x^3+y^2+y);
l=7;
C=orderCode(I,{2,3},l);
assert(length C.LinearCode==8)
assert( dim C.LinearCode==7)
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
	},    
    
	SUBSECTION "Contributors", "The following people have generously
	contributed code or worked on our code at various Macaulay2 workshops.",
	
	UL {
	    "Branden Stone"
	},
    
	SUBSECTION "Modified Methods",
	
	UL {
	    TO "random(GaloisField, ZZ, ZZ)" -- not sure how to cite this properly.
	}
    	
	}
    
-----------------------------------------------
-----------------------------------------------
-- Use this section for Linear Code documentation:
-----------------------------------------------
-----------------------------------------------
    
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
    Headline => "This does not work and it will likely be removed.",
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
    Key => {tannerGraph, (tannerGraph,Matrix)},
    Headline => "Outputs the Tanner graph associated with the given parity check matrix.",
    Usage => "bitflipDecode(H,v)",
    Inputs => {
	"H" => Matrix => {"The parity check matrix."}
      	},
    Outputs => {
	Graphs$Graph => {}
	},
    "Calculates the bipartite Tanner graph of the parity check matrix H.",
    EXAMPLE {
	"H := matrix(GF(2), {{1,1,0,0,0,0,0},{0,1,1,0,0,0,0},{0,1,1,1,1,0,0},{0,0,0,1,1,0,0},{0,0,0,0,1,1,0},{0,0,0,0,1,0,1}});",
	"tannerGraph(H)"
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
    PARA{"This symbol is provided by the package ", TO CodingTheory, "."}
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

document {
   Key => {vNumber, (vNumber,Ideal)},
   Headline => "Gives the v-number of a graded ideal.",
   Usage => "vNumber(I)",
   Inputs => {
	"I" => Ideal => {"Graded ideal."},
	},
   Outputs => {
	"i" => ZZ => {"v-number of the ideal."}
	},
	EXAMPLE {
	"K=ZZ/3;",
        "R=K[t3,t2,t1,MonomialOrder=>Lex];",
        "I=ideal(t1*t2^2-t1^2*t2,t1*t3^3-t1^3*t3,t2*t3^3-t2^3*t3);",
        "vNumber(I)"
	}
 }
 

 document {
   Key => {footPrint, (footPrint,ZZ,ZZ,Ideal)},
   Headline => "Gives the footPrint value of an ideal with parameters (d,r)",
   Usage => "footPrint(d,r,I)",
   Inputs => {
	"I" => Ideal => {"Graded ideal."},
	"d" => ZZ => {"Degree of the monomials in the Gröbner éscalier of I."},
	"r" => ZZ => {"Length of the sequences in the Gröbner éscalier of I of degree d."}
	},
   Outputs => {
	"i" => ZZ => {"footPrint value of an ideal with parameters (d,r)."}
	},
	EXAMPLE {
	"K=QQ;", 
        "R=K[t1,t2,t3];",
        "I=ideal(t1^3,t2*t3);",
        "footPrint(2,3,I)"
	}
 }
    

    
document {
   Key => {hYpFunction, (hYpFunction,ZZ,ZZ,Ideal)},
   Headline => "Gives the hYp value of an ideal with parameters (d,r)",
   Usage => "hYpFunction(d,r,I)",
   Inputs => {
	"I" => Ideal => {"Graded ideal."},
	"d" => ZZ => {"Degree of certain homogenous component of ring I."},
	"r" => ZZ => {"Length of the sequences in homogenous component of degree d."}
	},
   Outputs => {
       "i" => ZZ => {"The hYp value of an ideal with parameters (d,r)."}
	},
	EXAMPLE {
	"K=ZZ/3;", 
        "R=K[t1,t2,t3,t4,t5,t6];",
        "I=ideal(t1*t6-t3*t4,t2*t6-t3*t5);",
        "hYpFunction(1,1,I)"
	}
 }  
 

 document {
   Key => {gMdFunction, (gMdFunction,ZZ,ZZ,Ideal)},
   Headline => "Gives the Generalized minimum distance value of an ideal with parameters (d,r)",
   Usage => "gMdFunction(d,r,I)",
   Inputs => {
	"I" => Ideal => {"Graded ideal."},
	"d" => ZZ => {"Degree of certain homogenous component of ring I."},
	"r" => ZZ => {"Length of the sequences in homogenous component of degree d."}
	},
   Outputs => {
       "i" => ZZ => {"Gives the Generalized minimum distance value of an ideal with parameters (d,r)."}
	},
	EXAMPLE {
	"K=ZZ/3;", 
        "R=K[t1,t2,t3,t4,t5,t6];",
        "I=ideal(t1*t6-t3*t4,t2*t6-t3*t5);",
        "gMdFunction(1,1,I)"
	}
 }   
 

 
 
 
 document {
   Key => {vasFunction , (vasFunction,ZZ,ZZ,Ideal)},
   Headline => "Gives the Vasconcelos function of an ideal with parameters (d,r)",
   Usage => "vasFunction (d,r,I)",
   Inputs => {
	"I" => Ideal => {"Graded ideal."},
	"d" => ZZ => {"Degree of certain homogenous component of ring I."},
	"r" => ZZ => {"Length of the sequences in homogenous component of degree d."}
	},
   Outputs => {
       "i" => ZZ => {"The Vasconcelos function of an ideal with parameters (d,r)"}
	},
	EXAMPLE {
	"K=QQ;", 
        "R=K[t1,t2,t3];",
        "I=ideal(t1^3,t2*t3);",
        "vasFunction(1,1,I)"
	}
 }


-----------------------------------------------
-----------------------------------------------
-- Use this section for Evaluation Code documentation:
-----------------------------------------------
-----------------------------------------------


document {
    Key => {cartesianCode, (cartesianCode,Ring,List,List), (cartesianCode,Ring,List,ZZ), (cartesianCode,Ring,List,Matrix)},
    Headline => "Constructs a Cartesian code.",
    Usage => "cartesianCode(F,L,S)\ncartesianCode(F,L,d)\ncartesianCode(F,L,M)",
    Inputs => {
	"F" => Ring => {"Field."},
	"L" => List => {"Sets of F to make a Cartesian product."},
	"S" => List => {"Sets of polynomials to evaluate."},
	"d" => ZZ => {"Polynomials up to dedree d will be evaluated."}, 
	"M" => Matrix => {"Matrix whose rows are the exponents of the monomials to evaluate."}
	},
    Outputs => {
	"C" => EvaluationCode => {"Cartesian code."}
	},
    "F is a field, L  is a list of sets of F and d is an integer",
    "Returns the Cartesian code obtained when polynomials up to degree d are evaluated over the points on the Cartesian product made by the sets of L.",
    EXAMPLE {
	"C=cartesianCode(ZZ/11,{{1,2,3},{2,6,8}},3);",
	"C.Sets",
	"C.VanishingIdeal",
	"C.PolynomialSet",
	"C.LinearCode",
	"length C.LinearCode"	
	}
    }

document {
    Key => {RMCode, (RMCode,ZZ,ZZ,ZZ)},
    Headline => "Constructs the Reed-Muller code.",
    Usage => "RMCode(q,m,d)",
    Inputs => {
	"q" => ZZ => {"Size of the field."},
	"m" => ZZ => {"Number of varibles."},
	"d" => ZZ => {"Polynomials up to dedree d will be evaluated."}	
	},
    Outputs => {
	"C" => EvaluationCode => {"Reed-Muller code."}
	},
    "q, m and d are integers",
    "Returns the Reed-Muller code obtained when polynomials in m variables up to total degree d are evaluated over the points on GF(q)^m.",
    EXAMPLE {
	"C=RMCode(2,3,4);",
	"C.Sets",
	"C.VanishingIdeal",
	"C.PolynomialSet",
	"C.LinearCode",
	"length C.LinearCode"
	}
    }

document {
    Key => {RSCode, (RSCode,Ring,List,ZZ)},
    Headline => "Constructs the Reed-Muller code.",
    Usage => "RMCode(F,L,k)",
    Inputs => {
	"F" => Ring => {"Finite field."},
	"L" => List => {"Elements of the field to evaluate."},
	"k" => ZZ => {"Polynomials of dedree less than k will be evaluated."}	
	},
    Outputs => {
	"C" => EvaluationCode => {"Reed-Solomon code."}
	},
    "F is a finite fiel, L={{a_1,...,a_n}} contains the elements to evaluate, polynomials of degree less than k are used to evaluate",
    "Returns the Reed-Solomon code obtained when polynomials of degree less than k are evaluated on the elements of L .",
    EXAMPLE {
	"C=RSCode(ZZ/31,{1,2,3},3);",
	"peek C"
	}
    }

document {
    Key => {orderCode, (orderCode,Ring,List,List,ZZ), (orderCode,Ideal,List,List,ZZ), (orderCode,Ideal,List,ZZ)},
    Headline => "Order codes.",
    Usage => "orderCode(F,P,G,d)\norderCode(I,P,G,d)\norderCode(I,G,d)\n",
    Inputs => {
	"F" => Ring => {"Finite field."},
	"P" => List => {"A list of points to evaluate."},
	"G" => List => {"A list of natural numbers."},
	"I" => Ideal => {"Ideal whose rational points will be evaluated."},
	"l" => ZZ  => {"Polynomials up to weigth l will be evaluated."}	
	},
    Outputs => {
	"C" => EvaluationCode => {"Order code."}
	},
    "F is a field, P is a list of points to evaluate, G is a list of natural numbers",
    "Returns the Evaluation code obtained when polynomials in #P variables up to weight l are evaluated over the points on P.",
    EXAMPLE {
	"F=GF(4);",
	"R=F[x,y];",
	"I=ideal(x^3+y^2+y);",
	"l=7;",
	"C=orderCode(I,{2,3},l);",
	"peek C"
	}
    }



       
       
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


