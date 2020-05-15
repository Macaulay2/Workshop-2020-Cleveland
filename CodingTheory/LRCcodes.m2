installPackage("CodingTheory",FileName=>"~/Workshop-2020-Cleveland/CodingTheory/CodingTheory.m2")
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
    F:=GF(#p.Alphabet);
    generatorS:=apply((entries gens F^(p.Dimension),i->apply(i,j->sub(j,F))));
    encodingPolynomials:=apply(generatorS,i->getEncodingPolynomial(p,i,g));
    informationSymbols:=flatten A;
    
    -- we evaluate each encoding polynomial at each of the symbols in A
    listOfGens:=apply(encodingPolynomials,i->apply(informationSymbols,j->sub(i[j],GF(#p.Alphabet))));
    
    --should check that the evaluation of each generator in listOfGens over the entries of each codeword 
    -- returns the same number of distinct images as there are subsets in the partition A.
    setSizes:=apply(listOfGens,i-># set apply(i, j-> sub(sub(g[j],GF(#p.Alphabet)),ZZ)));
    if not all (setSizes, Sizes-> Sizes<=#A) then error "Something went wrong";
    
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
      i:=toList(0..(p.Locality-1));
      coeffs:=apply(i,l->getCoefficientPolynomial(p,infVec,g,l));
      polynoms:=apply(i,l->(sub(x,GF(#p.Alphabet)[x])^l);
      sum apply(i,l->coeffs_l*polynoms_l)
     )

getCoefficientPolynomial = method(TypicalValue => RingElement)
getCoefficientPolynomial(TargetParameters,List,RingElement,ZZ) := RingElement => (p,infVec,g,i) -> (
     -- generates the coefficient polynomial for an LRC code
      -- input:    the TargetParameters hash table p, a list infVec in F^k, a good polynomial g
      --               in the ring F[x], an increment i
      -- output:   the coefficient polynomial for an information vector in F^k  
      
      j:=toList(0..(p.Dimension//p.Locality-1));
      coeffs:=flatten apply(j,l->infVec_{i*2+l});
      polynoms:=apply(j,l->g^l);
      sum apply(j,l->coeffs_l*polynoms_l)
     )
 


----------------------------------------------------------
--           Good Polynomials for Partitions of symbols
--                (group theoretical constructions
----------------------------------------------------------

 
goodPolynomial = method(Options=>{})
goodPolynomial(ZZ,List) := RingElement -> (q,A) -> (
    -- generates a good polynomial for a partition of symbols in finite field F=F_q
    -- by utilizing the multiplicative group structure of F\0
    -- input:    field size q a prime, partition A of symbols in F\0
    -- output:   a polynomial function f such that the image of each point in a given 
    --          subset in A is the same.
    
)

getGroupAnnihilatorPolynomial = method(TypicalValue => RingElement)
getGroupAnnihilatorPolynomial(List,ZZ) := RingElement => (G,q) -> (
    x:=symbol x;
    i:=toList(0..(#G-1));
    product(apply(i,inc->(sub(x,GF(q)[x])-G_inc)))
    )


--------------------------------------------- Test example
--   restart
--  
--   p = targetParameters(13,9,4,2)
--   A = { {1,3,9}, {2,6,5}, {4,12,10} }
--   R = GF(#p.Alphabet)[x]
--   g = x^3
--   LRCencoding(p,A,g)

-------------------------   END   MATT
--------------------------------------------

