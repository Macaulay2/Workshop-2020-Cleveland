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
    -- Methods
    "field",
    "vectorSpace",
    "codeDim",
    "codeLength",
    "ambientSpace",
    "informationRate",
    "dualCode",
    "alphabet",
    "shortestPath",
    "minimumWeight",
    "matroidPartition",
    "weight"
    
    }

exportMutable {}
needsPackage "Graphs";
needsPackage "Matroids";

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
  
    -- note: need to add checks that the codewords live in the ambient module
     
    new LinearCode from {
	symbol AmbientModule => S,
	symbol BaseField => S.ring,
	symbol Generators => V.gens,
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

net LinearCode := c -> (
     "Code: " | net c.Code
     )
toString LinearCode := c -> toString c.Generators
 
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
    return ring(C.AmbientModule);
    )

--input: A linear code C
--output: The vector space spanned by the generators of C
vectorSpace = method(TypicalValue => Module)
vectorSpace LinearCode := Module => C -> (
    return C.Code;
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
length LinearCode := Number => C -> (
    return rank(C.AmbientModule);
    )

--input: A linear code C
--output: The vector space dimension of the subspace given by the
--span of the generators of C
dim LinearCode := Number => C -> (
    return rank C.Code;
    )

--input: A linear code C
--output: The ratio (dim C)/(length C)
informationRate = method(TypicalValue => Number)
informationRate LinearCode := Number => C -> (
    return (dim C)/(length C);
    )

dualCode = method()
dualCode(LinearCode) := LinearCode => C -> (
    -- creates dual code to code C
    -- defn: the dual C^ is the code given by all c'
    -- such that c'.c == 0 for all c in C.
    linearCode(dual cokernel gens C.Code)
    )

alphabet = method()
alphabet(LinearCode) := List => C -> (
    -- "a" is the multiplicative generator of the
    -- field that code C is over
    a := C.BaseField.generators_0;
    
    -- take 0, and compute non-zero elements of C.BaseField:
    alphaB := {sub(0,C.BaseField)} | apply(toList(1..(C.BaseField.order-1)), i-> a^i);
    
    -- return this alphabet:
    alphaB    
    )

--Perform BFS to find shortest path between a vertex and a set of
--vertices in a digraph
shortestPath = method(TypicalValue => List)
shortestPath (Digraph, Thing, List) := List => (D,start,finishSet) -> (
    V    := vertexSet(D);
    assert(member(start, V));
    r    := length vertexSet(D);
    --just pick some dummy variable to initialize predecessor array
    local dummy;
    dummy = symbol dummy;
    pred := new MutableHashTable from apply(V,i-> i=>dummy);
    dist := new MutableHashTable from apply(V,i-> i=>infinity);
    visited := new MutableHashTable from apply(V,i-> i=>false);
    dist#start = 0;
    visited#start = true;
    queue := {start};
    
    while not queue == {} do (
    	v := first queue;
	queue = drop(queue,1);
	for u in elements children(D,v) do (
	    if (visited#u) == false 
	    then (
		visited#u = true;
	    	dist#u = (dist#v) + 1;
		pred#u = v;
	    	queue=append(queue,u);
	    	if member(u, finishSet) 
	    	then (
		    P := {u};
		    back := u;
		    while(not (pred#back) === dummy) do (
		    	P = prepend(pred#back,P);
		    	back = pred#back;
		    );
		return P;
		);
	    );
	);
    );
    return {};
)

--input: A list of matroids with the same ground set
--output: A partition if possible. Otherwise, the emptylist.
matroidPartition = method(TypicalValue => List)
matroidPartition List := List => mls -> (
    --check to make sure list of matroids with same ground set
    r   := length mls;
    assert(all(0..r-1, i-> instance(mls_i,Matroid)));
    E   := (mls_0).groundSet;
    assert(all(0..r-1, i->((mls_i).groundSet)===E));
    
    --set up initial values: special symbols z and list of lists that'll hopefully become our partition
    local z;
    Z   := apply(new List from 1..r, i-> symbol z_i);
    Els := new MutableList from prepend(elements(E),apply(new List from 1..r, i->{}));
    
    
    --function to make relation for the digraph
    arrow := (x,y) -> (
	if (member(y,Els#0) or member(x,Z) or x===y) then return 0;
	if member(y,Z) 
	then if (not isDependent(mls_(((baseName y)#1)-1),append(Els#((baseName y)#1),x)))
	    then return 1
	    else return 0
	else (
	    j := first select(1..r, i->member(y,Els#i));
	    if not isDependent(mls_(j-1),append(delete(y,Els#j),x)) 
	    then return 1
	    else return 0
	    )
    );
    
    --Once shortest path is found between x and z_j, update the partition!
    repaint := (P,Els) -> (
	l := (length P)-2;
	for i from 1 to l do (
	    --We are traversing the path a 2-tuple at a time starting with (P_0,P_1)
	    --We want to replace P_i from its current set of partition with P_(i-1) until we get to some element of Z
	    j1 := first select(0..r,k->member(P_(i-1),Els#k));
	    j2 := first select(0..r,k->member(P_i,Els#k));
	    Els#j1 = delete(P_(i-1),Els#j1);
	    Els#j2 = append(Els#j2,P_(i-1));
	    );
	--P_(i-1) is a z_j, so just rip off index
	j1 := first select(0..r,k->member(P_l,Els#k));
	Els#j1 = delete(P_l,Els#j1);
	Els#((baseName P_(l+1))#1) = append(Els#((baseName P_(l+1))#1),P_l);
	);
    
    --unless we've exhausted elements, try to make a partition!
    while not (Els#0) == {} do (
	newVertex   := first first Els;
	constructed := mingle drop(Els,1);
	V   := join({newVertex},constructed, Z);
    	M   := matrix for x in V list for y in V list arrow(x,y);
	D   := digraph(V,M);
	if any(1..r, i->isReachable(D,Z_(i-1),newVertex))
	then repaint(shortestPath(D,newVertex,Z),Els)
	--WOMP. No partition.
	else return {};
    );
    --We found a partition! Now sort it by length, largest to smallest
    return apply(rsort apply(new List from drop(Els,1),i->(#i,i)),i->i_1);
)

reduceMatrix = method(TypicalValue => Matrix)
reduceMatrix(Matrix) := Matrix => M -> (
   -- check if matrix is of full rank:
   if (rank M == min(rank M.source,rank M.target)) then {
    return M
    } else return transpose gb transpose M
   )

weight = method(TypicalValue => Number)
weight BasicList := Number => c -> (
    sum(new List from (apply(0..length c-1, i-> if c_i == 0 then 0 else 1)))
    )

ambientWords = method(TypicalValue => List)
ambientWords LinearCode := List => C -> (
    S := C.AmbientModule;
    apply(toList(toList (set(alphabet C))^**(length C.Generators)/deepSplice), i->toList i)
    )

minimumWeight = method(TypicalValue => Number)
minimumWeight LinearCode := Number => C -> (
    M := matrix C.Generators;
    F := C.BaseField;
    k := length C.Generators; --Assumes generators are linearly independent?
    n := length C;
    l := ceiling(n/k);
    D := l; --D could probably be modified to be better
    w := 1;
    j := 1;
    
    --Partition columns of LinearCode into information sets
    T := matroidPartition(apply(toList(1..l),i->matroid(M)));
    
    r := {}; --list of relative ranks
    currentUnion := set();
    for i from 0 to length T-1 do (
	r = append(r,#(T_i-currentUnion));
	currentUnion = currentUnion + set(T_i);
	);
    nonzeroWords := delete(apply(1..k,i->0),ambientWords(C));
    
    dupper := n-k+1; --Start with Singleton Bound
    dlower := 0;
    while(true) do (
        permutation := join(T_(j-1),toList(0..n-1)-set(T_(j-1)));
        G := reduceMatrix(M_permutation);
        sameWeightWords := select(nonzeroWords, u -> weight(toList u) == w);
        specialCodewords := apply(sameWeightWords, u -> flatten entries ((matrix {toList u})*G));
        dupper = min(append(apply(specialCodewords, i->weight i),dupper));
        dlower = sum(toList apply(1..j,i->max(0,w+1-k+r_(i-1))))+sum(toList apply(j+1..D,i->max(0,w-k+r_(i-1))));
        if dlower >= dupper
    	then return dlower
    	else (if j < D then j = j+1
	    else w = w+1);
    	if w > k then error "No minimum weight found.";
    )
)
    
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