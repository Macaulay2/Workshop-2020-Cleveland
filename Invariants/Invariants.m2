-- -*- coding: utf-8 -*-
newPackage(
        "Invariants",
        Version => "0.1", 
        Date => "May 13, 2020",
        Authors => {
             {Name => "Luigi Ferraro", Email => "ferrarl@wfu.edu", HomePage => "http://users.wfu.edu/ferrarl/"},
             {Name => "Federico Galetto", Email => "f.galetto@csuohio.edu", HomePage => "https://math.galetto.org"},
<<<<<<< HEAD
             {Name => "Francesca Gandini", Email => "fra.gandi.phd@gmail.com", HomePage => "https://sites.google.com/a/umich.edu/gandini/home"},
	     {Name => "Hang Huang", Email => "hhuang235@tamu.edu", HomePage => "https://math.tamu.edu/~hhuang"},
	     {Name => "Matthew Mastroeni", Email => "mmastro@okstate.edu", HomePage => "https://mnmastro.github.io/"},
             {Name => "Xianglong Ni", Email => "xlni@berkeley.edu", HomePage => "https://math.berkeley.edu/~xlni/"}
=======
             {Name => "Xianglong Ni", Email => "xlni@berkeley.edu", HomePage => "https://math.berkeley.edu/~xlni/"},
	     {Name => "Hang Huang", Email => "hhuang235@tamu.edu", HomePage => "https://math.tamu.edu/~hhuang"}
>>>>>>> d16bfad0cb6eb0ff5c9dee2c48531736d012b20a
             },
        Headline => "Computing Invariants for Tori and Abelian Groups",
        DebuggingMode => true,
        AuxiliaryFiles => false
        )

-- Any symbols or functions that the user is to have access to
-- must be placed in one of the following two lists
export {
    "action",
    "finiteAction",
    "groupGens",
    "invariants",
    "invariantRing",
    "isAbelian",
    "torusAction",
    "weights",
    "abelianInvariants",
    "hilbertIdeal",
    "generatorsFromHilbertIdeal",
    "linearInvariants",
    "isInvariant"
    }
--exportMutable {}

--Protect Option/hashtable symbols
protect Action
protect AmbientRing
protect basering
protect Generators
protect RepDimension
protect TorusRank
protect WeightMatrix

needsPackage("Polyhedra", Reload => true)
needsPackage("Elimination", Reload => true)


GroupAction = new Type of MutableHashTable
FiniteGroupAction = new Type of GroupAction
TorusAction = new Type of GroupAction
RingOfInvariants = new Type of Ring    	       -- For some reason, InvariantRing already seems to be a protected symbol.


-------------------------------------------
--- FiniteGroupAction methods -------------
-------------------------------------------

net FiniteGroupAction := G -> net G.Generators

finiteAction = method()

finiteAction List := FiniteGroupAction => G -> (
    new FiniteGroupAction from {basering => ring first G, Generators => G, RepDimension => numColumns first G}
    )

groupGens = method()

groupGens FiniteGroupAction := List => G -> G.Generators 

numgens FiniteGroupAction := ZZ => G -> #(groupGens G)

dim FiniteGroupAction := ZZ => G -> G.RepDimension

ring FiniteGroupAction := Ring => G -> G.basering

isAbelian = method()

isAbelian FiniteGroupAction := Boolean => G -> (
    X := groupGens G;
    n := #X;
    if n == 1 then(
	return true 
	)
    else(
	all(n - 1, i -> all(n - 1 - i, j -> (X#j)*(X#(n - 1 - i)) == (X#(n - 1 - i))*(X#j) ) )
	)
    )


-------------------------------------------
--- TorusAction methods -------------------
-------------------------------------------

torusAction = method()

torusAction Matrix := TorusAction => W -> (
    new TorusAction from {WeightMatrix => W, TorusRank => numRows W, RepDimension => numColumns W}
    )

net TorusAction := T -> net (T.WeightMatrix)

dim TorusAction := ZZ => T -> T.RepDimension

rank TorusAction := ZZ => T -> T.TorusRank

weights = method()

weights TorusAction := Matrix => T -> T.WeightMatrix 



-------------------------------------------
--- RingOfInvariants methods --------------
-------------------------------------------

net RingOfInvariants := B -> (
    R := ambient B;
    G := action B;
    if instance(G, TorusAction) then (net R)|" <-- "|(net action B)
    else net R
    )

invariantRing = method()

invariantRing (TorusAction, PolynomialRing) := RingOfInvariants => (T, R) -> (
    new RingOfInvariants from {AmbientRing => R, Action => T }
    )

PolynomialRing^TorusAction := RingOfInvariants => (R, T) -> invariantRing(T, R)

action = method()

action RingOfInvariants := GroupAction => B -> B.Action

ambient RingOfInvariants := PolynomialRing => B -> B.AmbientRing

-------------------------------------------

invariants = method()

invariants RingOfInvariants := B -> invariants(action B, ambient B)

invariants (TorusAction, PolynomialRing) := List => (T, R) -> (
    r := rank T; -- r is the dimension of the torus
    n := dim R; -- n is the dimension of the ring R
    if (n =!= rank source vars R) then (error "invariants: Dimension of the polynomial ring does not match size of the weight matrix");
    W := weights T;
    local C;
    if r == 1 then C = convexHull W else C = convexHull( 2*r*W|(-2*r*W) );
    C = (latticePoints C)/vector; -- C is a list of weights we are testing
    S := new MutableHashTable from apply(C, w -> w => {});
    scan(n, i -> S#(W_i) = {R_i});
    U := new MutableHashTable from S;
    local v, local m, local v', local u;
    nonemptyU := select(keys U, w -> #(U#w) > 0);
    --iteration := 0; --step by step printing
    while  #nonemptyU > 0 do(
	v = first nonemptyU;
	m = first (U#v);
	
	-- Uncomment lines in step by step printing to see steps
	-- Note: there is one such line before the while loop
	--print("\n"|"Iteration "|toString(iteration)|".\n"); --step by step printing
    	--print(net("    Weights: ")|net(W)); --step by step printing
	--print("\n"|"    Set U of weights/monomials:\n"); --step by step printing
	--print(net("    ")|net(pairs select(hashTable pairs U,l->l!= {}))); --step by step printing
	--print("\n"|"    Set S of weights/monomials:\n"); --step by step printing
	--print(net("    ")|net(pairs select(hashTable pairs S,l->l!= {}))); --step by step printing
	--iteration = iteration + 1; --step by step printing
	
	scan(n, i -> (
        u := m*R_i;
        v' := v + W_i;
        if ((U#?v') and all(S#v', m' -> u%m' =!= 0_R)) then( 
                S#v' = S#v'|{u};
                U#v' = U#v'|{u};
		)
	    )
	);
	U#v = delete(m, U#v);
	nonemptyU = select(keys U, w -> #(U#w) > 0)
	);
    return S#(0_(ZZ^r))
    )

-------------------------------------------
-- No FiniteAbelianAction type exists yet

abelianInvariants = method()
abelianInvariants (Matrix, PolynomialRing, List) := List => (W, R, L) -> (
    r := numRows W;
    n := numColumns W;
    t := 1; -- t is the size of abelian group
    --sanity check 
    if #L =!= r then error "Size of the group does not match the weight matrix";
    scan(L,i->t = t*i);
    local C; -- C is a list of all possible weights
    for i from 0 to #L-1 do(
	if i == 0 then(
	    C = apply(L_i,j-> matrix {{j}});
	) else (
	temp := flatten apply(L_i,j->apply(C,M->M || matrix {{j}}));
	C = temp;
        );
    );
    S := new MutableHashTable from apply(C, w -> w => {});
    scan(n, i -> S#(W_i) = {R_i});
    U := flatten entries vars R;
    local v, local m, local u, local v';
    while  #U > 0 do(
    m = min U; 
    v = vector(apply(n,i->degree(R_i,m))); --degree vector of m
    v = W*v; --weight vector of m
    j := 0;
    scan(n,i->if m % R_i == 0 then (j = i+1;break));
    k := j;
    while k > 0 do(
        u = m*R_(k-1);
        temp := flatten entries (v + W_(k-1));
	temp = apply(#temp,i -> temp_i % L_i);
	v' = matrix(vector temp);
        if all(S#v', m' -> u%m' =!= 0_R) then (
	    S#v' = S#v'|{u};
            if first degree u < t then(
		U = U | {u};
            );
        );
        k = k - 1;
    );
    U = delete(m, U);
    );
    return S#(matrix(0_(ZZ^r)))
)

hilbertIdeal = method()
hilbertIdeal (Ideal, Matrix, PolynomialRing) := Ideal => (A, M, R) -> (
    if (numColumns M =!= numRows M) or (numRows M =!= #(gens R)) then print "Matrix size does not match polynomial ring";
    -- first, some information about the inputs:
    n := #(gens R);
    K := coefficientRing(R);
    l := #(gens ring M);
    
    -- now make the enlarged polynomial ring we'll work in, and convert inputs to that ring
    x := local x, y := local y, z := local z;
    S := K[x_1..x_n, y_1..y_n, z_1..z_l]; -- this results in an error.. trying to fix
    M' := sub(M, apply(l, i -> (ring M)_i => z_(i+1)));
    A' := sub(A, apply(l, i -> (ring M)_i => z_(i+1)));
    
    -- the actual algorithm follows
    J' := apply(n, i -> y_(i+1) - sum(n, j -> M'_(j,i) * x_(j+1)));
    J := A' + ideal(J');
    I := eliminate(apply(l, i -> z_(i+1)),J);
    II := sub(I, apply(n, i -> y_(i+1) => 0));
    
    -- return the result back in the user's input ring R
    return trim(sub(II, join(apply(n, i -> x_(i+1) => R_i),apply(n, i -> y_(i+1) => 0), apply(l, i -> z_(i+1) => 0))))
)

generatorsFromHilbertIdeal = method(TypicalValue => List)
generatorsFromHilbertIdeal (Ideal, Matrix, Ideal) := List => (A, M, I) -> (
    R := ring(I);
    if (numColumns M =!= numRows M) or (numRows M =!= #(gens R)) then print "Matrix size does not match polynomial ring";
    x := local x, z := local z;
    n := numColumns M;
    K := coefficientRing(ring(I));
    l := #(gens ring M);
    X := K[x_1..x_n];
    
    I' := flatten entries gens sub(I, apply(n, i -> (ring I)_i => x_(i+1)));
    
    S := K[x_1..x_n, z_1..z_l];
    M' := sub(M, apply(l, i -> (ring M)_i => z_(i+1)));
    A' := sub(A, apply(l, i -> (ring M)_i => z_(i+1)));
    
    degreeList := sort toList set apply(I', i -> first degree i);
    generatorList := {};
    
    local d;
    while (#degreeList > 0) do(
	d = degreeList#0;
    	Id := select(I', i -> first degree i == d);
	
	alreadyInv := true;
	j := 0;
	while alreadyInv and Id#?j do(
	    if not isInvariant(A,M,Id#j) then alreadyInv = false;
	    j = j+1
	);
    	if not alreadyInv then (
	    L := sub(basis(d,X), S);
    	    r := numColumns L;
    	    NFDL := apply(r, i -> (sub(L_(0,i), apply(n, j -> x_(j+1) => sum(n, k -> M'_(k,j) * x_(k+1)))) - L_(0,i)) % A');
    	    monomialsNFDL := flatten entries monomials(matrix{NFDL});
    	    m := #monomialsNFDL;
    	    B := matrix(apply(m, i -> apply(r, j -> coefficient(monomialsNFDL#i, NFDL#j))));
    	    KB := gens kernel B;
	    generatorList = join(generatorList, flatten entries sub(L * KB, join(apply(n, i -> x_(i+1) => R_i), apply(l, i -> z_(i+1) => 0))))
	) else (
	    use X;
	    generatorList = join(generatorList, apply(Id, f -> sub(f, apply(n, i -> x_(i+1) => R_i))));
	    use S
	);
    	degreeList = drop(degreeList,1)
    );
    return generatorList
)

manualTrim = method(TypicalValue => List)
manualTrim (List) := List => L -> (
    L' := {0_(ring L#0)};
    
    scan(#L, i -> (
	if not (L#i % ideal(L') == 0) then L' = append(L', L#i)
    ));
    return drop(L',1)
)

linearInvariants = method(TypicalValue => List)
linearInvariants (Ideal, Matrix, PolynomialRing) := List => (A,M,R) -> (
    return manualTrim generatorsFromHilbertIdeal(A,M,hilbertIdeal(A,M,R))
)

isInvariant = method(TypicalValue => Boolean)
isInvariant (Ideal, Matrix, Thing) := Boolean => (A, M, f) -> (
    R := ring(f);
    if (numColumns M =!= numRows M) or (numRows M =!= #(gens R)) then print "Matrix size does not match polynomial ring";
    x := local x, z := local z;
    n := numColumns M;
    K := coefficientRing(ring(f));
    l := #(gens ring M);
    
    S := K[x_1..x_n, z_1..z_l];
    M' := sub(M, apply(l, i -> (ring M)_i => z_(i+1)));
    A' := sub(A, apply(l, i -> (ring M)_i => z_(i+1)));
    f' := sub(f, apply(n, i -> (ring(f))_i => x_(i+1)));
    Gf' := sub(f, apply(n, i -> (ring(f))_i => sum(n, j -> M'_(j,i) * x_(j+1))));
    return ( (Gf' - f') % A' == 0 )
)
isInvariant (Matrix, Thing) := Boolean => (W,f) -> (
    return W * transpose(matrix(exponents(f))) == 0
)
isInvariant (Matrix, List, Thing) := Boolean => (W,L,f) -> (
    V := W * transpose(matrix(exponents(f)));
    n := numColumns W;
    return apply(n, i -> (V#i)%(L#i)) == 0
)

beginDocumentation()
document { 
	Key => Invariants,
	Headline => "Computing Invariants for Tori and Abelian Groups",
	EM "Invariants", " is a package implementing algorithms
	to compute invariants of reductive groups.",
	PARA {
	    "Current algorithms include:"
	    },
	UL { 
	    {"A fast algorithm for invariants of finite abelian groups based on: ",
		"Gandini, F. ",
		HREF{"https://deepblue.lib.umich.edu/handle/2027.42/151589","Ideals of Subspace Arrangements"}, 
	   	". Thesis (Ph.D.)-University of Michigan. 2019. ISBN: 978-1392-76291-2. pp 29-34."
		},
	    {"A fast algorithm for invariants of tori based on: ",
		"Derksen, H. & Kemper, G. (2015). ",
		HREF{"https://link.springer.com/book/10.1007%2F978-3-662-48422-7","Computational Invariant Theory"}, 
	   	". Heidelberg: Springer. pp 174-177"
		}
        }
	}
 -*
document {
	Key => {torusInvariants, (torusInvariants,Matrix,PolynomialRing)},
	Headline => "Computes the primary invariants for a diagonal torus action given by column weight vectors",
	Usage => "torusInvariants(W,R)",
	Inputs => {  
	    	"R" => PolynomialRing => {"on which the torus acts diagonally"},
		"W" => Matrix => {"whose ith column is the weight vector of ", TT "R_i"}
		},
	Outputs => {
		List => {"A minimal set of generating invariants for the torus action"}
		},
	SeeAlso => {abelianInvariants},
	PARA {
	    "This function is provided by the package ", TO Invariants, ". It implements an algorithm by Derksen and Kemper for computing a minimal set of generating invariants for an action of a torus",
	    TEX /// $(k^\times)^r$ ///,
	    " on a polynomial ring ",
	    TEX /// $R = k[x_1,\ldots,x_n]$.///,
	    " We assume that the torus action is diagonal, in the sense that ",
	    TEX /// $(t_1,\ldots,t_r) \in (k^\times)^r$ ///,
	    " acts by",
	    TEX /// $$(t_1,\ldots,t_r) \cdot x_j = t_1^{w_{1j}}\cdots t_r^{w_{rj}} x_j$$ ///,
	    "for some integers ",
	    TEX /// $w_{ij}$. ///,
	    "These are the entries of the input matrix ", TT "W", ". In other words, the j-th column of ", TT "W", " is the weight vector of",
	    TEX /// $x_j$. ///
	},
    	PARA {
	    "Here is an example of a one-dimensional torus acting on a two-dimensional vector space:"
	},
    	EXAMPLE {
		"torusInvariants(matrix{{1,-1}}, QQ[x_1,x_2])"
		},
      
	UL { 
	    {"Derksen, H. & Kemper, G. (2015). ", EM "Computational Invariant Theory", 
	   ". Heidelberg: Springer. pp 174-177"}
        }	
}
*-
document {
	Key => {abelianInvariants, (abelianInvariants,Matrix,PolynomialRing,List)},
	Headline => "Computes the primary invariants for an abelian group action given by column weight vectors",
	Usage => "abelianInvariants(W,R,L)",
	Inputs => {
	        "L" => List => {"whose entries are the cardinalities of the cyclic group factors of the abelian group"},
	    	"R" => PolynomialRing => {"on which a group acts diagonally"},
		"W" => Matrix => {"whose ith column is the weight vector of ", TT "R_i"}
		},
	Outputs => {
		List => {"A minimal set of generating invariants for the abelian group action"}
		},
	SeeAlso => {invariants},
	PARA {
	    "This function is provided by the package ", TO Invariants, ". It is based on the same algorithm as ", TO invariants,
	    " with some adjustments and optimizations for the finite group case; see the reference below for details. Writing the finite abelian group as",
	    TEX /// $\mathbb{Z}/d_1 \oplus \cdots \oplus \mathbb{Z}/d_r$, ///,
	    "the input ", TT "L", " is the list ", TT "{d_1,d_2,...,d_r}", ". We assume that the group acts diagonally on the input polynomial ring",
	    TEX /// $R = k[x_1,\ldots,x_n]$, ///,
	    "which is to say that if we denote the evident generators of the group by",
	    TEX /// $g_1,\ldots,g_r$ ///,
	    "then we have",
	    TEX /// $$g_i \cdot x_j = \zeta_i^{w_{ij}} x_j$$ ///,
	    "for",
	    TEX /// $\zeta_i$ ///,
	    "a primitive",
	    TEX /// $d_i$///,
	    "-th root of unity. The integers",
	    TEX /// $w_{ij}$ ///,
	    "comprise the input matrix ", TT "W", "."
	},
        UL { 
	    {"Gandini, F. ", EM "Ideals of Subspace Arrangements", 
	   ". Thesis (Ph.D.)-University of Michigan. 2019. ISBN: 978-1392-76291-2. pp 29-34."}
        },
    	PARA {
	    "Here is an example of a product of two cyclic groups of order 3 acting on a three-dimensional vector space:"
	},
	
	EXAMPLE {
	    "R = QQ[x_1..x_3]",
	    "W = matrix{{1,0,1},{0,1,1}}",
	    "abelianInvariants(W,R,{3,3})"
		}
	}
document {
	Key => {hilbertIdeal, (hilbertIdeal,Ideal,Matrix,PolynomialRing)},
	Headline => "Computes generators (possibly non-invariant) for the invariant ideal",
	Usage => "hilbertIdeal(A,M,R)",
	Inputs => {
	        "A" => Ideal => {"of some polynomial ring ", TT "S", " defining the group as an affine variety"},
	    	"R" => PolynomialRing => {"on which the group acts"},
		"W" => Matrix => {"whose entries are in ", TT "S", ", that encodes the group action"}
		},
	Outputs => {
		Ideal => {"the ideal of ", TT "R", " generated by the invariants (note that the generators of I are likely non-invariant)"}
		},
	"This function is provided by the package ", TO Invariants,
	". The hope is that this function will used to compute actual generating invariants, but the crucial step is still missing (the Reynolds operator). For now, it outputs the ideal generated by the invariants in the polynomial ring, as the following example illustrates.",
	
	EXAMPLE {
		"S = QQ[z]",
		"hilbertIdeal(ideal(z^2 - 1), matrix{{(z+1)/2, (1-z)/2},{(1-z)/2, (z+1)/2}}, QQ[x,y])"
		},
	
	UL { 
	    {"Derksen, H. & Kemper, G. (2015).", EM "Computational Invariant Theory", 
	   ". Heidelberg: Springer. pp 159-164"}
        }
}

document {
	Key => {action, (action,RingOfInvariants)},
	Headline => "Group action that produced a certain ring of invariants",
	Usage => "action(R)",
	Inputs => {
	    	"R" => RingOfInvariants => {"of the group action being returned"},
		},
	Outputs => {
		GroupAction => {"the action that produced the ring of invariants in the input"}
		},
	"This function is provided by the package ", TO Invariants,".",
	
	EXAMPLE {
		"R=QQ[x_1..x_4]",
		"T=torusAction matrix{{0,1,-1,1},{1,0,-1,-1}}",
		"S=R^T",
		"action S"
		},
}

document {
	Key => {finiteAction, (finiteAction,List)},
	Headline => "Group action generated by a list of matrices",
	Usage => "finiteAction(L)",
	Inputs => {
	    	"L" => List => {"of matrices representing elements of a finite group"},
		},
	Outputs => {
		GroupAction => {"the action of the (finite) matrix group generated by the input list"}
		},
	"This function is provided by the package ", TO Invariants,".",
	
	EXAMPLE {
		"L={matrix{{0,1,0},{1,0,0},{0,0,1}},matrix{{0,0,1},{0,1,0},{1,0,0}}}",
		"finiteAction L"
		},
}

TEST ///
R1 = QQ[x_1..x_4]
T1 = torusAction matrix {{-3, -1, 1, 2}}
invariants1 =  set {x_2*x_3, x_2^2*x_4, x_1*x_3*x_4, x_1*x_2*x_4^2, x_1^2*x_4^3, x_1*x_3^3}
assert(set invariants(T1, R1) === invariants1)
///

TEST ///
R2 = QQ[x_1..x_4]
T2 = torusAction matrix{{0,1,-1,1},{1,0,-1,-1}}
invariants2 = set {x_1*x_2*x_3,x_1^2*x_3*x_4}
assert(set invariants(T2,R2) === invariants2)
///
       
end

-- Here place M2 code that you find useful while developing this
-- package.  None of it will be executed when the file is loaded,
-- because loading stops when the symbol "end" is encountered.

restart
uninstallPackage "Invariants"
installPackage "Invariants"
--installPackage("Invariants", RemakeAllDocumentation=>true)
check Invariants

-- Local Variables:
-- compile-command: "make -C $M2BUILDDIR/Macaulay2/packages PACKAGES=Invariants pre-install"
-- End:

needsPackage "Invariants"
S = QQ[z]
A = ideal(z^2 - 1)
M = matrix{{(1+z)/2, (1-z)/2},{(1-z)/2, (1+z)/2}}
R = QQ[a,b]
I = hilbertIdeal(A,M,R)
generatorsFromHilbertIdeal(A,M,I)
linearInvariants(A,M,R)
