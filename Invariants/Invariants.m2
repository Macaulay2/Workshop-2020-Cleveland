-- -*- coding: utf-8 -*-
newPackage(
        "Invariants",
        Version => "1.0", 
        Date => "May 12, 2020",
        Authors => {
             {Name => "Luigi Ferraro", Email => "ferrarl@wfu.edu",
              HomePage => "http://users.wfu.edu/ferrarl/"},
             {Name => "Federico Galetto", Email => "f.galetto@csuohio.edu", HomePage => "https://math.galetto.org"},
             {Name => "Xianglong Ni", Email => "xlni@berkeley.edu", HomePage => "https://math.berkeley.edu/~xlni/"}
             },
        Headline => "Computing Invariants for Tori and Abelian Groups",
        DebuggingMode => true,
        AuxiliaryFiles => false
        )

-- Any symbols or functions that the user is to have access to
-- must be placed in one of the following two lists
export {
    "torusInvariants",
    "abelianInvariants",
    "linearInvariantIdeal",
    "firstFunction",
    "secondFunction",
    "MyOption"
    }
exportMutable {}

needsPackage("Polyhedra", Reload => true)
needsPackage("Elimination", Reload => true)

torusInvariants = method()
torusInvariants (Matrix, PolynomialRing) := List => (W, R) -> (
    r := numRows W;
    n := numColumns W;
    local C;
    if r == 1 then C = convexHull W else C = convexHull( 2*r*W|(-2*r*W) );
    C = (latticePoints C)/vector;
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

abelianInvariants = method()
abelianInvariants (Matrix, PolynomialRing, List) := List => (W, R, L) -> (
    r := numRows W;
    n := numColumns W;
    t := 1; -- t is the size of abelian group
    --sanity check 
    if #L =!= r then print "Size of the group does not match the weight";
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
        u := m*R_(k-1);
        temp := flatten entries (v + W_(k-1));
	temp = apply(#temp,i -> temp_i % L_i);
	v' := matrix(vector temp);
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

linearInvariantIdeal = method()
linearInvariantIdeal (Ideal, Matrix, PolynomialRing) := Ideal => (A, M, R) -> (
    if (numColumns M =!= numRows M) or (numRows M =!= #(gens R)) then print "Matrix size does not match polynomial ring";
    -- first, some information about the inputs:
    n := #(gens R);
    K := coefficientRing(R);
    l := #(gens ring M);
    
    -- now make the enlarged polynomial ring we'll work in, and convert inputs to that ring
    local x, local y, local z;
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

beginDocumentation()
document { 
	Key => Invariants,
	Headline => "Computing Invariants for Tori and Abelian Groups",
	EM "Invariants", " is an example package which can
	be used as a template for user packages."
	}
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
	UL { 
	    {"Derksen, H. & Kemper, G. (2015). ", EM "Computational Invariant Theory", 
	   ". Heidelberg: Springer. pp 174-177"}
        },

	EXAMPLE {
		"torusInvariants(matrix{{1,-1}}, QQ[x_1,x_2])"
		}
	}
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
	
	PARA {
	    "This function is provided by the package ", TO Invariants, ". It is based on the same algorithm as ", TO torusInvariants,
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
	
	EXAMPLE {
		"0; -- none yet!"
		}
	}
document {
	Key => {linearInvariantIdeal, (linearInvariantIdeal,Ideal,Matrix,PolynomialRing)},
	Headline => "Computes generators (possibly non-invariant) for the invariant ideal",
	Usage => "linearInvariantIdeal(A,M,R)",
	Inputs => {
	        "A" => Ideal => {"of some polynomial ring ", TT "S", " defining the group as an affine variety"},
	    	"R" => PolynomialRing => {"on which the group acts"},
		"W" => Matrix => {"whose entries are in ", TT "S", ", that encodes the group action"}
		},
	Outputs => {
		Ideal => {"the ideal of ", TT "R", " generated by the invariants (note that the generators of I are likely non-invariant)"}
		},
	"This function is provided by the package ", TO Invariants, ". The hope is that this function will used to compute actual generating invariants, but the crucial step is still missing (the Reynolds operator).",
	
	UL { 
	    {"Derksen, H. & Kemper, G. (2015).", EM "Computational Invariant Theory", 
	   ". Heidelberg: Springer. pp 159-164"}
        },
	
	EXAMPLE {
		"S = QQ[z]"
--		"linearInvariantIdeal(ideal(z^2 - 1), matrix{{(z+1)/2, (1-z)/2},{(1-z)/2, (z+1)/2}}, QQ[x,y])"
		}
	}

TEST ///

R1 = QQ[x_1..x_4]
W1 = matrix {{-3, -1, 1, 2}}
invariants1 =  set {x_2*x_3, x_2^2*x_4, x_1*x_3*x_4, x_1*x_2*x_4^2, x_1^2*x_4^3, x_1*x_3^3}
assert(set torusInvariants(W1, R1) === invariants1)

R2 = QQ[x_1..x_4]
W2 = matrix{{0,1,-1,1},{1,0,-1,-1}}
invariants2 = set {x_1*x_2*x_3,x_1^2*x_3*x_4}
assert(set torusInvariants(W2,R2) === invariants2)

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

