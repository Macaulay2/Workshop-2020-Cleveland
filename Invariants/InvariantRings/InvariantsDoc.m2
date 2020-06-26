    
document {
	Key => {action, (action, RingOfInvariants)},
	
	Headline => "the group action that produced a ring of invariants",
	
	Usage => "action S",
	
	Inputs => {
	    	"S" => RingOfInvariants => {"of the group action being returned"},
		},
	
	Outputs => {
		GroupAction => {"the action that produced the ring of invariants in the input"}
		},
	"This function is provided by the package ", TO InvariantRings,".",
	
	PARA {
	    "This example shows how to recover the action of a
	    torus that produced a certain ring of invariants.
	    Note other action types are possible and may produce
	    a different looking output."
	    },
    	
	EXAMPLE {
		"R = QQ[x_1..x_4]",
		"T = torusAction(matrix {{0,1,-1,1},{1,0,-1,-1}}, R)",
		"S = R^T",
		"action S"
		},
	    }

document {
	Key => (generators, RingOfInvariants),
	
	Headline => "the generators for a ring of invariants",
	
	Usage => "generators S, gens S",
	
	Inputs => {
	    	"S" => RingOfInvariants,
		},
	    
	Outputs => {
		List => {"of algebra generators for the ring of invariants"}
		},
	    
	"This function is provided by the package ", TO InvariantRings,". ",
	
	PARA {
	    "This method gets the algebra generators for a ring of invariants."
	    },
    	
	EXAMPLE {
		"R = QQ[x_1..x_4]",
		"W = matrix{{0,1,-1,1},{1,0,-1,-1}}",
		"T = torusAction(W, R)",
		"S = R^T",
		"gens S",
		},
	    }

document {
	Key => {invariantRing, 
	    (invariantRing, GroupAction),
	    (symbol ^, PolynomialRing, GroupAction)},
	
	Headline => "the ring of invariants of a group action",
	
	Usage => "invariantRing G, R^G",
	Inputs => {
	    	"G" => GroupAction,
	    	"R" => PolynomialRing => {"on which the group acts"},
		},
	Outputs => {
		RingOfInvariants => {"the ring of invariants of the given group action"}
		},
	    
	"This function is provided by the package ", TO InvariantRings,". ",
	
	PARA {
	    "The following example defines an action of a 
	    two-dimensional torus on a four-dimensional vector space
	    with a basis of weight vectors whose weights are
	    the columns of the input matrix."
	},
    	
	EXAMPLE {
		"R = QQ[x_1..x_4]",
		"W = matrix{{0,1,-1,1},{1,0,-1,-1}}",
		"T = torusAction(W, R)",
		"S = invariantRing T",
		},
	    
	PARA {
	    "The algebra generators for the ring of invariants are computed upon
	    initialization by the method ",
	    TO invariants,"."
	    },

	PARA {
	    "Alternatively, we can use the following shortcut to construct
	    a ring of invariants."
	    },
    	
	EXAMPLE {
		"S = R^T",
		},
	    }

document {
	Key => {
	    invariants, 
	    (invariants, TorusAction),
	    (invariants, FiniteAbelianAction)
	    },
	
	Headline => "compute the generating invariants of a group action",
	
	Usage => "invariants T \n invariants A",
	
	Inputs => {  
	    	"T" => TorusAction => {"a diagonal action of a torus on a polynomial ring"},
		"A" => FiniteAbelianAction => {"a diagonal action of a finite abelian group on a polynomial ring"}
		},
	Outputs => {
		"L" => List => {"a minimal set of generating invariants for the group action"}
		},

	PARA {
	    "This function is provided by the package ", TO InvariantRings, ". It implements algorithms to compute minimal sets 
	    of generating invariants for diagonal actions of tori and finite abelian groups.  The algorithm for tori due to 
	    Derksen and Kemper can be found in:"
	    },
       
       UL { 
	    {"Derksen, H. & Kemper, G. (2015).", EM "Computational Invariant Theory", 
	   ". Heidelberg: Springer. pp 159-164"}
        },
    
       PARA {
	    "The algorithm for tori computes a minimal set of generating monomial invariants for an action of a torus",
	    TEX /// $(k^\times)^r$ ///,
	    " on a polynomial ring ",
	    TEX /// $R = k[x_1,\ldots,x_n]$.///,
	    " We assume that the torus action is diagonal, in the sense that ",
	    TEX /// $(t_1,\ldots,t_r) \in (k^\times)^r$ ///,
	    " acts by",
	    TEX /// $$(t_1,\ldots,t_r) \cdot x_j = t_1^{w_{1j}}\cdots t_r^{w_{rj}} x_j$$ ///,
	    "for some integers ",
	    TEX /// $w_{ij}$. ///,
	    "These are the entries of the input matrix ", TT "W",
	    " for the torus action. In other words, the j-th column of ", TT "W", " is the weight vector of",
	    TEX /// $x_j$. ///
	},
    
    	PARA {
	    "Here is an example of a one-dimensional torus acting on a two-dimensional vector space:"
	},
    
    	EXAMPLE {
	    	"R = QQ[x_1,x_2]",
		"W = matrix{{1,-1}}",
		"T = torusAction(W, R)",
		"invariants T"
		},
	   
	PARA {
	    "The algorithm for finite abelian groups due to Gandini is based on the Derksen-Kemper algorithm for tori,
	     with some adjustments and optimizations for the finite group case.  A description of this algorithm can be found in: "
	     },
	 
        UL { 
	    {"Gandini, F. ", EM "Ideals of Subspace Arrangements", 
	   ". Thesis (Ph.D.)-University of Michigan. 2019. ISBN: 978-1392-76291-2. pp 29-34."}
        },
    
    	PARA {	 
	     "Writing the finite abelian group as",
	    TEX /// $\mathbb{Z}/d_1 \oplus \cdots \oplus \mathbb{Z}/d_r$, ///,
	    "the input ", TT "A", " is a finite abelian action which consists of ", TT "d", " the list ", TT "{d_1,d_2,...,d_r}, ", 
	    TT "W", " a weight matrix, and ",  TT "R"," a polynomial ring. We assume that the group acts diagonally on the polynomial ring",
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
	    "comprise the weight matrix ", TT "W", "."  
	},
    
    	PARA {
	    "Here is an example of a product of two cyclic groups of order 3 acting on a three-dimensional vector space:"
	},
	
	EXAMPLE {
	    "R = QQ[x_1..x_3]",
	    "d = {3,3}",
	    "W = matrix{{1,0,1},{0,1,1}}",
	    "A = finiteAbelianAction(d, W, R)",
	    "invariants A"
		},
    
    	SeeAlso => {invariantRing, torusAction, finiteAbelianAction, isInvariant},	
	}

document {
	Key => {
	    (invariants, LinearlyReductiveAction, ZZ)
	    },
	
	Headline => "basis for graded component of invariant ring",
	
	Usage => "invariants(V,d)",
	
	Inputs => {  
	    	"V" => LinearlyReductiveAction,
		"d" => ZZ => {"a degree"},
		},
	Outputs => {
		"L" => List => {"an additive basis of invariants in degree ", TT "d"}
		},

	PARA {
	    "This function is provided by the package ", TO InvariantRings,
	    },
	PARA {
	    "When called on a linearly reductive group action and
	    a degree, it computes an additive basis for the
	    invariants of the action in the given degree. This is
	    an implementation of Algorithm 4.5.1 in:"
	    },
       
       UL { 
	    {"Derksen, H. & Kemper, G. (2015).", EM "Computational Invariant Theory", 
	   ". Heidelberg: Springer."}
        },
    	PARA {
	    "The following example examines the action of the
	    special linear group of degree 2 on the space of
	    binary quadrics. There is a single invariant of degree
	    2 but no invariant of degree 3."
	    },
    	EXAMPLE {
	    	"S = QQ[a,b,c,d]",
		"I = ideal(a*d - b*c - 1)",
		"A = S[u,v]",
		"M = (map(S,A)) last coefficients sub(basis(2,A),{u=>a*u+c*v,v=>b*u+d*v})",
		"R = QQ[x_1..x_3]",
		"V = linearlyReductiveAction(I,M,R)",
		"invariants(V,2)",
		"invariants(V,3)",
		},
	   
    	SeeAlso => {invariantRing, linearlyReductiveAction, isInvariant},
	}

document {
	Key => {
	    (invariants, LinearlyReductiveAction)
	    },
	
	Headline => "invariant generators of Hilbert ideal",
	
	Usage => "invariants V",
	
	Inputs => {  
	    	"V" => LinearlyReductiveAction,
		},
	Outputs => {
		"L" => List => {"of invariants generating the Hilbert ideal"}
		},

	PARA {
	    "This function is provided by the package ", TO InvariantRings,
	    },
	PARA {
	    "When called on a linearly reductive group action and
	    a degree, this function returns a list of generators for the
	    Hilbert ideal that are also invariant under the action.
	    This function computes the Hilbert ideal first using ",
	    TO "hilbertIdeal", " then finds invariant generators
	    degree by degree using ",
	    TO "invariants(LinearlyReductiveAction,ZZ)", ".",
	    },
    	PARA {
	    "The next example constructs a cyclic group of order 2
	    as a set of two affine points. Then it introduces an
	    action of this group on a polynomial ring in two variables
	    and computes the Hilbert ideal. The action permutes the
	    variables of the polynomial ring."
	    },
    	EXAMPLE {
		"S = QQ[z]",
		"I = ideal(z^2 - 1)",
		"M = matrix{{(z+1)/2, (1-z)/2},{(1-z)/2, (z+1)/2}}",
		"sub(M,z=>1),sub(M,z=>-1)",
		"R = QQ[x,y]",
		"V = linearlyReductiveAction(I, M, R)",
		"H = hilbertIdeal V",
		"invariants V",
		},
	Caveat => {
	    "Both ", TO "hilbertIdeal", " and ",
	    TO "invariants(LinearlyReductiveAction,ZZ)",
	    " require Groebner bases computations, which could
	    lead to long running times. The computations for ",
	    TO "hilbertIdeal", " are typically the bottleneck.",
	    },
    	SeeAlso => {hilbertIdeal, invariants},
	}

document {
	Key => {isInvariant, 
	    (isInvariant, RingElement, FiniteGroupAction),
	    (isInvariant, RingElement, TorusAction),
	    (isInvariant, RingElement, FiniteAbelianAction),
	    },
	
	Headline => "check whether a polynomial is invariant under a group action",
	
	Usage => "isInvariant(f, G), isInvariant(f, T), isInvariant(f, A)",
	
	Inputs => {
	    	"f" => RingElement => {"a polynomial in the polynomial ring on which the group acts"},
	    	"G" => FiniteGroupAction,
		"T" => TorusAction,
		"A" => FiniteAbelianAction
		},
	    
	Outputs => {
		Boolean => "whether the given polynomial is invariant under the given group action"
		},
	    
	"This function is provided by the package ", TO InvariantRings,". ",
    	
	PARA {
	    "This function checks if a polynomial is invariant
	    under a certain group action."
	    },
	
	PARA {
	    "The following example defines the permutation action
	    of a symmetric group on a polynomial ring with three
	    variables."
	    },
	
	EXAMPLE {
	    "R = QQ[x_1..x_3]",
	    "L = apply(2, i -> permutationMatrix(3, [i + 1, i + 2] ) )",
	    "S3 = finiteAction(L, R)",
	    "isInvariant(1 + x_1^2 + x_2^2 + x_3^2, S3)",
	    "isInvariant(x_1*x_2*x_3^2, S3)"
		},
    
    	PARA {
	    "Here is an example with a two-dimensional torus
	    acting on polynomial ring in four variables:"
	    },
	
	EXAMPLE {
	    "R = QQ[x_1..x_4]",
	    "W = matrix{{0,1,-1,1},{1,0,-1,-1}}",
	    "T = torusAction(W, R)",
	    "isInvariant(x_1*x_2*x_3, T)",
	    "isInvariant(x_1*x_2*x_4, T)"
		},
	    
         PARA {
	    "Here is another example of a product of two cyclic groups
	    of order 3 acting on a three-dimensional vector space:"
	    },
	
	EXAMPLE {
	    "R = QQ[x_1..x_3]",
	    "d = {3,3}",
	    "W = matrix{{1,0,1},{0,1,1}}",
	    "A = finiteAbelianAction(d, W, R)",
	    "isInvariant(x_1*x_2*x_3, A)",
	    "isInvariant((x_1*x_2*x_3)^3, A)"
		},
	    }	

document {
	Key => {reynoldsOperator, (reynoldsOperator, RingElement, FiniteGroupAction)},
	
	Headline => "the image of a polynomial under the Reynolds operator",
	
	Usage => "reynoldsOperator(f, G)",
	
	Inputs => {
	    	"G" => FiniteGroupAction,
		"f" => RingElement => {"a polynomial in the polynomial ring of the given group action"}
		},
	    
	Outputs => {
		RingElement => {"the invariant polynomial which is the image of the given 
		    polynomial under the Reynolds operator of the given finite group action"}
		},
	    
	"This function is provided by the package ", TO InvariantRings,". ",
	
	PARA {
	    "The following example computes the image of a polynomial under the
	    Reynolds operator for a cyclic permutation of the variables."
	    },
    	
	EXAMPLE {
	    "R = ZZ/3[x_0..x_6]",
	    "P = permutationMatrix toString 2345671",
	    "C7 = finiteAction(P, R)",
	    "reynoldsOperator(x_0*x_1*x_2^2, C7)",
		},
	    }


