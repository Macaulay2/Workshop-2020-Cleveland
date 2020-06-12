
document {
	Key => {finiteAbelianAction, (finiteAbelianAction, List, Matrix, PolynomialRing)},
	Headline => "Finite abelian group action via weights",
	Usage => "finiteAbelianAction(d, W, R)",
	Inputs => {
	    	"d" => List => {"of orders of factors in the decomposition of the group"},
	    	"W" => Matrix => {"of weights of the group action"},
		"R" => PolynomialRing => {"on which the group acts"}
		},
	Outputs => {
		FiniteAbelianAction => {"the (diagonal) action of the finite abelian group corresponding to the given weight matrix"}
		},
	"This function is provided by the package ", TO InvariantRings,". ",

    	PARA {	 
	    "Writing the finite abelian group as",
	    TEX /// $\mathbb{Z}/d_1 \oplus \cdots \oplus \mathbb{Z}/d_r$, ///,
	    "the list ", TT "d = {d_1,d_2,...,d_r},",  " contains the orders of the factors.",
	    " We assume that the group acts diagonally on the polynomial ring",
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
		},
    
	    }

document {
	Key => {FiniteAbelianAction},
	
	Headline => "the class of all diagonal actions by
	finite abelian groups",
	
	"This class is provided by the package ", TO InvariantRings,".",
	
	PARA {
	    	TT "FiniteAbelianAction", " is the class of all
		diagonal actions by finite abelian groups
		on polynomial rings for the
		purpose of computing invariants.
		It is created using ", TO "finiteAbelianAction", "."
	    },
	}
    
document {
	Key => {(numgens, FiniteAbelianAction)},
	Headline => "number of generators of a finite abelian group",
	Usage => "numgens A",
	Inputs => {
	    	"A" => FiniteAbelianAction =>
		{"the action of a finite abelian group"},
		},
	Outputs => {
		ZZ => {"the number of generators of the group"}
		},
	"This function is provided by the package ", TO InvariantRings,". ",

    	PARA {	 
	    "Writing the finite abelian group as",
	    TEX /// $\mathbb{Z}/d_1 \oplus \cdots \oplus \mathbb{Z}/d_r$, ///,
	    "this function returns ", TT "r", "."
	},
    
    	PARA {
	    "Here is an example of a product of two cyclic groups
	    of order 3 acting on a polynomial ring in 3 variables."
	},
	
	EXAMPLE {
	    "R = QQ[x_1..x_3]",
	    "d = {3,3}",
	    "W = matrix{{1,0,1},{0,1,1}}",
	    "A = finiteAbelianAction(d, W, R)",
	    "numgens A"
		},
	    }

document {
	Key => {torusAction, (torusAction, Matrix, PolynomialRing)},
	
	Headline => "the torus action from a weight matrix",
	
	Usage => "torusAction(W, R)",
	
	Inputs => {
	    	"W" => Matrix => {"of weights of a torus action"},
		"R" => PolynomialRing => {"on which the torus acts"}
		},
	    
	Outputs => {
		TorusAction => {"the (diagonal) torus action with the given weight matrix"}
		},
	    
	"This function is provided by the package ", TO InvariantRings,". ",

       	PARA {
	    "Use this function to set up an action of a torus",
	    TEX /// $(k^\times)^r$ ///,
	    " on a polynomial ring ",
	    TEX /// $R = k[x_1,\ldots,x_n]$.///,
	    " We assume that the action is diagonal, meaning that ",
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
	"The following example defines an action of a 
	two-dimensional torus on a four-dimensional vector space
	with a basis of weight vectors whose weights are
	the columns of the input matrix."
	},
        	
	EXAMPLE {
	    "R = QQ[x_1..x_4]",
	    "W = matrix{{0,1,-1,1},{1,0,-1,-1}}",
	    "T = torusAction(W, R)"
		},
	    }
	
document {
	Key => {TorusAction},
	
	Headline => "the class of all diagonal torus actions",
	
	"This class is provided by the package ", TO InvariantRings,".",
	
	PARA {
	    	TT "TorusAction", " is the class of all
		diagonal torus actions on polynomial rings for the
		purpose of computing invariants.
		It is created using ", TO "torusAction", "."
	    },
	}

document {
	Key => {weights},
	Headline => "of a diagonal action",
	Usage => "weights A\n
	weights T",
	Inputs => {
	    	"A" => FiniteAbelianAction =>
		{"the diagonal action of a finite abelian group"},
	    	"T" => TorusAction =>
		{"a diagonal torus action"},
		},
	Outputs => {
		Matrix => {"the weight matrix of the group action"}
		},
	"This function is provided by the package ", TO InvariantRings,". ",

}

document {
	Key => {(weights, FiniteAbelianAction)},
	Headline => "for the diagonal action of a finite abelian group",
	Usage => "weights A",
	Inputs => {
	    	"A" => FiniteAbelianAction =>
		{"the action of a finite abelian group"},
		},
	Outputs => {
		Matrix => {"the weight matrix of the group action"}
		},
	"This function is provided by the package ", TO InvariantRings,". ",

    	PARA {	 
	    "Writing the finite abelian group as",
	    TEX /// $\mathbb{Z}/d_1 \oplus \cdots \oplus \mathbb{Z}/d_r$, ///,
	    "the list ", TT "d = {d_1,d_2,...,d_r},",  " contains the orders of the factors.",
	    " We assume that the group acts diagonally on the polynomial ring",
	    TEX /// $R = k[x_1,\ldots,x_n]$, ///,
	    "which is to say that if we denote the evident generators of the group by",
	    TEX /// $g_1,\ldots,g_r$ ///,
	    "then we have",
	    TEX /// $$g_i \cdot x_j = \zeta_i^{w_{ij}} x_j$$ ///,
	    "for",
	    TEX /// $\zeta_i$ ///,
	    "a primitive",
	    TEX /// $d_i$///,
	    "-th root of unity. This function returns the weight
	    matrix",
	    TEX /// $(w_{ij})$ ///, "."  
	},
    
    	PARA {
	    "Here is an example of a product of two cyclic groups
	    of order 3 acting on a polynomial ring in 3 variables."
	},
	
	EXAMPLE {
	    "R = QQ[x_1..x_3]",
	    "d = {3,3}",
	    "W = matrix{{1,0,1},{0,1,1}}",
	    "A = finiteAbelianAction(d, W, R)",
	    "weights A"
		},
	    }

document {
	Key => {(weights, TorusAction)},
	Headline => "of a diagonal torus action",
	Usage => "weights T",
	Inputs => {
	    	"T" => TorusAction => {"a torus action"},
		},
	Outputs => {
		Matrix => {"the weight matrix of the torus action"}
		},
	"This function is provided by the package ", TO InvariantRings,". ",
    	PARA {
	    "Use this function to recover the weight matrix of a
	    diagonal torus action on a polynomial ring.
	    The variables of the ring are weight vectors with
	    weights corresponding in order to the columns of the
	    weight matrix."
	    },
	
    	PARA {
	"The following example defines an action of a 
	two-dimensional torus on a polynomial ring in four
	variables."
	},
        	
	EXAMPLE {
	    "R = QQ[x_1..x_4]",
	    "W = matrix{{0,1,-1,1},{1,0,-1,-1}}",
	    "T = torusAction(W, R)",
	    "weights T"
		},
	    }
