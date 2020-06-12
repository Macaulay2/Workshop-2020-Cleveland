
document { 
	Key => InvariantRings,
	Headline => "invariants of group actions",
	EM "InvariantRing", " is a package implementing algorithms
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
    
document {
	Key => {(dim, GroupAction)},
	
	Headline => "dimension of the polynomial ring being acted upon",
	
	Usage => "dim G",
	
	Inputs => {
	    	"G" => GroupAction => {"a group action on a polynomial ring"},
		},
	
	Outputs => {
		ZZ => {"the dimension of the polynomial ring being acted upon"}
		},
	
	PARA {"This function is provided by the package ", 
	    TO InvariantRings,"."},
	
	EXAMPLE {
		"R = QQ[x_1..x_4]",
		"T = torusAction(matrix {{0,1,-1,1},{1,0,-1,-1}}, R)",
		"dim T == dim R"
		},
	    }

document {
	Key => {GroupAction},
	
	Headline => "the class of all group actions",
	
	"This class is provided by the package ", TO InvariantRings,".",
	
	PARA {
	    	TT "GroupAction", " is the class of all group actions
		on polynomial rings for the purpose of computing
		invariants. This is not typically used directly,
		delegating creation to the various constructor
		functions for different kinds of group actions:"
	    },
	UL {
	    {TO "FiniteGroupAction", ", the class of 
	    a finite matrix group action, is created with ",
	    TO "finiteAction"},
	    {TO "FiniteAbelianAction", ", the class of the diagonal
	    action of a finite abelian group, is created with ",
	    TO "finiteAbelianAction"},
	    {TO "TorusAction", ", the class of a diagonal
	    torus action, is created with ",
	    TO "torusAction"},
	    {TO "LinearlyReductiveAction", ", the class of a
	    linearly reductive matrix group action,
	    is created with ",
	    TO "linearlyReductiveAction"}
	    },
	
	PARA {
	    "Each class implements different algorithms to
	    compute invariants. Although mathematically speaking
	    all the above group actions are linearly reductive
	    (at least in the non modular case), the class ",
	    TO "LinearlyReductiveAction", " should be used only
	    when none of the other classes apply because it has fewer
	    and possibly less efficient methods."
	    },
	
	PARA {
	    	"The class ", TT "GroupAction ", "is implemented as
		a ", TT "HashTable", ". When created it stores
		information such as the action (in a format
		dependent upon the group) and the polynomial ring
	    	being acted upon."
	    },
	}

document {
	Key => {(ring, GroupAction)},
	
	Headline => "the polynomial ring being acted upon",
	
	Usage => "ring G",
	
	Inputs => {
	    	"G" => GroupAction => {"a group action on a polynomial ring"},
		},
	
	Outputs => {
		Ring => {"the polynomial ring being acted upon"}
		},
	
	PARA {"This function is provided by the package ",
	    TO InvariantRings,"."},
	
	EXAMPLE {
		"R = QQ[x_1..x_4]",
		"T = torusAction(matrix {{0,1,-1,1},{1,0,-1,-1}}, R)",
		"ring(T) === R"
		},
	    }



