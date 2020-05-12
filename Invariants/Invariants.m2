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
export {"primaryInvariants", "firstFunction", "secondFunction", "MyOption"}
exportMutable {}

needsPackage("Polyhedra", Reload => true)

primaryInvariants = method()
primaryInvariants (Matrix, PolynomialRing) := List => (W, R) -> (
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
    while  #nonemptyU > 0 do(
	v = first nonemptyU;
	m = first (U#v);
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

beginDocumentation()
document { 
	Key => Invariants,
	Headline => "Computing Invariants for Tori and Abelian Groups",
	EM "Invariants", " is an example package which can
	be used as a template for user packages."
	}
document {
	Key => {primaryInvariants, (primaryInvariants,Matrix,PolynomialRing)},
	Headline => "Computes the primary invariants for a diagonal torus action given by column weight vectors",
	Usage => "primaryInvariants(W,R)",
	Inputs => {
	    	"R" => PolynomialRing => {"on which a torus acts"},
		"W" => Matrix => {"whose ith column is the weight vector of ", TT "R_i"}
		},
	Outputs => {
		List => {"A minimal set of generating invariants for the torus action"}
		},
	"This function is provided by the package ", TO Invariants, ".",
	EXAMPLE {
		"primaryInvariants(matrix{{1,-1}}, QQ[x_1,x_2])"
		}
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
	"This function is provided by the package ", TO Invariants, ".",
	EXAMPLE {
		"firstFunction 1",
		"firstFunction 0"
		}
	}
document {
	Key => secondFunction,
	Headline => "a silly second function",
	"This function is provided by the package ", TO Invariants, "."
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
     "This symbol is provided by the package ", TO Invariants, "."
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

TEST ///

R1 = QQ[x_1..x_4]
W1 = matrix {{-3, -1, 1, 2}}
invariants1 =  set {x_2*x_3, x_2^2*x_4, x_1*x_3*x_4, x_1*x_2*x_4^2, x_1^2*x_4^3, x_1*x_3^3}
assert(set primaryInvariants(W1, R1) === invariants1)

R2 = QQ[x_1..x_4]
W2 = matrix{{0,1,-1,1},{1,0,-1,-1}}
invariants2 = set {x_1*x_2*x_3,x_1^2*x_3*x_4}
assert(set primaryInvariants(W2,R2) === invariants2)

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

