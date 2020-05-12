-- -*- coding: utf-8 -*-
newPackage(
	"SwitchingFields",
    	Version => "0.1", 
    	Date => "May 11, 2020",
    	Authors => {
	     {Name => "Zhan Jiang", Email => "zoeng@umich.edu"}
	     },
    	HomePage => "http://www-personal.umich.edu/~zoeng/",
    	Headline => "an example Macaulay2 package",
	AuxiliaryFiles => false -- set to true if package comes with auxiliary files
    	)

-- Any symbols or functions that the user is to have access to
-- must be placed in one of the following two lists
export {"fieldExtension", "secondFunction", "MyOption"}
exportMutable {}

fieldExtension = method(Options => {})
fieldExtension(Ring, Ring, List) := o -> (S1, R1, l1) -> (
    K1 := coefficientRing R1;
    L1 := coefficientRing S1;
    f1 := map(L1, K1);
    return map(S1, R1, append(l1, f1(K1_0)))
)

--this function should change the coefficient ring of R1 to K1 
fieldExtension(PolynomialRing, Ring) := opts -> (R1, K1) -> (
	if (not isField(K1)) then error "fieldExtension:  Expected the second argument to be a field."; --maybe we don't want this.
	M1 := monoid R1;
	return (K1(M1));
);
   
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
	Key => SwitchingFields,
	Headline => "an example Macaulay2 package",
	EM "SwitchingFields", " is an example package which can
	be used as a template for user packages."
	}

document {
	Key => fieldExtension,
	Headline => "prototype",
	"This function is provided by the package ", TO SwitchingFields, "."
	}
document {
	Key => (fieldExtension, Ring, Ring, List),
	Headline => "prototype2",
	Usage => "fieldExtension(S, R, l)",
	Inputs => {
	     "S" => {"Ring"},
	     "R" => {"Ring"},
	     "l" => {"List"}
	     },
	Outputs => {
	     {"Ring Map"}
	},
	EXAMPLE {
	    "fieldExtension(GF(64)[y], GF(8)[x], {y})"
		}
	}


document {
	Key => secondFunction,
	Headline => "a silly second function",
	"This function is provided by the package ", TO SwitchingFields, "."
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
     "This symbol is provided by the package ", TO SwitchingFields, "."
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
f := fieldExtension(GF(64)[y], GF(8)[x], {y})
  assert(secondFunction(1,3) === 4)
  assert(secondFunction(1,3,MyOption=>5) === 9)
///
  
       
end

-- Here place M2 code that you find useful while developing this
-- package.  None of it will be executed when the file is loaded,
-- because loading stops when the symbol "end" is encountered.

installPackage "SwitchingFields"
installPackage("SwitchingFields", RemakeAllDocumentation=>true)
check SwitchingFields

-- Local Variables:
-- compile-command: "make -C $M2BUILDDIR/Macaulay2/packages PACKAGES=SwitchingFields pre-install"
-- End: