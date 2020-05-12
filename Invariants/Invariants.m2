-- -*- coding: utf-8 -*-
newPackage(
	"Invariants",
    	Version => "1.0", 
    	Date => "May 12, 2020",
    	Authors => {
	     {Name => "Luigi Ferraro", Email => "ferrarl@wfu.edu",
	      HomePage => "http://users.wfu.edu/ferrarl/"}
	     },
	     {Name => "Federico Galetto", Email => "f.galetto@csuohio.edu", HomePage => "https://math.galetto.org"},
	     {Name => "Xianglong Ni", Email => "xlni@berkeley.edu", HomePage => "https://math.berkeley.edu/~xlni/"}
	     },
    	Headline => "Computing Invariants for Tori and Abelian Groups",
	DebuggingMode => true,
	AuxiliaryFiles => false -- set to true if package comes with auxiliary files
    	)

-- Any symbols or functions that the user is to have access to
-- must be placed in one of the following two lists
export {"firstFunction", "secondFunction", "MyOption"}
exportMutable {}

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
	Headline => "an example Macaulay2 package",
	EM "Invariants", " is an example package which can
	be used as a template for user packages."
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

