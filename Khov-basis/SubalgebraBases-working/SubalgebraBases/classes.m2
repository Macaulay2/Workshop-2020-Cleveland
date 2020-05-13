needsPackage "SubalgebraBases"

Subalgebra = new Type of HashTable
subalgebra = method()
subalgebra Matrix := M -> (
    R := ring M;
    new Subalgebra from {
    	"AmbientAlgebra" => R,
    	"Generators" => M,
--    	"Valuation" => valuation R,
	cache => new CacheTable from {
	    "PartialSubalgebraBasis" => M,
	    "InitialAlgebraGenerated" => null
	    }
	}
    )
--note: gens is already a MethodFunctionWithOptions
gens Subalgebra := o -> A -> A#"Generators"

subalgebraBasis Subalgebra := o -> A -> (
    newgens := subalgebraBasis(gens A, o);
    (A.cache)#"PartialSubalgebraBasis" = newgens;
    newgens
    )


end--
restart
load "classes.m2"
R=QQ[x,y]
A = subalgebra matrix{{x+y,x*y,x*y^2}}
gens A
subalgebraBasis A -- returns up to whatever limit
