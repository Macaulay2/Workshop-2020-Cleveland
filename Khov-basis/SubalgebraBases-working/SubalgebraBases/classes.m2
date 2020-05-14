-- new classes and methods which operate on them
load "methods.m2"

Valuation = new Type of HashTable
-- what should a valuation need to know?
source Valuation := v -> v#source
target Valuation := v -> v#target

MonomialValuation = new Type of Valuation
monomialValuation = method()
monomialValuation Ring := R -> new MonomialValuation from {
    source => R,
    target => ZZ^(numgens R),
    "evaluate" => (f -> matrix exponents leadTerm f)
    }
leadTerm (MonomialValuation, RingElement) := (v, f) -> (
    assert(ring f === source v);
    leadTerm f
    )
MonomialValuation RingElement := (v, f) -> matrix exponents leadTerm(v, f)

R=QQ[x,y]
f = x+y^2
v = monomialValuation R
source v
target v
v f
leadTerm(v,f) < y


Subring = new Type of HashTable
subring = method()
subring Matrix := M -> (
    R := ring M;
    new Subring from {
    	"AmbientRing" => R,
    	"Generators" => M,
	cache => new CacheTable from {}
	}
    )
subring List := L -> subring matrix{L}

gens Subring := o -> A -> A#"Generators"
numgens Subring := A -> numcols gens A
ambient Subring := A -> A#"AmbientRing"
isAlgebra := A -> instance(coefficientRing ambient A, Field)

presentation (Matrix, Subring) := (G, A) -> (
    if not A.cache.?presentation then (
    	B := ambient A;
    	k := coefficientRing B;
	(nB, nA) := (numgens B, numgens A);
	-- introduce nA "tag variables" w/ monomial order that eliminates non-tag variables
    	Cmonoid := monoid [Variables => nB + nA,
	                   MonomialOrder => (options B).MonomialOrder];
    	C := k Cmonoid;
	B2C := map(C,B,(vars C)_{0..nB-1});
    	I := ideal(B2C G - (vars C)_{nB..numgens C-1});
    	A.cache.presentation = selectInSubring(1, gens gb I);
	);
    A.cache.presentation
    )
ring Subring := A -> (
    I := ideal presentation A;
    R := ring I;
    R/I
    )

-- needs to be implemented
RingElement % Subring := (f, A) -> f
member (RingElement, Subring) := (f, A) -> (
    r := f%A;
    R := ambient A;
    r == 0_R
    )

options Subring := A -> A.cache#"Options"

subalgebraBasis Subring := o -> A -> (
    -- return value
    ret := if (A.cache#?"Options" and o.Limit == A.cache#"Options".Limit) then 
           A.cache#"PartialSubalgebraBasis" 
    else (
	-- recompute
	(newgens, isDone) := subalgebraBasis(gens A, o);
	-- update cache
	A.cache#"PartialSubalgebraBasis" = newgens;
	A.cache#"InitialAlgebraGenerated" = isDone;
	newgens
	);
    A.cache#"Options" = o;
    ret
    )


end--
restart
load "classes.m2"
R=QQ[x,y]
A = subring matrix{{x+y,x*y,x*y^2}}
gens A -- gets the use-specified generators 
subalgebraBasis(A, Limit=>10)
options A
presentation(gens A, A)
