-------------------------------------------------------------------------------
-- Examples for the ToricMaps package (to be merged in NormalToricVarieties) --
-------------------------------------------------------------------------------
restart
needsPackage "ToricMaps"
-- Define P^2 and P^2xP^2
PP2 = toricProjectiveSpace 2;
X = PP2 ** PP2;
n = dim PP2
S = ring PP2
R = ring X

-- Defining the projection into the first factor
f = map(PP2, X, id_(ZZ^2) | (0 * id_(ZZ^2)))
assert isWellDefined f

-- Ideal of the image of f
assert(ideal f == 0)

-- Checking some properties
assert(isProper f)
assert(isSurjective f)

-- Pullback of a divisor on P^2
D = toricDivisor({1,-2,3}, PP2)
pullback(f, D)

-- Pullback commutes with OO
assert(pullback(f, OO D) === OO pullback(f, D))


-- Pullback of a coherent sheaf
pullback(f, cotangentSheaf PP2)

-- The diagonal map P2 -> P2xP2
g = map(X, PP2, id_(ZZ^n) || id_(ZZ^n))
assert isWellDefined g

-- Maps compose to identity on P^2
assert (f * g === id_PP2)

-- Ideal of the diagonal
I = ideal g
assert isHomogeneous I
assert(codim I == dim PP2)

-- resolution of the diagonal
res I

--------------------------------------------------------------------------
-- Examples for the Chow package (to be merged in NormalToricVarieties) --
--------------------------------------------------------------------------
restart
needsPackage "Chow"

