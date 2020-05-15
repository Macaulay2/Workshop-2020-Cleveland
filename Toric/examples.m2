-------------------------------------------------------------------------------
-- Examples for the ToricMaps package (to be merged in NormalToricVarieties) --
-------------------------------------------------------------------------------
installPackage "ToricMaps"
installPackage "Chow"

restart
viewHelp "ToricMaps"
needsPackage "ToricMaps"
-- Define P^2 and P^2xP^2
PP2 = toricProjectiveSpace 2;
X = PP2 ** PP2;
n = dim PP2

-- Defining the projection into the first factor
f = map(PP2, X, id_(ZZ^2) | (0 * id_(ZZ^2)))
assert isWellDefined f

-- Checking some properties
assert isProper f
assert isSurjective f

-- Pullback of a divisor on P^2
D = toricDivisor({1,-2,3}, PP2)
pullback(f, D)

-- Pullback commutes with OO
assert(pullback(f, OO D) === OO pullback(f, D))

-- Pullback of a coherent sheaf
pullback(f, cotangentSheaf PP2)

-- Ideal of the image of f
assert(ideal f == 0)

-- Computing the induced map on the Cox rings
S = ring PP2; R = ring X; -- just so the map is pretty
inducedMap f

-- The diagonal map P2 -> P2xP2
g = map(X, PP2, id_(ZZ^n) || id_(ZZ^n))
assert isWellDefined g

-- Maps compose to identity on P^2
assert(f * g === id_PP2)

-- Ideal of the diagonal
I = ideal g
assert isHomogeneous I
assert(codim I == dim PP2)

-- Resolution of the diagonal
res I

--------------------------------------------------------------------------
-- Examples for the Chow package (to be merged in NormalToricVarieties) --
--------------------------------------------------------------------------
restart
viewHelp "Chow"
needsPackage "Chow"

X = toricProjectiveSpace 4;
rays X
max X
--Create a cycle on P^4
Z1 = toricCycle({({0,1},3), ({0,2},5) },X)
Z2 = 3*X_{0,1}+5*X_{0,2}
Z1==Z2

--Intersect with a divisor

D= X_0;
D*Z1



--See that the exceptional divisor on Bl_p(P^2) has self-intersection -1
Y=toricBlowup({0,1},toricProjectiveSpace 2);
rays Y
Y_0*Y_0
Y_3*Y_{3}

