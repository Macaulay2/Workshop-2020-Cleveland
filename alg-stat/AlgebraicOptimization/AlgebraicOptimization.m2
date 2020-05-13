newPackage(
  "AlgebraicOptimization",
  Version => "0.1", 
  Date => "May 12, 2020",
  Authors => {
    {Name => "Marc Harkonen", 
    Email => "harkonen@gatech.edu", 
    HomePage => "https://people.math.gatech.edu/~mharkonen3/"},
    {Name => "Your name here",
    Email => "Your email here",
    HomePage => "Your page here"}
  },
  Headline => "A package for algebraic optimization",
  DebuggingMode => true,
  PackageImports => {"Elimination"}
)

export {
  -- Methods
  "projectiveDual",
  "conormalRing",
  "conormalVariety",
  "multiDegreeEDDegree",
  -- Options
  "DualVariable",
  --Types and keys
  "ConormalRing","CNRing","PrimalRing","DualRing","PrimalCoordinates","DualCoordinates"
}

ConormalRing = new Type of HashTable;

conormalRing = method(Options => {DualVariable => null});
-- Creates a ConormalRing from a primal ring R
conormalRing Ring := ConormalRing => opts -> R -> (
  if not degreeLength R == 1 then error "expected degree length 1";
  u := if opts.DualVariable === null then symbol u else opts.DualVariable;
  dualR := (coefficientRing R)[u_0..u_(#gens R - 1)];
  new ConormalRing from {
    CNRing => R ** dualR,
    PrimalRing => R,
    DualRing => dualR,
    PrimalCoordinates => gens R,
    DualCoordinates => gens dualR
  }
)


conormalVariety = method(Options => options conormalRing);
-- Computes the conormal variety
conormalVariety (Ideal, ConormalRing) := Ideal => opts -> (I,C) -> (
  if not ring I === C.PrimalRing then error "expected ideal in primal ring";
  
  c := codim I;
  jacI := sub(diff(matrix{C.PrimalCoordinates}, transpose gens I), C.CNRing);
  jacBar := sub(matrix{C.DualCoordinates}, C.CNRing) || jacI;
  J' := sub(I,C.CNRing) + minors(c+1, jacBar);
  J := saturate(J', minors(c, jacI));
  J
)
TEST ///

///


projectiveDual = method(Options => options conormalRing);
-- (Alg. 5.1 in SIAM book)
-- Takes homogeneous ideal as input, returns ideal of dual of the projective variety
projectiveDual Ideal := Ideal => opts -> I -> (
  if not isHomogeneous I then error("Ideal has to be homogeneous");
  R := ring I;
  S := conormalRing(R, opts);

  primalCoordinates := S.PrimalCoordinates / (i->sub(i,S.CNRing));
  dualCoordinates := S.DualCoordinates / (i->sub(i,S.CNRing));

  J := conormalVariety(I, S);

  sub(eliminate(primalCoordinates, J), S.DualRing)
)

TEST ///
S = QQ[x_0..x_2]
I = ideal(x_2^2-x_0^2+x_1^2)
dualI = projectiveDual(I)
S = ring dualI
assert( dualI == ideal(S_0^2 - S_1^2 - S_2^2)) 
///


multiDegreeEDDegree = method();
multiDegreeEDDegree Ideal := ZZ => I -> (
  S := conormalRing ring I;
  N := conormalVariety(I,S);
  (mon,coef) := coefficients multidegree N;
  sub(sum flatten entries coef, ZZ)
)

TEST ///
R = QQ[x_0..x_3]
J = ideal det(matrix{{x_0, x_1, x_2}, {x_1, x_0, x_3}, {x_2, x_3, x_0}})
assert(multiDegreeEDDegree(J) == 13)
///







-- Documentation below

beginDocumentation()

-- template for package documentation
doc ///
Key
  AlgebraicOptimization
Headline
  Package for algebraic optimization
Description
  Text
    Todo
  Example
    todo
Caveat
SeeAlso
///

doc ///
Key
  ConormalRing
///


-- template for function documentation
doc ///
Key
  projectiveDual
  (projectiveDual, Ideal)
  [projectiveDual, DualVariable]
Headline
  Compute projective dual
Usage
  projectiveDual(I)
Inputs
  I:
    a homogeneous @TO2{Ideal, "ideal"}@
Outputs
  :Ideal
    the projective dual of {\tt I}
--Consequences
--  asd
Description
  Text
    Compute the projective dual of a homogeneous ideal.
    For example, the snippet below shows that the dual of a circle is a circle.

  Example
    S = QQ[x_0..x_2]
    I = ideal(x_2^2-x_0^2+x_1^2)
    projectiveDual(I)

  Text
    The option {\tt DualVariable} specifies the basename for the dual variables
  Example
    projectiveDual(I,DualVariable => y)
--  Code
--    todo
--  Pre
--    todo
--Caveat
--  todo
--SeeAlso
--  todo
///

doc ///
Key
  conormalRing
  [conormalRing, DualVariable]
Headline
  Creates a ring with primal and dual variables
Usage
  conormalRing(R)
Inputs
  R:Ring
Outputs
  :ConormalRing
Description
  Text
    Creates an element of type ConormalRing
  Example
    R = QQ[x_0..x_2]
    conormalRing(R)
    conormalRing(R, DualVariable => l)
Caveat
  The ring $R$ must have degree length 1
SeeAlso
  conormalVariety
///

doc ///
Key
  conormalVariety
  (conormalVariety, Ideal, ConormalRing)
--Headline
--  todo
Inputs
  I:Ideal
    defined in the primal variables only
  S:ConormalRing
Usage
  conormalVariety(I,S)

Caveat
  The ring containing $I$ and $p$ must have primal variables in degree $\{1,0\}$ and dual variables in degree $\{0,1\}$.
  Such a ring can be obtained using @TO{conormalRing}@.
///

doc ///
Key
  multiDegreeEDDegree
  (multiDegreeEDDegree, Ideal)
Inputs
  I:Ideal
Outputs
  :ZZ
    the ED-degree of $I$
Usage
  multiDegreeEDDegree(I)
Description
  Text
    Computes the ED degree symbolically by taking the sum of multidegrees of the conormal ideal. 
    See theorem 5.4 in Draisma et. al. The Euclidean Distance Degree of an Algebraic Variety https://arxiv.org/abs/1309.0049 

    As an example, we see that the ED-degree of Caylay's cubic surface is 13
  Example
    R = QQ[x_0..x_3]
    J = ideal det(matrix{{x_0, x_1, x_2}, {x_1, x_0, x_3}, {x_2, x_3, x_0}})
    multiDegreeEDDegree(J)

Caveat
  The conormal variety cannot intersect the diagonal $\Delta(\mathbb{P}^{n-1}) \subset \mathbb{P}^{n-1} \times \mathbb{P}^{n-1}$.
  At the moment this is not checked.
///

TEST ///
  -- test code and assertions here
  -- may have as many TEST sections as needed
///

  
end


--Example
path={"/Users/jo/Documents/GoodGit/M2020/Workshop-2020-Cleveland/alg-stat/AlgebraicOptimization"}|path  
restart
loadPackage "AlgebraicOptimization"
M= QQ[x_1..x_2]
I = ideal(4*(x_1^4+x_2^4),4*x_1^3,4*x_2^3)
dualI = projectiveDual(I)
radical I==I
S = ring dualI
