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
  "makePrimalDualRing",
  "conormalVariety",
  -- Options
  "DualVariable"
}

-- Code here

conormalVariety = method();
-- Computes the conormal variety with respect to the (polynomial)
-- objective function p
conormalVariety (Ideal, RingElement) := Ideal => (I,p) -> (
  if not ring I === ring p then error("Ideal and polynomial must be in same ring.");
  R := ring p;
  if not degreeLength R == 2 then error("ring doesn't have degree length 2") -- This could create the primal dual ring!
)

makePrimalDualRing = method(Options => {DualVariable => null});
-- Creates a ring with the primal and dual variables
makePrimalDualRing Ring := Ring => opts -> R -> (
  u := if opts.DualVariable === null then symbol u else opts.DualVariable;
  dualR := (coefficientRing R)[u_0..u_(#gens R - 1)];
  R ** dualR
)


projectiveDual = method(Options => options makePrimalDualRing);
-- (Alg. 5.1 in SIAM book)
-- Takes homogeneous ideal as input, returns ideal of dual of the projective variety
projectiveDual Ideal := Ideal => opts -> I -> (
  if not isHomogeneous I then error("Ideal has to be homogeneous");
  c := codim I;
  jacI := transpose jacobian I;
  R := ring I;
  numVars := #gens R;
  u := if opts.DualVariable === null then symbol u else opts.DualVariable;
  dualR := (coefficientRing R)[u_0..u_(numVars-1)];
  S := R ** dualR;
  jacBar := sub(vars dualR, S) || sub(jacI, S);
  J' := sub(I, S) + minors(c+1, jacBar);
  J := saturate(J', minors(c, sub(jacI,S)));
  xVars := (gens R) / (i -> sub(i,S));
  sub(eliminate(xVars, J), dualR)
)

TEST ///
S = QQ[x_0..x_2]
I = ideal(x_2^2-x_0^2+x_1^2)
dualI = projectiveDual(I)
S = ring dualI
assert( dualI == ideal(S_0^2 - S_1^2 - S_2^2)) 
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
  makePrimalDualRing
  [makePrimalDualRing, DualVariable]
Headline
  Creates a ring with primal and dual variables
Usage
  makePrimalDualRing(R)
Inputs
  R:Ring
Outputs
  :Ring
Description
  Text
    Return a ring containing both primal and dual variables.
    This is the ring where the conormal variety lives.
    By default, the dual variables have the symbol u, but this can be changed using the
    optional argument {\tt DualVariable}
  Example
    R = QQ[x_0..x_4]
    S = makePrimalDualRing(R)
    gens S
    makePrimalDualRing(R, DualVariable => y)
  Text
    The primal variables have degree $\{1,0\}$ and the dual variables have degree $\{0,1\}$
  Example
    basis({1,0}, S)
    basis({0,1}, S)
SeeAlso
  conormalVariety
///

doc ///
Key
  conormalVariety
///

TEST ///
  -- test code and assertions here
  -- may have as many TEST sections as needed
///

