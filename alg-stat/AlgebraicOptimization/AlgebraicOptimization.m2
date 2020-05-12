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
  "projectiveDual"
}

-- Code here

projectiveDual = method(Options => {}); -- Maybe options are needed?
-- (Alg. 5.1 in SIAM book)
-- Takes homogeneous ideal as input, returns ideal of dual of the projective variety
projectiveDual Ideal := Ideal => opts -> I -> (
  if not isHomogeneous I then error("Ideal has to be homogeneous");
  c := codim I;
  jacI := transpose jacobian I;
  R := ring I;
  numVars := #gens R;
  u := symbol u;
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
--  Code
--    todo
--  Pre
--    todo
--Caveat
--  todo
--SeeAlso
--  todo
///

  TEST ///
  -- test code and assertions here
  -- may have as many TEST sections as needed
  ///

