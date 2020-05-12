newPackage(
  "AlgebraicOptimization",
  Version => "0.1", 
  Date => "1",
  Authors => {{Name => "a", 
  Email => "b", 
  HomePage => "c"}},
  Headline => "a",
  DebuggingMode => true,
  PackageImports => {"Elimination"}
)

export {}

-- Code here

computeDualVariety = method(Options => {}); -- Maybe options are needed?
-- (Alg. 5.1 in SIAM book)
-- Takes homogeneous ideal as input, returns ideal of dual of the projective variety
computeDualVariety Ideal := Ideal => opts -> I -> (
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
dualI = computeDualVariety(I)
S = ring dualI
assert( dualI == ideal(S_0^2 - S_1^2 - S_2^2)) 
///



-- Documentation below

beginDocumentation()

-- template for package documentation
--  doc ///
--  Key
--    AlgebraicOptimization
--  Headline
--    TODO
--  Description
--    Text
--      Todo
--    Example
--      todo
--  Caveat
--  SeeAlso
--  ///


-- template for function documentation
--  doc ///
--  Key
--    todo
--  Headline
--    todo
--  Usage
--    todo
--  Inputs
--    todo
--  Outputs
--    todo
--  Consequences
--    todo
--  Description
--    Text
--      todo
--    Example
--      todo
--    Code
--      todo
--    Pre
--  Caveat
--  SeeAlso
--  ///

  TEST ///
  -- test code and assertions here
  -- may have as many TEST sections as needed
  ///

