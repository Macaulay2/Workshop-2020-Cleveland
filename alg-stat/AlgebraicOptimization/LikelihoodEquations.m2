newPackage(
  "LikelihoodEquations",
  Version => "0.1",
  Date => "May 14, 2020",
  Authors => {
    {Name => "Fatemeh Tarashi Kashani", 
    Email => "tarashikashanifatemeh@gmail.com", 
    HomePage => "https://www.linkedin.com/in/fatemehtarashi/"},
    {Name => "Your name here",
    Email => "Your email here",
    HomePage => "Your page here"}
  },
  Headline => "A package for ikelihood equations",
  DebuggingMode => true,
)

export {
  -- Methods
  "pLikelihood",
  -- Options
  --Types and keys
 
}


pLikelihood = method(); -- option must be add
-- (Alg. 18 in Solving the Likelihood Equations(https://arxiv.org/pdf/math/0408270)
-- input: Polynomials f_0,...,f_n with ∑ f_i = 1 and vector u
-- output: Generators of the parametric likelihood ideal
pLikelihood List := flist  -> (
    m1 := diagonalMatrix flist;
    mlist = for i in flist list transpose jacobian ideal(i);
    m2 =  fold(mlist, (i,j) -> i || j);
    M = m1 | m2;
    Ju' = ideal generators ker M;
    ju = saturate(Ju', product F)
)

TEST ///
R= QQ[p,s,t];
f_0=     p *       (1-s)^4 +     (1-p) *       (1-t)^4;
f_1= 4 * p * s   * (1-s)^3 + 4 * (1-p) * t   * (1-t)^3;
f_2= 6 * p * s^2 * (1-s)^2 + 6 * (1-p) * t^2 * (1-t)^2;
f_3= 4 * p * s^3 * (1-s)   + 4 * (1-p) * t^3 * (1-t);
f_4=     p * s^4           +     (1-p) * t^4;
F = {f_0,f_1,f_2,f_3,f_4}; --- list of function as input
lf = pLikelihood F

assert( lf == ) 
///


doc ///
Key
  pLikelihood
  (pLikelihood, List)
Headline
  Generators of the parametric likelihood ideal
Usage
  pLikelihood(Flist)
Inputs
  Flist:
    list of function
Outputs
  :Ideal
    Generators of the parametric likelihood ideal
--Consequences
--  asd
Description
  Text
    ---
  Example
    R= QQ[p,s,t]
    f_0=     p *       (1-s)^4 +     (1-p) *       (1-t)^4;
    f_1= 4 * p * s   * (1-s)^3 + 4 * (1-p) * t   * (1-t)^3;
    f_2= 6 * p * s^2 * (1-s)^2 + 6 * (1-p) * t^2 * (1-t)^2;
    f_3= 4 * p * s^3 * (1-s)   + 4 * (1-p) * t^3 * (1-t);
    f_4=     p * s^4           +     (1-p) * t^4;
    F = {f_0,f_1,f_2,f_3,f_4}; --- list of function as input
    pLikelihood(F)
--  Code
--    todo
--  Pre
--    todo
--Caveat
--  todo
--SeeAlso
--  
///
