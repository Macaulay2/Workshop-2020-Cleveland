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
