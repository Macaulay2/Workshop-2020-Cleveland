newPackage(
  "LikelihoodEquations",
  Version => "0.1",
  Date => "May 14, 2020",
  Authors => {
    {Name => "Fatemeh Tarashi Kashani", 
    Email => "tarashikashanifatemeh@gmail.com", 
    HomePage => "https://www.linkedin.com/in/fatemehtarashi/"},
  Headline => "A package for ikelihood equations",
  DebuggingMode => true,
)

export {
  -- Methods
  "pLikelihood",
  -- Options
  --Types and keys
 
}


MLdegree = method(); -- option must be add
-- (Alg. 18 in Solving the Likelihood Equations(https://arxiv.org/pdf/math/0408270)
-- input: Polynomials f_0,...,f_n with ∑ f_i = 1 and vector u
-- output: Generators of the parametric likelihood ideal
MLdegree (List,List) := (F,u)-> (
    if not (sum F ==1) then error("The sum of functions is not equal to one.");
    m1 = diagonalMatrix F;
    m2 = for i in F list transpose jacobian ideal(i);
    m2p = fold(m2, (i,j) -> i || j);
    M = m1 | m2p;
    g = generators ker M;
    g'=matrix drop(entries g,-numrows g+#u);
    Ju'=ideal (matrix {u} * g');
    Ju = saturate(Ju');
    
    degree Ju
)

TEST ///
R = QQ[t]
s=1
f_0 = s^3 * (-t^3-t^2-t+1)
f_1 = s^2*t
f_2 = s*t^2
f_3 = t^3
u = {2,3,5,7}
F = {f_0,f_1,f_2,f_3} --- list of function as input

assert( MLdegree (F,u) == 3) 
///


doc ///
Key
   MLdegree
   (MLdegree,List,List) 
Headline
  Degree of the parametric likelihood
Usage
  MLdegree (F,u)
Inputs
  F:
    list of function
  u:
    list of numerical data
Outputs
  :Number
    The Maximum Likelihood Degree
--Consequences
--  asd
Description
  Text
    ---
  Example
    R = QQ[t]
    s=1
    f_0 = s^3 * (-t^3-t^2-t+1)
    f_1 = s^2*t
    f_2 = s*t^2
    f_3 = t^3
    u = {2,3,5,7}
    F = {f_0,f_1,f_2,f_3} --- list of function as input
    MLdegree (F,u)
--  Code
--    todo
--  Pre
--    todo
--Caveat
--  todo
--SeeAlso
--  
///
