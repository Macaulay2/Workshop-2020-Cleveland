The Euclidean Distance Degree of an Algebraic Variety: A walk through. 
Reference: https://arxiv.org/pdf/1309.0049.pdf

0. We consider the squared distance function d_u on an algebraic variety X. 
Our aim is to compute ED degrees and/or compute the corresponding critical points. 


Idea 1. Using Lagrange multipliers, and the observation that...

From the text: we seek to satisfy the constraints x∈X, x not in X_\sing ,
and (u−x) ⊥ T_xX

This makes intuitive sense from optimization techniques we learn in calculus.

2. Example 1.1 

kk=ZZ/30103--Working over finite fiels often helps with speed.
kk=QQ
R=kk[x,y,u,v]--Symbolic computation
cardioid = ((x^2+y^2+x)^2 -(x^2+y^2))
--gradient vector for our distance function depends on data. 
duGrad = matrix{{x,y}-{u,v}}
duGrad = sub(duGrad,{u=>7,v=>99})
--   ^^^ This is what is done in practice. 
--Caveat: we assume the chosen data is generic
--Our algorithm here is probabilistic. 

--gradient vector for the constraints. 
jac = matrix{{diff(x,cardioid),diff(y,cardioid)}}
jacBar = duGrad||jac
I1 = minors(2,jacBar ) --(u−x) ⊥ T_xX
I2 = ideal cardioid
criticalIdeal=saturate(I1+I2,ideal singularLocus ideal cardioid)

degree criticalIdeal
--If u,v are fixed then with probability one you will get 3,
--else if u,v are indeterminants you will get 7. 

--This let's you determine the x coordinates. 
E = (eliminate({y},criticalIdeal))_0
coefficients(E,Variables=>x)
if kk===QQ then roots sub(E,kk[x])

Recap: So far we have found critical points of the distance function for a plane curve.

Remark: These ideas generalize to arbitrary objective functions. 
ML degrees count critical points for a different objective function. 


3. ED Critical Ideal (equation 2.1)
Compare these equations to the curve case.
There are three parts. 
The first part is I_X which says the point x is in X. 
The second part is the ideal generated by minor,
which gives the condition that the Jacobian vector 
The last part saturates the singular locus. 

These are analaogus to the setup in Marc's function from earlier today. 


4. Lemma 2.1. This essentially says,
the ED degree is well defined and 
it makes sense to take a random choice of data to determine it. 


5. Example 2.5
--This is M2 code that we can base our method on. 

6. Example 2.7 
--There are special situations when the model has extra structure and a nicer algorithm exists. 
--One such instance is the projective ED degree for affine cones. 
--It would be good for our package have these algorithms as well. 
