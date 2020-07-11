-- This file contains code that is being ported from the original
-- InvariantRing package by Thomas Hawes.

------------------------------------------------
-- molienSeries
-- Calculates the Molien (Hilbert) series of the invariant ring of a finite 
-- group G.
-- Considers two cases: when the field the matrices are defined over is QQ 
-- and when it is a general number field.
-- This is to get around the fact that frac for number fields is not yet
-- implimented in Macaulay2
-- The author thanks an anonymous referee for suggested improvements to this 
-- method to ensure a consistent class of polynomial is returned 
-- Reference:
-- [S08] Sturmfels, B. "Algorithms in Invariant Theory". 2nd Edition. Wien New
-- York: Springer-Verlag, 2008.        
------------------------------------------------

-* Porting notes:

o Applies to FiniteGroupAction rather than RingOfInvariants
o TODO: original code checked characteristic is nonzero.
  Should we check this when group is constructed?
  Does this work in pos char in the non modular case?
o Original code distinguished cases when coefficient ring K is QQ
  from other fields because frac(K[U]) is not implemented when
  K is a finite field extension of QQ created as quotient ring.
  New code treats all fields as the most general one.

*-

molienSeries = method();
molienSeries FiniteGroupAction:= G -> (
     K:=coefficientRing ring G;
     U:=symbol U;
     -- frac of a general number field is not implemented yet in Macaulay2. So
     -- need to calculate fractions and sum of fractions 'manually'. 
     n:= numgens ring G;
     Ku:= K[U]; 
     In:= id_(Ku^n);
     L:=apply(group G, M->(det(In-U*sub(M,Ku)))); 
     -- L is a list {p_1(U),...,p_m(U)}, say, (with m=#G), of reciprocals of 
     -- summands in the Molien series expansion.
     numerat:=sum(#L,i->product(drop(L,{i,i})));  
     -- in above notation, (and using LaTeX syntax):
     -- numerat=numerator of \frac{1}{p_1(U)}+...+\frac{1}{p_m(U)}.
     denominat:=#(group G)*product(L); 
     A:=degreesRing(1);
     -- A is the ring containing the numerator and denominator of the
     -- Hilbert series
     T:= first gens A; -- T is the variable of the Hilbert series	  
     f:=map(A,Ku,{T}); -- Ring map K[U] -> A that sends U to T
     -- Note that any non-integer elements of K would be sent to zero.  
     h:=new Divide from {f(numerat),factor(f(denominat))};
     return reduceHilbert h;
     );
