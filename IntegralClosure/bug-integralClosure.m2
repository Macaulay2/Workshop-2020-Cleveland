R=ZZ/32003[a,b,c,d,e,f]
I=ideal(a*b*d,a*c*e,b*c*f,d*e*f);
trim(J=I^2)
K=integralClosure(I,2) -- integral closure of J = I^2
time K' = integralClosure(I^2)
F=ideal(a*b*c*d*e*f);
gens(F^2)%J^2 -- so F satisfies X^2-m, with m\in J^2.
isSubset(F,K)==false -- but should be true
K==J -- true, but should be false: K should be larger -- should contain F.

viewHelp integralClosure
apply (10, i->gens(F^i)%(J^i))

restart
R=QQ[a,b,c,d]
I=ideal"ab,ac,ad,bc,bd,cd"
integralClosure (I,2)
F = ideal"abcd"
gens(F^2) % I^4

trim(J=I^2)
K=integralClosure(I,2)
