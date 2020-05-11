debug needsPackage "IntegralClosure"
integralClosure(Ideal, ZZ) := opts -> (I,D) ->(
    S:= ring I;
    z:= local z;
    w:= local w;
    Reesi := (flattenRing reesAlgebra(I,Variable =>z))_0;
    Rbar := integralClosure(Reesi, opts, Variable => w);
    zIdeal := ideal(map(Rbar,Reesi))((vars Reesi)_{0..numgens I -1});
    zIdealD := module zIdeal^D;
    RbarPlus := ideal(vars Rbar)_{0..numgens Rbar - numgens S-1};
    RbarPlusD := module RbarPlus^D;
    gD := matrix inducedMap(RbarPlusD, zIdealD);
    --     MM=(RbarPlus^D/(RbarPlus^(D+1)));
    mapback := map(S,Rbar, matrix{{numgens Rbar-numgens S:0_S}}|(vars S), DegreeMap => d -> drop(d, 1));
    M := coker mapback presentation RbarPlusD;
    ID := I^D;
    f := map(M, module ID, mapback gD);
    error "debug me";
    extendIdeal(ID,f)
    )

end--

restart
needs "bug-integralClosure.m2"
R=ZZ/32003[a,b,c,d,e,f]
I=ideal(a*b*d,a*c*e,b*c*f,d*e*f);
trim(J=I^2)
K=integralClosure(I,2) -- integral closure of J = I^2
--time K' = integralClosure(I^2)  -- how long does this take?
F=ideal(a*b*c*d*e*f);
gens(F^2)%J^2 -- so F satisfies X^2-m, with m\in J^2.
assert(isSubset(F, K)) -- F should be contained in the integral closure.
assert(K != J)


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


-- Mike playing:
