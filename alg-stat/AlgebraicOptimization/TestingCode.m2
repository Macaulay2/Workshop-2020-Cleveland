
EDDegree =(someIdeal) -> (I:=ideal someIdeal; 
    R:= ring I;
    S:=QQ[u_1..u_(#gens R)];
    T:= R**S;
    duGrad:= sub(vars R,T)- sub(vars S,T);
    L:=apply(gens S, u->sub(u,T) => random(1,100));
    duGradinT := sub(duGrad,L);
    duGradinR := sub(duGradinT,R);
    jac := transpose jacobian(I);
    jacBar := duGradinR || jac;
    I1 := minors(#gens R - dim I+1,jacBar);
    criticalIdeal := saturate(I1+I, ideal singularLocus I);   
    return degree criticalIdeal;
    );




