--restart
rand:=randomZZ--This is the function used to compute random numbers. 
--random(QQ) is not a good choice in practice.
--This function computes weighted ED degrees
--makeJac:=(F,x)->apply(F,f->apply(x,j->diff(j,f)))
symbolicOptions={ReturnCriticalIdeal=>false		}
symbolicWeightEDDegree=method(Options=>symbolicOptions)
symbolicWeightEDDegree(List,List,List):= o-> (F,data,weight)->(
    xList:=gens ring first F;
    numX:=#xList;
    I:=ideal(F);
    jac:=matrix makeJac(F,xList);---Fix this so max can run it. 
    topRow:=apply(#weight,i->2*weight_i*(xList_i-data_i));
    M:=matrix{topRow}||jac;
    c:=codim I;
    win:=I+minors(c+1,M);
    unitQ:=sum apply(xList,i->i^2);
    sl:=radical ideal singularLocus I;
    win=saturate(win,sl);
    if o.ReturnCriticalIdeal then return win else return degree win
--    return degree win
    )

determinantalUnitEuclideanDistanceDegree=method(Options=>symbolicOptions)
determinantalUnitEuclideanDistanceDegree(List):= o-> (F)->symbolicWeightEDDegree(F,
    apply(#gens ring first F,i->rand()),
    apply(#gens ring first F,i->1_(ring first F)))

determinantalGenericEuclideanDistanceDegree=method(Options=>symbolicOptions)
determinantalGenericEuclideanDistanceDegree(List):= o-> (F)->symbolicWeightEDDegree(F,apply(#gens ring first F,i->rand()),apply(#gens ring first F,i->rand()))



-*
R=QQ[t1,t2,t3,p1,p2,p3,p4,p5,p6]
I=ideal(drop(gens R,3)-{t1*t3,t2*t3,t1*t2*t3,t1^2*t2*t3,t1^3*t2*t3,t1*t2^2*t3})
E=eliminate({t1,t2,t3},I+ideal(t3-1))-- ED degree is 25
E=eliminate({t1,t2,t3},I)-- ED degree is 28
S=QQ[drop(gens R,3)]
determinantalGenericEuclideanDistanceDegree(flatten entries gens sub(E,S))
determinantalGenericEuclideanDistanceDegree()
*-


-*
R=QQ[p1,p2,p3,p4,p5,p6]
I=ideal(drop(gens R,3)-{t1*t3,t2*t3,t1*t2*t3,t1^2*t2*t3,t1^3*t2*t3,t1*t2^2*t3})
E=eliminate({t1,t2,t3},I+ideal(t3-1))-- ED degree is 25
E=eliminate({t1,t2,t3},I)-- ED degree is 28
S=QQ[drop(gens R,3)]
determinantalGenericEuclideanDistanceDegree(flatten entries gens sub(E,S))
determinantalGenericEuclideanDistanceDegree()

*-