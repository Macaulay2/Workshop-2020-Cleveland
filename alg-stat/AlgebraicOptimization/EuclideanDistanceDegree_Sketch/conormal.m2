
conormalVariety=method(Options=>{		})
conormalVariety(Ideal):= o-> (I)->(
    R:=ring I;
    numX:=#gens R;
    kk:=coefficientRing R;
    S:=R**kk[apply(numX,i->"yDual"|i)];
    primalVars := flatten entries basis({1,0},S);
    dualVars := flatten entries basis({0,1},S);
    rI:=sub(I,S);    
    jac:=apply(flatten entries gens rI,i->apply(primalVars,j->diff(j,i)));
    singI:=ideal singularLocus rI;
    augJac=matrix{dualVars}||matrix jac;
    CV:=minors(1+codim I,augJac)+rI;
    CV=saturate(CV,singI);    
    return CV    
    )

-*
R=QQ[x0,x1,x2,x3]
I=ideal sum apply(gens R,i->i^3);
CV=conormalVariety(I);
multidegree CV;
randomSlice=(c)->apply(c,i->random({1},R)+2*random({1},R))

codimSlice=1;
I1=I+ideal(randomSlice(codimSlice));
CV1=conormalVariety(I1);
multidegree CV1
*-


testEDDegreeConjecture=method(Options=>{		})
testEDDegreeConjecture(Ideal):= o-> (I)->(--Homogeneous ideal
--    wu:=determinantalUnitEuclideanDistanceDegree(flatten entries gens I)    ;
    cod=6;
    wu:=leftKernelUnitEDDegree(theDir,cod,flatten entries gens I)    ;
    print("primal Unit",wu);
--    wg:=determinantalGenericEuclideanDistanceDegree(flatten entries gens I)  ;  
    wg:=leftKernelGenericEDDegree(theDir,cod,flatten entries gens I)  ;  
    print("primal Gen",wg);
    R:=ring I;
    numX:=#gens R;
    kk:=coefficientRing R;
    S:=R**kk[apply(numX,i->"yDual"|i)];
    primalVars := flatten entries basis({1,0},S);
    dualVars := flatten entries basis({0,1},S);
    rI:=sub(I,S);    
    jac:=apply(flatten entries gens rI,i->apply(primalVars,j->diff(j,i)));
    singI:=ideal singularLocus rI;
    augJac=matrix{dualVars}||matrix jac;
    CV:=minors(1+codim I,augJac)+rI;
    CV=saturate(CV,singI);
    dualX:=eliminate(primalVars,CV);
    dualF:=flatten entries gens sub(dualX,kk[dualVars]);
    dwu:=determinantalUnitEuclideanDistanceDegree(dualF)    ;
    print("dual Unit",dwu);
    dwg:=determinantalGenericEuclideanDistanceDegree(dualF)  ;         
    print("dual Gen",dwg);
--    return CV    
    )

R=QQ[x0,x1,x2,x3]
F={det matrix{{x0,x1},{x2,x3}}}
testEDDegreeConjecture ideal F

R=QQ[x0,x1,x2,x3]
F={det matrix{{x0,x1},
	{x2,x3}},x1-x2}
testEDDegreeConjecture ideal F

R=QQ[x0,x1,x2,x3]
F={det matrix{{x0,x1},{x2,x3}},random({1},R)}
testEDDegreeConjecture ideal F

--m=5. 
R=CC[x1,x2,x3,x4,x5,x6,x7,x8,x9]
codimSlice=4
F={det matrix{{x9,x1,x2},{x3,x4,x5},{x6,x7,x8}}}|apply(codimSlice,i->random({1},R))
testEDDegreeConjecture ideal F
codim 4

--5x5 matices
--number1=genericEDDegree(X3)-unitEDDegree(X3)
--number2=genericEDDegree(X2)-unitEDDegree(X2)



