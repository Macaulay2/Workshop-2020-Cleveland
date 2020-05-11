
restart
R=QQ[x,y,z]
f=x^3+x+y
g1=y^2+z^3+5
g2=(x+y)
I=ideal(f,g1*g2)
decompose I
primaryDecomposition I
oo/decompose
needsPackage"Bertini"
bertiniPosDimSolve {f,g1*g2}

restart
loadPackage("EuclideanDistanceDegree",Reload=>true)
help EuclideanDistanceDegree

-*
restart
installPackage("EuclideanDistanceDegree")
help EuclideanDistanceDegree
*-





examples EuclideanDistanceDegree
     R=QQ[x,y];
     F={x^2+y^2-1};
     2==determinantalUnitEuclideanDistanceDegree(F)
     R=QQ[x,y];
     F={x^2+y^2-1};  c=1;
     leftKernelUnitEDDegree(storeBM2Files,c,F)
     2==runBertiniEDDegree(storeBM2Files)
     R=QQ[x,y];
     F={x^2+y^2-1};  c=1
     4==determinantalGenericEuclideanDistanceDegree(F)
     leftKernelGenericEDDegree(storeBM2Files,c,F)
     4==runBertiniEDDegree(storeBM2Files)
     R=QQ[x,y];
     F={x^2+y^2-1};
     genericWeightVector={2,3};
     unitWeightVector={1,1};
     dataVector={5,7};
     4==symbolicWeightEDDegree(F,dataVector,genericWeightVector)
     2==symbolicWeightEDDegree(F,dataVector,unitWeightVector)
     R=QQ[x1,x2,x3,x4]
     F={det genericMatrix(R,2,2)};
     P=(F,F)
     6==numericEDDegree(P,"Generic")
     2==numericEDDegree(P,"Unit")
     R=QQ[x1,x2,x3,x4,x5,x6]
     F=(minors(2,genericMatrix(R,3,2)))_*;
     G=drop(F,-1);
     P=(F,G)
     #G==codim ideal F;
     10==numericEDDegree(P,"Generic")
     2==numericEDDegree(P,"Unit")
     dir=temporaryFileName();if not fileExists dir then mkdir dir;
     R=QQ[x1,x2,x3,x4,x5,x6]
     F=(minors(2,genericMatrix(R,3,2)))_*;
     G=drop(F,-1);
     #G==codim ideal F;
     P=(F,G)
     NCO=newNumericalComputationOptions(dir,P)
     NCO#"TargetWeight"=apply(#gens R,i->1)
     homotopyEDDegree(NCO,"Weight",true,true)
     NCO#"TargetWeight"=(apply(-1+#gens R,i->1))|{0}
     homotopyEDDegree(NCO,"Weight",false,true)
     dir=temporaryFileName();if not fileExists dir then mkdir dir;
     R=QQ[x1,x2,x3,x4,x5,x6]
     F=(minors(2,genericMatrix(R,3,2)))_*;
     G=drop(F,-1);
     #G==codim ideal F;
     P=(F,G)
     NCO=newNumericalComputationOptions(dir,P)
     NCO#"TargetData"=apply(#gens R,i->1)
     homotopyEDDegree(NCO,"Data",true,true)
     NCO#"TargetWeight"=(apply(-1+#gens R,i->1))|{0}
     homotopyEDDegree(NCO,"Data",false,true)