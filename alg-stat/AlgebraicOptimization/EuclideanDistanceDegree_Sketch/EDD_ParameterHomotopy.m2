--restart
--Projective formulation for intersections with linear spaces

EDDegreeParameterHomotopyOptions=new Type of MutableHashTable
-- Directory=> home directory where the files will be stored.

--method used to write the files
-- WriteMethod => leftKernelUnitEDDegree

--method used to run the computation
-- RunMethod => runBertiniEDDegree

-- StartWeight => null
-- TargetWeight => null
-- StartData => null
-- TargetData =>null
-- StartData => null
-- TargetData => null
-- StartSubmodel =>{}
-- TargetSubmodel =>{}

--BertiniConfiguration=>{}
--BertiniSubstitute=>{}
--Boundary =>{}


rand:=randomValue
--Assume ring is a complex inexact field
--G is a subset of F. 

projectiveEDDegree=method(Options=>{
	"TargetLinearSpace"=>null,
	"TargetWeight"=>null,
	"TargetData"=>null,
	"TargetIndex"=>null	})
projectiveEDDegree(EDDegreeParameterHomotopyOptions)
projectiveEDDegree=(theDir,G,F,L,weight,data)->(
    theR:=ring first F;
    numX:=#gens theR;
    kk:=(coefficientRing theR);
    if class kk=!=ComplexField then "Error: coefficient ring needs to be a ComplexField. ";
    S:=theR**kk[apply(#L+#G+1,i->"L"|i)]**kk[apply(numX,i->"u"|i)]**kk[apply(numX,i->"w"|i)]**kk[numerHB,denomQ]**kk[apply(numX-1,i->"gam"|i)];
    xList:=flatten entries basis({1,0,0,0,0,0},S);
    lamList:=flatten entries basis({0,1,0,0,0,0},S);
    uList:=flatten entries basis({0,0,1,0,0,0},S);
    wList:=flatten entries basis({0,0,0,1,0,0},S);
    gamList:=flatten entries basis({0,0,0,0,0,1},S);
    jac:=sub(matrix makeJac(apply(L|G,i->sub(i,S)),xList),S);
    topRow:=apply(#weight,i->sub(denomQ,S)*uList_i-sub(numerHB,S)*xList_i*wList_i);
    M:=matrix{topRow}||jac;
    degRescale:={3}|apply(L,i->1)|(G/degree/first);
    maxDeg:=(max degRescale);
    --print degRescale;
    degRescale=apply(degRescale,i->maxDeg-i);
    --print degRescale;
    LV:=matrix{apply(lamList,degRescale,(lam,j)->if j==0 then sub(lam,S) else if j>0 then sub(lam,S)*(sub(numerHB,S))^j else print "Error: Homogenized incorrectly.")};
    --print LV; 
    critEq:=flatten entries((LV*sub(M,S)));
    win:=L|G|apply(#critEq-1,i->critEq_i+gamList_i*last critEq);
    theConstants:=(transpose{uList,data})|(transpose{wList,weight})|(transpose{gamList,apply(gamList,i->random CC)});
----Input file 
    makeB'InputFile(theDir,NameB'InputFile=>"inputCriticalPointSuperSet",
	HomVariableGroup=>{xList,lamList},
	B'Configs=>{UseRegeneration=>1,TrackType=>0,PrintPathProgress=>1000},
	B'Polynomials=>win,
	B'Functions=>{numerHB=>sum apply(uList,xList,(u,x)->u*x),denomQ=>sum apply(wList,xList,(w,x)->w*x^2)},
	B'Constants=>theConstants
	);
-----Membership test files.
    imt:=(s,k,bp)->makeB'InputFile(theDir,NameB'InputFile=>("inputMembershipTest"|s|toString k),
	AffVariableGroup=>flatten{xList,lamList},
	B'Configs=>{UseRegeneration=>1,TrackType=>k,PrintPathProgress=>1000},
	B'Polynomials=>bp,
	B'Functions=>{numerHB=>sum apply(uList,xList,(u,x)->u*x),denomQ=>sum apply(wList,xList,(w,x)->w*x^2)},
	B'Constants=>theConstants
	);
--Filter Residuals
    imt("Residual",1,{last critEq});
    imt("Residual",3,{last critEq});
--UBeta
    imt("Degenerate",1,{"numerHB*denomQ*L0"});
    imt("Degenerate",3,{"numerHB*denomQ*L0"});
--Filer component    
    imt("Component",1,L|F);
    imt("Component",3,L|F);
        )  

linearSpaceIntersectionEDDegree=linearSpaceIntersectionUnitEDDegree=(theDir,L,G,F)->linearSpaceIntersectionWeightEDDegree(theDir,L,G,F,apply(#gens ring first F,i->rand()),apply(#gens ring first F,i->1_(ring first F)))
linearSpaceIntersectionGenericEDDegree=(theDir,L,G,F)->linearSpaceIntersectionWeightEDDegree(theDir,L,G,F,apply(#gens ring first F,i->rand()),apply(#gens ring first F,i->rand()))

runBertiniLinearSpaceIntersectionEDDegree=(storeBM2Files)->(
    runBertini(storeBM2Files,NameB'InputFile=>"inputCriticalPointSuperSet");
    moveB'File(storeBM2Files,"bertini_session.log","bertini_session_CriticalPointSuperSet.log",CopyB'File => true);
    moveB'File(storeBM2Files,"nonsingular_solutions","member_points");
--Residual
    runBertini(storeBM2Files,NameB'InputFile=>"inputMembershipTestResidual1");
    moveB'File(storeBM2Files,"bertini_session.log","bertini_session_MembershipTestResidual1.log",CopyB'File => true);
    runBertini(storeBM2Files,NameB'InputFile=>"inputMembershipTestResidual3");
    moveB'File(storeBM2Files,"bertini_session.log","bertini_session_MembershipTestResidual3.log",CopyB'File => true);
    imResidual:=importIncidenceMatrix(storeBM2Files);                                                                           
--Degenerate
    runBertini(storeBM2Files,NameB'InputFile=>"inputMembershipTestDegenerate1");
    moveB'File(storeBM2Files,"bertini_session.log","bertini_session_MembershipTestDegenerate1.log",CopyB'File => true);
    runBertini(storeBM2Files,NameB'InputFile=>"inputMembershipTestDegenerate3");
    moveB'File(storeBM2Files,"bertini_session.log","bertini_session_MembershipTestDegenerate3.log",CopyB'File => true);
    imDegenerate:=importIncidenceMatrix(storeBM2Files);
--Component
    runBertini(storeBM2Files,NameB'InputFile=>"inputMembershipTestComponent1");
    moveB'File(storeBM2Files,"bertini_session.log","bertini_session_MembershipTestComponent1.log",CopyB'File => true);
    runBertini(storeBM2Files,NameB'InputFile=>"inputMembershipTestComponent3");
    moveB'File(storeBM2Files,"bertini_session.log","bertini_session_MembershipTestComponent3.log",CopyB'File => true);
    imComponent:=importIncidenceMatrix(storeBM2Files);
    EDDeg:=0;
    scan(#imResidual,i->if imResidual_i=!={} and imDegenerate_i=={} and imComponent_i=!={} then EDDeg=EDDeg+1);
    moveB'File(storeBM2Files,"bertini_session_CriticalPointSuperSet.log","bertini_session.log");
--    return(imResidual,imDegenerate,imComponent)
    return(EDDeg)
     )                                                                           
end

---EXAMPLES

--path=prepend("/Users/jo/Dropbox/Euclidean distance degree/Projective varieties/ComputingEDDegree",path)
load"LinearSpaceIntersectionEDDegree.m2"

--[EX 1] 
----Key words: 2 by 3 matrices, non complete intersection
--storeBM2Files="/Users/jo/Desktop/BertiniOutputFiles/****"
R=QQ[x0,x1,x2,y0,y1,y2];
F=flatten entries gens minors(2,genericMatrix(R,3,2))
G=drop(F,-(#F-2))
linearSpaceIntersectionEDDegree(storeBM2Files,{},G,F)
runBertiniLinearSpaceIntersectionEDDegree(storeBM2Files)--2
linearSpaceIntersectionGenericEDDegree(storeBM2Files,{},G,F)
runBertiniLinearSpaceIntersectionEDDegree(storeBM2Files)--10


--[EX 2] 
----Key words: 3 by 3 matrices rank two matrices, singular variety
--storeBM2Files="/Users/jo/Desktop/BertiniOutputFiles/****"
R=QQ[x11,x12,x13,
    x21,x22,x23,
    x31,x32,x33];
F=flatten entries gens minors(3,genericMatrix(R,3,3))
G=F

L={}
linearSpaceIntersectionUnitEDDegree(storeBM2Files,L,G,F)
runBertiniLinearSpaceIntersectionEDDegree(storeBM2Files)--3
linearSpaceIntersectionGenericEDDegree(storeBM2Files,L,G,F)
runBertiniLinearSpaceIntersectionEDDegree(storeBM2Files)--39


--These results agree with those on page 5 of https://www.researchgate.net/publication/258374161_Exact_Solutions_in_Structured_Low-Rank_Approximation/download
L={x12-x21,x31-x22,x31-x13,x32-x23}
linearSpaceIntersectionUnitEDDegree(storeBM2Files,L,G,F)
runBertiniLinearSpaceIntersectionEDDegree(storeBM2Files)--9
linearSpaceIntersectionGenericEDDegree(storeBM2Files,{x12-x21,x31-x22,x31-x13,x32-x23},G,F)
runBertiniLinearSpaceIntersectionEDDegree(storeBM2Files)--13



