--restart
--Projective formulation for intersections with linear spaces

rand:=randomValue
--Assume ring is a complex inexact field
--G is a subset of F. 
NumericalComputationOptions=new Type of MutableHashTable
(stageOne,stageTwo)=(1,2); 
         
parameterKeys={    "StartWeight",    "TargetWeight",
    "StartData",    "TargetData", 
    "GammaVector"}

jacKeys={    "JacobianWitnessModel","JacobianStartSubmodel","JacobianTargetSubmodel"}
modelKeys={    "Model","WitnessModel",    "StartSubmodel", "TargetSubmodel"}
degreeKeys={ "DegreeWitnessModel","DegreeSubmodel"}
--
bertiniKeys={    "BertiniStartFiberSolveConfiguration","BertiniMembershipTestConfiguration",    "BertiniSubstitute","BertiniConstants"}
coordinateKeys={    "PrimalCoordinates",    "HomogeneousVariableGroups",    "AffineVariableGroups"    }
directoryKeys={"Directory"} 
solutionKeys={"TrackSolutions"}
outputKeys={"OutputType","FinerRestriction"}

fixValues={"FixedData","FixedWeight","FixedSubmodel","FixedJacobianSubmodel"}
nocKeys=parameterKeys|jacKeys|modelKeys|degreeKeys|bertiniKeys|coordinateKeys|directoryKeys|solutionKeys|fixValues|outputKeys

defaultFixValues={"StartData","StartWeight","StartSubmodel","JacobianStartSubmodel"}
outputValues={"Standard","TestHomotopyConjectureGEDvUED"}


newNumericalComputationOptions=method()
newNumericalComputationOptions(String,Sequence):=(theDir,P)->(
    if #P==3 then (F,G,L):=P;
    if #P==2 then (F,G,L)=(P_0,P_1,{});
    NCO:=new NumericalComputationOptions from apply(nocKeys,i->i=>null);
    NCO#"Directory"=theDir;----directory where the files will be stored.
    NCO#"Model"=F,
    NCO#"WitnessModel"=G;
    NCO#"StartSubmodel"=L;
    NCO#"TargetSubmodel"=L;
    NCO#"DegreeSubmodel"=L/degree/first;
    NCO#"DegreeWitnessModel"=G/degree/first;
    NCO#"JacobianWitnessModel"=diff(matrix{gens ring first G}, transpose matrix{G} );
    NCO#"JacobianTargetSubmodel"=NCO#"JacobianStartSubmodel"=diff(matrix{gens ring first G}, transpose matrix {L} );
    NCO#"PrimalCoordinates"=gens ring first F; ---This is different when working with a parameterization
    numX:=#gens ring first G;
    NCO#"TargetData"=NCO#"StartData"=apply(numX,i->random CC); 
    NCO#"TargetWeight"=apply(numX,i->1);
    NCO#"StartWeight"=apply(numX,i->random CC); 
--    NCO#"GammaVector"=apply(numX-1,i->random CC); 
    scan(bertiniKeys,i->NCO#i={});
    NCO#"HomogeneousVariableGroups"={gens ring first F};
    NCO#"AffineVariableGroups"={};    
    NCO#"FixedData"="StartData";
    NCO#"FixedWeight"="StartWeight";
    NCO#"FixedSubmodel"="StartSubmodel";
    NCO#"FixedJacobianSubmodel"="JacobianStartSubmodel";
    NCO#"JacobianVars"="jv";
    NCO#"GradientVars"="gv";
    NCO#"ScaleVars"="sv";
    NCO#"DataVars"="dv";
    NCO#"WeightVars"="wv";
    NCO#"Infinity"=null;
    NCO#"PairGeneralHyperplaneList"=null;
    NCO#"IsProjective"=false;
    NCO#"OutputType"="Standard";
    NCO#"FinerRestriction"={};
    return NCO
    )


homotopyEDDegree=method()
possibleHT={"Weight","Data","Submodel"}
stageOne=1
stageTwo=2
--ht="Weight"
--isStageOne=true
--isStageTwo=true
homotopyEDDegree(NumericalComputationOptions,String,Boolean,Boolean):=(NCO,ht,isStageOne,isStageTwo)->(    
--(CODE 1) First we set the type of homotopy that will be performed.
    if not member(ht,possibleHT) then error("Argument 1 is in "|toString possibleHT);
    if ht===possibleHT_0 then     weightHomotopy:=true else weightHomotopy=false ;    
    if ht===possibleHT_1 then     dataHomotopy:=true else dataHomotopy=false ;
    if ht===possibleHT_2 then     submodelHomotopy:=true else submodelHomotopy=false ;
--(CODE 2) Extract information from NCO (NumericalComputationOptions).
--The homotopy is highly customizable, which is why we use a new type of MutableHashTable.
    jacL:=NCO#(NCO#"FixedJacobianSubmodel");
    L:=NCO#(NCO#"FixedSubmodel"); 
    startWeight:=  NCO#"StartWeight";
    targetWeight:=NCO#"TargetWeight";
    startData:=  NCO#"StartData";
    targetData:=NCO#"TargetData";
    (lagMult,numerHB,denomQ,primal,tWeight):=("lagMult","numerHB","denomQ","primal","tWeight")   ; 
    (jv,gv,sv):=(NCO#"JacobianVars",    NCO#"GradientVars",    NCO#"ScaleVars");   
    (dv,wv):=(NCO#"DataVars",    NCO#"WeightVars");   
--F is the model, V(G)\cap V(L) is a complete intersection contained in V(F)\cap V(L).
    (F,G,startL,targetL,jacG):=(NCO#"Model",NCO#"WitnessModel",NCO#"StartSubmodel",NCO#"TargetSubmodel",NCO#"JacobianWitnessModel");
--    randomGamma:=NCO#"GammaVector";
    xList:=NCO#"PrimalCoordinates";
--Set hyperplane at infinity
    if NCO#"Infinity"===null 
    then NCO#"Infinity"=makeB'Section(xList,NameB'Section=>"HX");
--(FUNCTION 0) --quickly create variabels
    vRing:=(numVars,s,kk)->kk[apply(numVars,i->s|i)];   
--(CODE 3) Now we make rings.
    nc:=#xList;
    kk0:=QQ; 
    extrinsicRing:=kk0[flatten transpose apply(#G+#L,i->apply(nc,j->jv|i|"v"|j))];
    scan({sv,gv,dv,wv},{#G+#L+1,nc,nc,nc},(s,numVars)->extrinsicRing=extrinsicRing**vRing(numVars,s,kk0));
    symbolicJac:=genericMatrix(extrinsicRing,#G+#L,nc);
    symbolicScaleMatrix:=basis({0,1,0,0,0},extrinsicRing);
    symbolicGradient:=basis({0,0,1,0,0},extrinsicRing);
-- symbolicSystem is the system we want to solve after subsituting subfunctions.
    symbolicSystem:=symbolicScaleMatrix*(symbolicGradient||symbolicJac);
    jacZero:={};
    pairJac:={};
-- (FUNCTION 1) ---pair a row of matrix with values
    pairRowFunction:=(M1,M2,hom)->(	
	arg:=flatten entries M1;
	val:=flatten entries M2;
	scan(#arg,i->if val_i==0 
	    then (jacZero=jacZero|{arg_i=>0};
		symbolicSystem=sub(symbolicSystem,{arg_i=>0}))
	    else pairJac=pairJac|{makeB'Section({val_i},
    	    	B'NumberCoefficients=>{1},	
	    	B'Homogenization=>hom,	
	    	NameB'Section=>arg_i )}));
 --   M1=matrix{{x,y},{z,w}}
--    M2=matrix{{1,2},{5,4}}
--   print peek last pairRow(M1,M2,1,"HX")
-- (FUNCTION 2) ---pair parameters of a parameter homotopy
    pairParameterFunction:=(p0,p1,r1,r2,sym,bool)->(
	if bool then pp:=apply(#p0,i->makeB'Section({p0_i,p1_i},
    	    B'NumberCoefficients=>{r1,r2},		
	    NameB'Section=>sym_i )) else
    if not bool then  pp=apply(#p0,i->makeB'Section({p0_i},
    	    B'NumberCoefficients=>{1},		
	    NameB'Section=>sym_i
	    )));
---(CODE 4) Now set up subfunctions. This is done by pairing a symbol with a value by an option or B'Section.
    weight:=symbolicWeight := gens vRing(nc,wv,kk0);
    data:=symbolicData := gens vRing(nc,dv,kk0);
    pairData:=pairParameterFunction(startData,targetData,"(1-TData)","TData",symbolicData,dataHomotopy);	    
    pairWeight:=pairParameterFunction(startWeight,targetWeight,"(1-TWeight)","TWeight",symbolicWeight,weightHomotopy);
    print ("pairData",peek first  pairData    );
    print ("pairWeight",peek first  pairWeight    );
---(CODE 5) Pair Gradient Vector 
    kk2:=ring first startWeight;
    topS:=kk2[numerHB,denomQ,tWeight];
    (topNumerHB,topDenomQ,topTWeight):=toSequence flatten entries basis({1},topS);
    pairGradient:=apply(#xList,i->makeB'Section({xList_i},
	    ContainsPoint=>{data_i},
	    B'NumberCoefficients=>{weight_i},
	    NameB'Section=>symbolicGradient_(0,i),
	    B'Homogenization=>"HX"));
---(CODE 6) Pair Jacobian: 
--create ring to homogenize rows (indexed by polynomials) of Jacobian 
    jacLG:=jacL||jacG;
    kk3:=coefficientRing ring first F;
    jacRing:=kk3[gens ring first F|{"HX"}];
    HX:=last gens jacRing;
    homogLG:= homogenize(sub(matrix{L|G},jacRing),HX)//entries//flatten;
    homogJac:=    matrix apply(numrows jacLG,i->apply(numcols jacLG,j->diff((gens jacRing)_j,homogLG_i)));
    print("homogenized jacobian",homogJac);
    pairRowFunction(symbolicJac,homogJac,"HX");
---(CODE 7) Pair Scaling variables (Lagrange multipliers): 
--Determine degrees to properly homogenize cols (indexed by variables) of Jacobian
--#pairJac;
--#jacZero;
    (degSubmodel,degWitnessModel):=(NCO#"DegreeSubmodel",NCO#"DegreeWitnessModel");
    degAugJac:={1}|apply(degSubmodel|degWitnessModel,i->i-1);
    maxDegree:=degAugJac//max;
    degRescale:=degAugJac/(i->maxDegree-i);        
    bLagrangeVars:=lagList:=apply(#degRescale,i->"L"|i);
    rescaling:=new MutableList from apply(#degRescale,i->lagList_i);
--Homogenize cols by multiplying by a diagonal matrix of linear products on the left. 
----The following determines these linear products. 
    generalHyperplaneList:={};
    scan(#degRescale,i->scan(
	    degRescale_i, 
	    j->(hg:="H"|i|"v"|j;---wants to be both
		rescaling#i=(rescaling#i)|"*"|hg;
	    	generalHyperplaneList=generalHyperplaneList|{hg})
	    ));
--    print(peek rescaling);
    if NCO#"PairGeneralHyperplaneList"=!=null then 
    pairGeneralHyperplanes:=NCO#"PairGeneralHyperplaneList"  else(
	pairGeneralHyperplanes=apply(#generalHyperplaneList,i->
	    makeB'Section(xList|{"HX"},
		NameB'Section=>generalHyperplaneList_i));
	NCO#"PairGeneralHyperplaneList"=pairGeneralHyperplanes);
--    print(peek first pairGeneralHyperplanes);
    pairScale:=apply(flatten entries symbolicScaleMatrix,rescaling,(i,j)->i=>j);
-- (CODE 8)  Set up inputs for bertini. 
    bModelVars:=gens ring first F|{"HX"}   ;
    bPoly:=homogLG|flatten entries symbolicSystem;
    bConfiguration:={"TrackType"=>0,
	"PrintPathProgress"=>1000}|(NCO#"BertiniStartFiberSolveConfiguration");    
    BF:=pairData|pairWeight|pairJac|pairGradient|pairGeneralHyperplanes|pairScale;
-- (FUNCTIONS 2) Functions for solving (write input)
    writeSolveInputFunction:=(stage,nif)->(
	if stage===stageOne then (PG:={"adfadfdf"}; BC:={"TData"=>0,"TWeight"=>0})
	else if stage===stageTwo
	then (BC={};
	    if dataHomotopy then PG={"TData"}
	    else if weightHomotopy then PG={"TWeight"});
    	if stage===stageOne then bConfiguration=bConfiguration|{"UseRegeneration"=>1};
    	if stage===stageTwo then bConfiguration=bConfiguration|{"UseRegeneration"=>0};
    	makeB'InputFile(NCO#"Directory",
    	    NameB'InputFile=>nif,
	    HomVariableGroup=>{bLagrangeVars,bModelVars},
    	    B'Configs=>bConfiguration|{"ParameterHomotopy"=>stage},
	    B'Polynomials=>bPoly,
	    B'Constants=>jacZero|BC,
	    ParameterGroup=>PG,
    	    B'Functions=>BF
	    ));
-- (FUNCTIONS 2) Functions for solving (run file input)
--our solution file will always be member points. 
    criticalPointName:="criticalPointFile";
    runSolveInputFunction:=(stage,nif)->(
	writeSolveInputFunction(stage,nif); 
    	if stage==stageTwo then(
    	    writeParameterFile(NCO#"Directory",{0},NameParameterFile=>"start_parameters");
    	    writeParameterFile(NCO#"Directory",{1},NameParameterFile=>"final_parameters"));
	runBertini(NCO#"Directory",NameB'InputFile=>nif);
    	readFile(NCO#"Directory");
    	if stage==stageOne then(	
	    moveB'File(NCO#"Directory","bertini_session.log","stageOne_log",CopyB'File=>true);
	    moveB'File(NCO#"Directory","nonsingular_solutions","stageOne_solutions",CopyB'File=>true);
	    moveB'File(NCO#"Directory","nonsingular_solutions","start",CopyB'File=>true);
	    moveB'File(NCO#"Directory","nonsingular_solutions","member_points",CopyB'File=>true);
	    moveB'File(NCO#"Directory","nonsingular_solutions",criticalPointName,CopyB'File=>true));
    	if stage==stageTwo then(
	    moveB'File(NCO#"Directory","bertini_session.log","stageTwo_log",CopyB'File=>true);
	    moveB'File(NCO#"Directory","nonsingular_solutions","stageTwo_solutions",CopyB'File=>true);
	    moveB'File(NCO#"Directory","main_data","stageTwo_main_data",CopyB'File=>true);
	    --moveB'File(NCO#"Directory","nonsingular_solutions","start",CopyB'File=>true);
	    moveB'File(NCO#"Directory","nonsingular_solutions","member_points",CopyB'File=>true);
	    moveB'File(NCO#"Directory","nonsingular_solutions",criticalPointName,CopyB'File=>true));	    
	    );
-- (FUNCTIONS 3) Functions for membership test and returning incidence matrix (IM).
    ttOne:=1;
    ttThree:=3;    
    nameFileFunction:=(stage,case,indexCase,hypersurface,theTrackType)->("input_first_MT_"|case|"_"|indexCase|"_"|theTrackType);
    writeIsMembershipFunction:=(stage,case,indexCase,hypersurface,theTrackType)->(
	nif:=nameFileFunction(stage,case,indexCase,hypersurface,theTrackType);
    	if stage===stageOne then BC:={"TData"=>0,"TWeight"=>0};
    	if stage===stageTwo then BC={"TData"=>1,"TWeight"=>1};
    	if not member(stage,{1,2}) then error"stage is in {1,2}";
    	makeB'InputFile(NCO#"Directory",
    	    NameB'InputFile=>nif,
	    AffVariableGroup=>flatten flatten {bLagrangeVars,bModelVars},
    	    B'Configs=>bConfiguration|{"TrackType"=>theTrackType},
	    B'Polynomials=>{hypersurface},
	    B'Constants=>jacZero|BC,
--	    ParameterGroup=>PG,
    	    B'Functions=>BF
	    ));
--    isMembershipFunction(stageOne,"TT",0,"x1*x2-x3*x4")--Test!
    isMembershipFunction:=(stage,case,indexCase,hypersurface)->(
	--Pos dim solve TrackType=>1
	writeIsMembershipFunction(stage,case,indexCase,hypersurface,ttOne);
	nif:=nameFileFunction(stage,case,indexCase,hypersurface,ttOne);
	runBertini(NCO#"Directory",NameB'InputFile=>nif);
    	moveB'File(NCO#"Directory","bertini_session.log","bertini_session_"|nif|".log",CopyB'File => false);
--    	print nif;
	--MT TrackType=>3
	writeIsMembershipFunction(stage,case,indexCase,hypersurface,ttThree);
	nif=nameFileFunction(stage,case,indexCase,hypersurface,ttThree);
	runBertini(NCO#"Directory",NameB'InputFile=>nif);
    	moveB'File(NCO#"Directory","bertini_session.log","bertini_session_"|nif|".log",CopyB'File => false);
       	outIM:=importIncidenceMatrix(NCO#"Directory");
    	print("Membership tests",nif);	
	print outIM;
	return outIM	)  ;  
-- (FUNCTIONS 4) Functions for filtering based off of incidence matrix
    filterSolutionFunction:=(nsf,kp,ns,numCoords)->(     
--    	print("RUN FILTER",kp=>numCoords);    
    	firstLine := true;
    	countSol  := 0;
    	countLine := 0;
    	groupSize := 1+numCoords;
    	isSelected:= null;
    	sf:=openOut(NCO#"Directory"|"/"|nsf);
    	scanLineSolutionFunction := (ell)->(
      	    if firstLine 
      	    then (firstLine=false; sf<< toString(#kp)<<endl)
      	    else if countSol < ns
      	    then (
    	  	if countLine==0 then isSelected=member(countSol,kp);
	  	countLine=countLine+1;
    	  	if isSelected then sf <<ell<<endl;
      	  	if countLine==groupSize 
      	  	then (
    	    	    print(countSol=>isSelected);    	    	
	      	    --print (countLine,groupSize,"grp");
	      	    countLine=0; 
	      	    countSol=countSol+1;
	      	    )));
      scanLines(scanLineSolutionFunction,(NCO#"Directory")|"/"|"member_points");      
      close sf;
      return (nsf));
  --filterSolutionFunction("T1",{1,2,3,4,5,6,7},8)
--      saturateFunction=positionFunction=positionFilterFunction;
    positionFilterFunction:=(stage,case,indexCase,hypersurface,bin)->(--(stage,case,indexCase,hypersurface)
--	isMembershipFunction(stage,case,indexCase,hypersurface);      
--    	(kp,ns):=positionMembershipFunction(stage,case,indexCase,hypersurface);
    	if bin==="typeA" 
	then isOffHypersurface:=(m->(m==={}))
    	else if bin==="typeB" 
	then isOffHypersurface=(m->(m=!={}))
	else error"last argument is typeA or typeB";
	imMT:=isMembershipFunction(stage,case,indexCase,hypersurface);
    	kp:={};
    	scan(#imMT,i->if isOffHypersurface(imMT_i) then kp=kp|{i});
    	ns:= #imMT;
	(nsf,nc):=("filterFile",#flatten {bLagrangeVars,bModelVars});
    	print("Filter",kp,"num kp",#kp,"num sols",ns,"num coordinates",nc,bin);
	filterSolutionFunction("filterFile",kp,ns,nc);
    	moveB'File(NCO#"Directory","filterFile","member_points",CopyB'File=>true);
	return #kp
	);
    stageEDDegBound:=new MutableList from {"GEDvUED",null,null};   
-- (FUNCTIONS 5) Functions to iterate filtering
    runSaturateUnionFunction:=(polyList,stage)->(
    	print("Remove critical points from member_points where any of these polynomials vanish",polyList);
    	(case,bin):=("SaturateH","typeA");
    	scan(#polyList,i->(
		stageEDDegBound#stage=positionFilterFunction(stageOne,case,i,polyList_i,bin);
	    	print(peek stageEDDegBound,"Saturate by polynomial"=>polyList_i)));	 
    	print(peek stageEDDegBound));	        
-- (FUNCTIONS 6) Functions to restrict to the variety 
    runRestrictIntersectionFunction:=(polyList,stage)->(
    	print("Only keeping critical points from member_points where every one of these polynomials vanish",polyList);
    	(case,bin):=("IntersectF","typeB");
    	scan(#polyList,i->(
		stageEDDegBound#stage=positionFilterFunction(stageOne,case,i,polyList_i,bin);
		print(peek stageEDDegBound,"Vanish polynomial"=>polyList_i)));	 
    	print(peek stageEDDegBound));	        
-- (Function 7) 
    runComputationStage:=(stage,offPolyList,onPolyList)->(
	if stage==stageOne then
	runSolveInputFunction(stageOne,"input_first_solve") else 
	runSolveInputFunction(stageTwo,"input_second_solve");
--	print("offPolyList",offPolyList);
	if stage===stageOne or NCO#"OutputType"=!="TestHomotopyConjectureGEDvUED"
	then runSaturateUnionFunction(offPolyList,stage);
--    	print("WIN","SATURATE");
--    	moveB'File(NCO#"Directory","member_points","filterFile",CopyB'File=>true);
--	print("onPolyList",onPolyList);
	runRestrictIntersectionFunction(onPolyList,stage);
--	print("WIN","RESTRICT");
    	if stage===stageTwo and NCO#"FinerRestriction"=!={} 
	then(
	    print("In stage 2, keep the critical points where each of these polynomials vanish ",NCO#"FinerRestriction");
	    	runRestrictIntersectionFunction(NCO#"FinerRestriction",stage));
	print("We have completed stage ",stage)	);    
    offPolyList:={HX,"L0"}|((pairGeneralHyperplanes/(i->i#NameB'Section)));
    onPolyList :=F/(i->homogenize(sub(i,jacRing),HX));
    if isStageOne then runComputationStage(stageOne,offPolyList,onPolyList);
    if isStageTwo then runComputationStage(stageTwo,offPolyList,onPolyList);
    if isStageTwo then return stageEDDegBound#2 else if isStageOne then return stageEDDegBound#1
      )

-*
vanishTally=method() 
vanishTally(NumericalComputationOptions,Ideal,RR):=(NCO,Z,setTolerance)->(
    limitPoints:=importMainDataFile(NCO#"Directory",NameMainDataFile=>"stageTwo_main_data");
    (F,G):=(NCO#"Model",NCO#"WitnessModel");    
    S:=CC[gens ring first F];
    return tally apply(#limitPoints,s->(	    
	p:=limitPoints#s;
	X:=drop(drop(p#Coordinates,#G+1),-1);
	--print X;
	xSub:=apply(gens S,X,(i,j)->i=>j);
	if 1e-8>norm sub(sub(gens Z,S),xSub) then {p#PathNumber}|p#PathsWithSameEndpoint else null )
    ))
vanishTally(NumericalComputationOptions,Ideal):=(NCO,Z)->(setTolerance:=1e-8,return vanishTally(NCO,Z,setTolerance))
vanishTally(NumericalComputationOptions,List,RR):=(NCO,fegZ,setTolerance)->vanishTally(NCO,ideal fegZ,setTolerance)
vanishTally(NumericalComputationOptions,List):=(NCO,fegZ)->vanishTally(NCO,ideal fegZ)
*-


numericWeightEDDegree=method()

numericWeightEDDegree(String,Sequence,List):=(dir,P,wv)->(    
    NCO:=newNumericalComputationOptions(dir,P);
--    WV:=apply(#gens ring first first P,i->random CC);
    NCO#"StartWeight"=wv;
    ht:="Weight";
    isStageOne:=true;
    isStageTwo:=false;
    homotopyEDDegree(NCO,ht,isStageOne,isStageTwo)
    )

numericWeightEDDegree(Sequence,List):=(P,wv)->(
    dir:=temporaryFileName();    
    if not fileExists dir then mkdir dir;
    numericWeightEDDegree(dir,P,wv)    )
--numericWeightEDDegree(P,{1,2,3,4})

edTypes={"Generic","Unit"}
numericEDDegree=method()
numericEDDegree(Sequence,String):=(P,typeED)->(    
    if typeED ==="Generic" then  wv:=apply(#gens ring first first P,i->random CC)
    else if typeED==="Unit" then wv=apply(#gens ring first first P,i->1)
    else error("last argument needs to be in "|toString edTypes);    
    numericWeightEDDegree(P,wv));    


end

 