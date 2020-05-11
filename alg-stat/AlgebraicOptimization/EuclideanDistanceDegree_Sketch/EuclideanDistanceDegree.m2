
newPackage(
    "EuclideanDistanceDegree",
    Version => "1.0", 
    Date => "May 2019",
    Authors => {
   {Name => "Jose Israel Rodriguez",
       Email => "Jose@Math.wisc.edu",
       HomePage => "http://www.math.wisc.edu/~jose/"}
    },
    Headline => "Produces equations and computes ED degrees. ",
    DebuggingMode => true,
    AuxiliaryFiles => false,
    PackageImports => {"SimpleDoc","Bertini"},
    PackageExports => {"SimpleDoc","Bertini"},
  Configuration => { "RandomCoefficients"=>CC,
      "Continuation"=>Bertini },
  CacheExampleOutput => false 
)


--path=prepend("/Users/jo/Documents/GoodGit/EuclideanDistanceDegree",path)
--loadPackage("EuclideanDistanceDegree",Reload=>true)
--restart

randomCC=()->random CC
randCC=()->random CC
randomRR=()->((-1)^(random(1,2)) *random RR)
randomZZ=()->random(1,30103)
randomValue=(kk)-> if kk===CC then randomCC() else if kk===RR then randomRR() else randomZZ() 
randomVector=method(Options=>{		})
randomVector(ZZ,Thing):= o->(n,R) ->apply(n,i->randomValue(R))--list of length n of randomValue

load"./EDD_Determinantal.m2"
load"./EDD_LeftKernel.m2"
load"./EDD_Numerical.m2"


export { 
--    "vanishTally", --Needs to be document if exported
    "ReturnCriticalIdeal",
    "homotopyEDDegree",
    "symbolicWeightEDDegree",
    "determinantalUnitEuclideanDistanceDegree",
    "determinantalGenericEuclideanDistanceDegree",
    "leftKernelWeightEDDegree",
    "leftKernelUnitEDDegree",
    "leftKernelGenericEDDegree",
    "runBertiniEDDegree",
    "newNumericalComputationOptions",
    "NumericalComputationOptions",
    "numericWeightEDDegree",
    "numericEDDegree"
            }

----------------------------------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------------------


--##########################################################################--
-- INTERNAL METHODS
--##########################################################################--
parString = (aString)->("("|toString(aString)|")");
addSlash = (aString)->(
    if aString_-1===" " then error (aString|" cannot end with whitespace.");
    if aString_-1=!="/" then aString=aString|"/";
    return aString    )
makeJac = (system,unknowns)->(--it is a list of lists of partial derivatives of a polynomial
         for i in system list for j in unknowns list  diff(j,i))
checkZero=(aSol,eps)->if aSol/abs//min<eps then false else true
sortPointFunction = (aSol)->(if not (apply(aSol,i->{realPart i,imaginaryPart i}/abs//max)//min<1e-8) then true else false	    );

--beginDocumentation()
--load "./DOC_EDD.m2";
--##########################################################################--
-- DOCUMENTATION
--##########################################################################--

doc /// --EuclideanDistanceDegree  
    Key
        EuclideanDistanceDegree 
    Headline
        a package to determine Euclidean distance degrees
    Description
      Text
        This package provides several routines for determining the (generic or unit) Euclidean distance degree of an algebraic variety.
    	These routines include symbolic methods and numerical methods for determining these degrees. 
      Text
      	Using symbolic computation, this code computes the (unit) ED degree of a circle. 		 
      Example
    	R=QQ[x,y];
	F={x^2+y^2-1};
	2==determinantalUnitEuclideanDistanceDegree(F)
      Text
      	Using numeric computation, this code computes the (unit) ED degree of a circle. 		 
      Example
    	R=QQ[x,y];
	F={x^2+y^2-1};	c=1;
    	leftKernelUnitEDDegree(storeBM2Files,F)
	2==runBertiniEDDegree(storeBM2Files)
      Text
      	This package also computes generic ED degrees. The generic ED degree of X is always greater than or equal to the unit ED degree X.
      Example
    	R=QQ[x,y];
	F={x^2+y^2-1};	c=1
    	4==determinantalGenericEuclideanDistanceDegree(F)
    	leftKernelGenericEDDegree(storeBM2Files,F)
	4==runBertiniEDDegree(storeBM2Files)
      Text
      	The most general method for computing ED degrees with symbolic computation is symbolicWeightEDDegree
      Example
   	R=QQ[x,y];
	F={x^2+y^2-1};
	genericWeightVector={2,3};
	unitWeightVector={1,1};
	dataVector={5,7};
	4==symbolicWeightEDDegree(F,dataVector,genericWeightVector)
	2==symbolicWeightEDDegree(F,dataVector,unitWeightVector)		
      Text
      	When the variety is an affine cone, one is able to compute ED degrees using ED degree homotopies, i.e., a structured parameter homotopy.
	The easiest case is when the variety is a hypersurface (or more generally, a complete intersection)  
      Example
        R=QQ[x1,x2,x3,x4]
	F={det genericMatrix(R,2,2)};
    	P=(F,F)
	6==numericEDDegree(P,"Generic")
	2==numericEDDegree(P,"Unit")
      Text
      	When a V(F) is not a complete intersection we incorporate a membership test to filter out residual critical points.
	Here V(F) is an irreducible component of V(G) (a reducible variety) and #G===codim ideal F.
	These methods employ an equation by equation method called regeneration. 
      Example
        R=QQ[x1,x2,x3,x4,x5,x6]
	F=(minors(2,genericMatrix(R,3,2)))_*;
    	G=drop(F,-1);	
    	P=(F,G)
    	#G==codim ideal F;
	10==numericEDDegree(P,"Generic")
	2==numericEDDegree(P,"Unit")
      Text
      	One may also determine (Unit) ED degrees using a parameter homotopy called a Weight-ED Degree Homotopy. 
      Example
    	dir=temporaryFileName();if not fileExists dir then mkdir dir;
        R=QQ[x1,x2,x3,x4,x5,x6]
	F=(minors(2,genericMatrix(R,3,2)))_*;
    	G=drop(F,-1);	
    	#G==codim ideal F;
    	P=(F,G)
	NCO=newNumericalComputationOptions(dir,P)
    	NCO#"TargetWeight"=apply(#gens R,i->1)
	2==homotopyEDDegree(NCO,"Weight",true,true)
    	NCO#"TargetWeight"=(apply(#gens R,i->random RR))
	10==homotopyEDDegree(NCO,"Weight",false,true)
      Text
      	One may also compute crtiical points for different data using a parameter homotopy called a Data-ED Degree Homotopy. 
      Example
    	dir=temporaryFileName();if not fileExists dir then mkdir dir;
        R=QQ[x1,x2,x3,x4,x5,x6]
	F=(minors(2,genericMatrix(R,3,2)))_*;
    	G=drop(F,-1);	
    	#G==codim ideal F;
    	P=(F,G)
	NCO=newNumericalComputationOptions(dir,P)
    	NCO#"TargetData"=apply(#gens R,i->1)
	10==homotopyEDDegree(NCO,"Data",true,true)
	importSolutionsFile(NCO#"Directory",NameSolutionsFile=>"member_points")	
    	NCO#"TargetWeight"={0}|(apply(-1+#gens R,i->1))
	homotopyEDDegree(NCO,"Data",false,true)
	importSolutionsFile(NCO#"Directory",NameSolutionsFile=>"member_points")	

///;


doc ///--symbolicWeightEDDegree
 Key
   symbolicWeightEDDegree
   (symbolicWeightEDDegree,List,List,List)
   determinantalUnitEuclideanDistanceDegree
   (determinantalUnitEuclideanDistanceDegree,List)
   determinantalGenericEuclideanDistanceDegree
   (determinantalGenericEuclideanDistanceDegree,List)
   ReturnCriticalIdeal
 Headline
   a method to determine Euclidean distance degrees using symbolic computation
 Usage
   UED = determinantalUnitEuclideanDistanceDegree(F)
   GED = determinantalGenericEuclideanDistanceDegree(F)
   GED = symbolicWeightEDDegree(F,U,W)
 Inputs
   F:List
     polynomials (system need not be square)
   U:List
     a (generic) data vector 
   W:List
     a (generic) weight vector
 Outputs
   GED:ZZ
     a generic Euclidean distance degree 
   UED:ZZ
     a unit Euclidean distance degree 
   ICP:Ideal
     an ideal for the variety of critical points
 Description
   Text
     The default is to return a degree (GED or UED) but the option ReturnCriticalIdeal=>true will change the option to ICP 
   Example
     R = QQ[x,y];     
     F = {x^2+y^2-1}
     (U,W) = ({12,23},{15,331})
     UED = determinantalUnitEuclideanDistanceDegree F 
     GED = determinantalGenericEuclideanDistanceDegree F 
     ICP = symbolicWeightEDDegree(F,U,W,ReturnCriticalIdeal=>true)
 Caveat
   none
      
///;

end

doc ///--NumericalComputationOptions
 Key
   NumericalComputationOptions
   newNumericalComputationOptions
   (newNumericalComputationOptions,String,Sequence)
   homotopyEDDegree   
   (homotopyEDDegree,NumericalComputationOptions,String,Boolean,Boolean)
   numericWeightEDDegree
   (numericWeightEDDegree,String,Sequence,List)
   (numericWeightEDDegree,Sequence,List)
   numericEDDegree
   (numericEDDegree,Sequence,String)
 Headline
   a method to determine Euclidean distance degrees of projective varieties (affine cones) using numerical computation
 Usage
   GED = numericEDDegree((F,G),"Generic")
   UED = numericEDDegree((F,G),"Unit")
   NCO = newNumericalComputationOptions(dir,(F,G))
   (NCO = newNumericalComputationOptions(dir,(F,G)); GED = homotopyEDDegree(NCO, "Weight", true, false))
   (NCO = newNumericalComputationOptions(dir,(F,G)); UED = homotopyEDDegree(NCO, "Weight", true, true))
 Inputs
   F:List
     polynomials 
   G:List
     polynomials (complete intersection) such that V(F) is an irreducible component of V(G).
   dir:String
     a directory 
   NCO:NumericalComputationOptions
     a MutableHashTable to keeps track of the options and configurations for the homotopy methods
 Outputs
   GED:ZZ
     a generic Euclidean distance degree 
   UED:ZZ
     a unit Euclidean distance degree 
   NCO:NumericalComputationOptions
     a MutableHashTable to keeps track of the options and configurations for the homotopy methods
   WS:List
     a (generic) start weight vector
 Description
   Text
     The Bertini input files are written in dir and then Bertini is ran.  
   Example
     R = QQ[x,y];     
     F = G = {x^2+y^2-1}
     W1 = {1,1}
     WS = {.7,1.2}
     dir=temporaryFileName(); mkdir dir;
     GED = numericEDDegree((F,G),"Generic")
     UED = numericEDDegree((F,G),"Unit")
     NCO = newNumericalComputationOptions(dir,(F,G))
     NCO#"TargetWeight"
     GED = homotopyEDDegree(NCO, "Weight", true, false)
     UED = homotopyEDDegree(NCO, "Weight", true, true)
     GED = numericWeightEDDegree((F,G),WS)
     UED = numericWeightEDDegree((F,G),W1)
 Caveat
   none
      
///;


doc ///--leftKernel
 Key
   leftKernelWeightEDDegree
   (leftKernelWeightEDDegree,String,List,List)
   leftKernelUnitEDDegree
   (leftKernelUnitEDDegree,String,List)
   leftKernelGenericEDDegree
   (leftKernelGenericEDDegree,String,List)
   runBertiniEDDegree
   (runBertiniEDDegree,String)
 Headline
   a method to determine Euclidean distance degrees of affine varieties that are complete intersections using numerical computation
 Usage
   GED = runBertiniEDDegree leftKernelWeightEDDegree(dir,c,F,W)
   GED = runBertiniEDDegree leftKernelGenericEDDegree(dir,c,F)
   UED = runBertiniEDDegree leftKernelUnitEDDegree(dir,c,F)
 Inputs
   F:List
     polynomials (system need not be square)
   dir:String
     a directory 
   c:ZZ
     a codimension
   W:List
     a (generic) weight vector
 Outputs
   GED:ZZ
     a generic Euclidean distance degree 
   UED:ZZ
     a unit Euclidean distance degree 
 Description
   Text
     The Bertini input files are written in dir and then Bertini is ran.  
   Example
     R = QQ[x,y];     
     F = {x^2+y^2-1}
     W = {.15,.331}
     dir=temporaryFileName(); mkdir dir;
     GED = runBertiniEDDegree leftKernelWeightEDDegree(dir,F,W)
     GED = runBertiniEDDegree leftKernelGenericEDDegree(dir,F)
     UED = runBertiniEDDegree leftKernelUnitEDDegree(dir,F)
 Caveat
   none
      
///;



--##########################################################################--
-- END DOCUMENTATION
--##########################################################################--


TEST///
--load concatenate(MultiprojectiveWitnessSets#"source directory","./AEO/TST/Example1.tst.m2")
///


end
restart
loadPackage"EuclideanDistanceDegree"
installPackage"EuclideanDistanceDegree"
check "EuclideanDistanceDegree"
(mRow,nCol)=(3,3)
R=QQ[x_(1,1)..x_(mRow,nCol)]
M=transpose genericMatrix(R,mRow,nCol)

 determinantalUnitEuclideanDistanceDegree flatten entries gens minors(2,M)

win1= determinantalGenericEuclideanDistanceDegree flatten entries gens minors(3,M)

win2= determinantalGenericEuclideanDistanceDegree flatten entries gens minors(2,M)


R=QQ[x,y,z]
F={x^2*y*z + x^2*z^2 - y^3*z - y^3 }
determinantalUnitEuclideanDistanceDegree(F)--15
primaryDecomposition ideal singularLocus ideal F
CV=conormalVariety(ideal F);




R=QQ[x,y,z]
F={x^2*y*z + x^2*z^2 - y^3*z - y^3 }
determinantalUnitEuclideanDistanceDegree(F)--15
primaryDecomposition ideal singularLocus ideal F
CV=conormalVariety(ideal F);





eliminate(drop(gens ring CV,-3),CV)


R=QQ[x0,x1,x2,x3]
I=ideal sum apply(gens R,i->i^3);


R=QQ[x,y,z]
F={x^2*y*z + x^2*z^2 - y^3*z - y^3 }
determinantalUnitEuclideanDistanceDegree(F)--15
primaryDecomposition ideal singularLocus ideal F
CV=conormalVariety(ideal F);

R=QQ[y,z]
gens coefficientRing R



---ED degree Equation 3.6
R=QQ[s,t]
sectionalEDdegree=(m,n,d1,d2,j)->(    
    L:= 4*(1+t)^m*(1+s)^n*(t+s)^j*sum(apply(d1+1,i->(-2*t)^i))*sum(apply(d2+1,i->(-2*s)^i));
    L=diff(t^(m-2)*s^(n-2),L);
    L=sub(L,{t=>0,s=>0});
    L=1/((m-2)!)*1/((n-2)!)*L	  
	  )

(m,n,d1,d2,jjj)=(5,5,20,20,2)
sectionalEDdegree(m,n,d1,d2,jjj)



R=QQ[x,y,z,w]
F={det genericMatrix(R,2,2) -1}
determinantalUnitEuclideanDistanceDegree(F)
leftKernelGenericEDDegree(storeBM2Files,1,F)
runBertiniEDDegree(storeBM2Files)

leftKernelUnitEDDegree(storeBM2Files,1,F)
runBertiniEDDegree(storeBM2Files)
primaryDecomposition ideal singularLocus ideal F
CV=conormalVariety(ideal F);


---
nSize=4
R=QQ[a_(1,1)..a_(nSize,nSize)]
F={det genericMatrix(R,nSize,nSize) -1}
determinantalUnitEuclideanDistanceDegree(F)
nSize/2*2^nSize
determinantalGenericEuclideanDistanceDegree(F)

{8,120}
leftKernelGenericEDDegree(storeBM2Files,1,F)
runBertiniEDDegree(storeBM2Files)



----
restart
loadPackage"EuclideanDistanceDegree"
R=QQ[x,y,z,w]
F={det genericMatrix(R,2,2),y-z}
determinantalUnitEuclideanDistanceDegree(F)
determinantalGenericEuclideanDistanceDegree(F)
primaryDecomposition ideal singularLocus ideal F
codim first decompose ideal singularLocus (ideal F+ideal(gens R/(i->i^2)//sum))
---

R=QQ[x,y,z,w]
F={x^2*w+y^2*w-z^3}
F={x^2*w+y^2*w-z^2*x}
F={(x^2+y^2+z^2+w^2)*x-w^3}--codim 1 and irreducible (GED,UED)=(15,5)

F={(x^2+y^2+z^2+w^2)*x-y*w^2}--codim 1 and irreducible (GED,UED)=(17,9)
F={(x^2+y^2+z^2+w^2)^2-z^3*w}--codim 1 and irreducible (GED,UED)=(16,8)--This has the multiplicity Max was looking for.
F={(x^2+y^2+z^2+w^2)-2*y^2}--codim 1 and irreducible (GED,UED)=(6,4)

--bertiniPosDimSolve F--used this to check irreducibility over CC
determinantalGenericEuclideanDistanceDegree(F)
determinantalUnitEuclideanDistanceDegree(F)
leftKernelGenericEDDegree(theDir,1,F)
runBertiniEDDegree(theDir)
leftKernelUnitEDDegree(theDir,1,F)
runBertiniEDDegree(theDir)

fZ=first primaryDecomposition ideal singularLocus ideal F
--2*2

pDecZ=primaryDecomposition ideal singularLocus (ideal F+ideal(gens R/(i->i^2)//sum))

codim\ pDecZ
degree\ pDecZ
degree\radical \pDecZ
(pDecZ//first//radical)_*//determinantalGenericEuclideanDistanceDegree
Z=(pDecZ//first//radical)_*

fZ
(ideal Z+fZ)//primaryDecomposition

leftKernelGenericEDDegree(theDir,2,Z)
runBertiniEDDegree(theDir)

----
U=((ideal F)*(ideal(gens R/(i->i^2)//sum)))
pDecZU=primaryDecomposition ideal singularLocus U
pDecZU/radical//first

primaryDecomposition(ideal F+radical first primaryDecomposition first pDecZU)




----LIMIT POINT TESTS

      Text
      	A current project (2019) is quantify the difference between the GED and UED in terms of topological invariants.
	We gain understanding by determining the limit of each endpoint of the weight-homotopy. 
      Example
    	dir=temporaryFileName();if not fileExists dir then mkdir dir;
    	zdir=temporaryFileName();if not fileExists zdir then mkdir zdir;
        R=QQ[x1,x2,x3,x4]
	F=(minors(2,genericMatrix(R,2,2)))_*;
    	P=(F,F)
    	Q=gens R/(i->i^2)//sum
	Z= radical ideal singularLocus (ideal(F)+ideal Q)
    	codimZ=codim\decompose radical Z
    	max codimZ==min codimZ--pure dimensional
    	GZ=ideal {};scan(Z_*,f->if numgens GZ+1==codim (GZ+ideal(f))then GZ=ideal(f)+GZ)
    	codim GZ==first codimZ
--6=2+4
    	6==determinantalGenericEuclideanDistanceDegree F
    	2==determinantalUnitEuclideanDistanceDegree F
    	4==determinantalGenericEuclideanDistanceDegree flatten entries gens Z       
--
	NCO=newNumericalComputationOptions(dir,P)
    	2==homotopyEDDegree(NCO,"Weight",true,true)
    	NCO#"OutputType"="TestHomotopyConjectureGEDvUED"
	6==homotopyEDDegree(NCO,"Weight",true,true)
    	NCO#"OutputType"="TestHomotopyConjectureGEDvUED"
    	NCO#"FinerRestriction"=flatten entries gens GZ
	4==homotopyEDDegree(NCO,"Weight",true,true)
	readFile(NCO#"Directory","member_points",10000)
	decompose Z
      Text
      	This test is for a variety where Z has multiplicity.
      Example
        R=QQ[x,y,z,w]
	F=G={(x^2+y^2+z^2+w^2)*x-w^3};
    	P=(F,F)
    	Q=gens R/(i->i^2)//sum
	singF=radical ideal singularLocus ideal F
	mZ=  ideal singularLocus (ideal(F)+ideal Q)
    	Z=radical mZ
    	print ("Multiplicity of Z"=>degree mZ/degree Z)
--15=4+5+2*4=UED(X)+GED(X_sing)+2*GED(Z)
    	15==determinantalGenericEuclideanDistanceDegree F
    	5==determinantalUnitEuclideanDistanceDegree F
    	4==determinantalGenericEuclideanDistanceDegree flatten entries gens Z;       
--
    	dir=temporaryFileName();if not fileExists dir then mkdir dir;
	NCO=newNumericalComputationOptions(dir,P)
    	5==homotopyEDDegree(NCO,"Weight",true,true)
	--Now we investigate where the other 15-5 solutions went. 
	readFile(NCO#"Directory","stageTwo_log",10000)
    	--The stage_Two_log file gives us some insights. 
	--The solutions partition by nonsing vs sing as {5}+{6}=11
	--The solutions partition by multiplicity as (1)*7+(2)*4=15
    	--Conclusion: {5}+{(1)*2+(2)*4}={15}
--    	readFile(NCO#"Directory","stageTwo_main_data",100000)    	
    	limitPoints=importMainDataFile(NCO#"Directory",NameMainDataFile=>"stageTwo_main_data");
    	#limitPoints==11
    	peek limitPoints#2	
    	vanishTally(NCO,singF)--two points
--    	2==#delete(null,keys vanishTally(NCO,singF))
    	vanishTally(NCO,Z)--six points
--    	6==#delete(null,keys vanishTally(NCO,Z))
      Text
      	This tests a variety with a positive dimensional Z. 
      Example
        R=QQ[x,y,z,w]
    	Q=gens R/(i->i^2)//sum
	G=F={(x^2+y^2+z^2+w^2)^2-z^3*w}
    	P=(F,G)
	mZ=  ideal singularLocus (ideal(F)+ideal Q)
	Z= radical mZ	
    	(degree mZ=>degree Z)	
	singX=radical ideal singularLocus ideal F
--16=GED(X)=UED(X)+2*GED(Z)
    	16==determinantalGenericEuclideanDistanceDegree F
    	8==determinantalUnitEuclideanDistanceDegree F
    	4==determinantalGenericEuclideanDistanceDegree flatten entries gens Z    
--
    	dir=temporaryFileName();if not fileExists dir then mkdir dir;
	NCO=newNumericalComputationOptions(dir,P)
    	8==homotopyEDDegree(NCO,"Weight",true,true)
	--Now we investigate where the other 16-8 solutions went. 
	readFile(NCO#"Directory","stageTwo_log",10000)
    	---We see that there were failures so we rerun with stageOne set to false
    	8==homotopyEDDegree(NCO,"Weight",false,true)
	readFile(NCO#"Directory","stageTwo_log",10000)
    	--The stage_Two_log file gives us some insights. 
	--The solutions partition by nonsing vs sing as {8}+{4}=12
	--The solutions partition by multiplicity as (1)*10+(2)*2=14
    	--We are short two failures. 
    	--Conclusion: {8}+{(1)*2+(2)*2}+{2}=={16}
--    	readFile(NCO#"Directory","stageTwo_main_data",100000)    	
    	limitPoints=importMainDataFile(NCO#"Directory",NameMainDataFile=>"stageTwo_main_data");
    	#limitPoints==13
    	peek limitPoints#2	
    	vanishTally(NCO,Z)--2+2*2
    	vanishTally(NCO,singX)--2+2*2
	2==#delete(null,keys vanishTally(NCO,singF))
    	vanishTally(NCO,Z)--six points
--    	6==#delete(null,keys vanishTally(NCO,Z))
    	    	
		
		
---		
		
		-*
installPackage"EuclideanDistanceDegree"
check EuclideanDistanceDegree

restart
printingPrecision=100
loadPackage("EuclideanDistanceDegree",Reload=>true)
check EuclideanDistanceDegree
help EuclideanDistanceDegree
R=QQ[x1,x2,x3,x4]
M=matrix{{x1,x2,x3},{x2,x3,x4}}
F=(minors(2,M))_*
G=drop(F,-1)--7
L={}
P=(F,G,L)
sf=temporaryFileName();mkdir sf
NCO=newNumericalComputationOptions(sf,P)
--determinantalUnitEuclideanDistanceDegree(F)
--determinantalGenericEuclideanDistanceDegree(F)
homotopyEDDegree(NCO,"Weight",true,true)
*-


--defaultFixValues={"StartData","StartWeight","StartSubmodel","JacobianStartSubmodel"}
-*
restart
printingPrecision=100
loadPackage("EuclideanDistanceDegree",Reload=>true)
R=QQ[x,y,z,w]
F=G={det genericMatrix(R,2,2)}
L={}
P=(F,G,L)
sf=temporaryFileName();mkdir sf
NCO=newNumericalComputationOptions(sf,P)
homotopyEDDegree(NCO,"Weight",true,true)--2
*-

-*
restart
printingPrecision=100
loadPackage("EuclideanDistanceDegree",Reload=>true)
R=QQ[x,y,z,w]

F=G={x^3-y*w+z+1,random({1},R)}
L={}
P=(F,G,L)
sf=temporaryFileName();mkdir sf
NCO=newNumericalComputationOptions(sf,P)
homotopyEDDegree(NCO,"Weight",true,true)
determinantalUnitEuclideanDistanceDegree(F)
*-

-*
restart
printingPrecision=100
loadPackage("EuclideanDistanceDegree",Reload=>true)
R=QQ[x,y,z,w]
F=G={x^3-y*w+z+1,x*y-z*w}
L={}
P=(F,G,L)
sf=temporaryFileName();mkdir sf
NCO=newNumericalComputationOptions(sf,P)
determinantalUnitEuclideanDistanceDegree(F)
determinantalGenericEuclideanDistanceDegree(F)
homotopyEDDegree(NCO,"Weight",true,true)
*-

-*
restart
printingPrecision=100
loadPackage("EuclideanDistanceDegree",Reload=>true)
R=QQ[x,y,z,w]
F=G={random({1},R),random({1},R)}
L={}
P=(F,G,L)
sf=temporaryFileName();mkdir sf
NCO=newNumericalComputationOptions(sf,P)
determinantalUnitEuclideanDistanceDegree(F)
determinantalGenericEuclideanDistanceDegree(F)
homotopyEDDegree(NCO,"Weight",true,true)
*-


-*
restart
printingPrecision=100
loadPackage("EuclideanDistanceDegree",Reload=>true)
R=QQ[x,y,z,w]
F=G={x+y,z-w}
L={}
P=(F,G,L)
sf=temporaryFileName();mkdir sf
NCO=newNumericalComputationOptions(sf,P)
determinantalUnitEuclideanDistanceDegree(F)
determinantalGenericEuclideanDistanceDegree(F)
homotopyEDDegree(NCO,"Weight",true,true)
*-



-*
restart
printingPrecision=100
loadPackage("EuclideanDistanceDegree",Reload=>true)
R=QQ[x1,x2,x3,x4,x5,x6,x7,x8,x9]
M=genericMatrix(R,3,3)
F=(minors(2,M))_*
G={F_0,F_1,F_4,F_5}+2*{F_1,F_2,F_3,F_7}-3*{F_2,F_1,F_0,F_5}+2*{F_2,F_1,F_6,F_8}
G={F_0,F_1,F_4,F_5}
4==codim first decompose ideal G
#G
L={}
P=(F,G,L)
sf=temporaryFileName();mkdir sf
NCO=newNumericalComputationOptions(sf,P)
--determinantalUnitEuclideanDistanceDegree(F)
--determinantalGenericEuclideanDistanceDegree(F)
homotopyEDDegree(NCO,"Weight",true,true)
*-



-*
R=QQ[x1,x2,x3,x4]
M=matrix{{x1,x2,x3},{x2,x3,x4}}
F=(minors(2,M))_*
G=drop(F,-1)
codim\decompose ideal G

S=QQ[gens R|{l0,l1,l2,HX}]
CM=matrix{apply(gens R,i->sub(i,S)-HX*random(1,1000))}||sub(matrix makeJac(G,gens R),S)
critG=ideal(matrix{{l0,l1,l2}}*CM)+sub(ideal(G),S)
critF=ideal(matrix{{l0,l1,l2}}*CM)+sub(ideal(F),S)
netList decompose critG
netList apply(decompose critG,i->ideal mingens (sub(ideal F,S)+saturate(i,HX*l0)))

help saturate
decWIN=decompose(minors(3,CM)+sub(ideal G,S))
decWIN/degree
decWIN/codim

decompose (decWIN_1+sub(ideal(F),S))
oo/codim
topRow=matrix{1431-x1}
*-


-*
loadPackage("EuclideanDistanceDegree",Reload=>true)
    	dir=storeBM2Files
       R=QQ[x1,x2,x3,x4,x5,x6]
       F=(minors(2,genericMatrix(R,3,2)))_*;
       G=drop(F,-1);
       #G==codim ideal F;
       P=(F,G)
       NCO=newNumericalComputationOptions(dir,P)
       NCO#"TargetWeight"=apply(#gens R,i->1)
       2==homotopyEDDegree(NCO,"Weight",true,true)
       vanishTally(NCO,F)
*-

--numericEDDegree(P,"Generic")
--numericEDDegree(P,"Unit")


--restart
--loadPackage"Bertini"
-*
parameterizeConormalMatrixRankConstraint=(r,m,n,L,kk)->(
    matrixVars:=(a,b,s)->for i to a-1 list for j to b-1 list (s|i|"v"|j);    
    getMatrix=(aRing,a,b)->transpose genericMatrix(aRing,b,a);
    getId=(m,v)->diagonalMatrix apply(m,i->v);
--
    ringPrimalSpan:=kk[(m-r,r,"PS")//matrixVars//flatten|{"PSH"}];
    ringPrimalCenter:=kk[(r,r,"PC")//matrixVars//flatten|{"PCH"}];
    ringDualSpan:=kk[(n-r,r,"DS")//matrixVars//flatten|{"DSH"}];
    ringDualCenter:=kk[(m-r,n-r,"DC")//matrixVars//flatten|{"DCH"}];
    ringData:=kk[flatten matrixVars(m,n,"u")];
    ringWeight:=kk[flatten matrixVars(m,n,"w")];
    allRings:={ringPrimalSpan,ringPrimalCenter,ringDualSpan,ringDualCenter,ringData,ringWeight};
    sizeMatrix={(m-r,r),(r,r),(n-r,r), (m-r,n-r), (m,n),  (m,n)}; 
    allMatrices= apply(allRings,sizeMatrix,(i,j)->getMatrix(i,j_0,j_1));
    print allMatrices; 
    lagRing=kk[apply(#L+1,i->"lag"|i)];
    bigRing=ringData**ringWeight**lagRing;
    scan(reverse drop(allRings,-2),i->bigRing=i**bigRing);
    allHomogenizers= apply(allRings,i->last gens i);
    print allHomogenizers;
    (hps,hpc,hds,hdc,hu,hw)= (allHomogenizers/(i->sub(i,bigRing)))//toSequence;
    print(hps,hpc,hds,hdc,hu,hw);
    U=sub(transpose genericMatrix(ringData,n,m),bigRing);
    print U;
    W=transpose sub(genericMatrix(ringWeight,n,m),bigRing);
    print W;
    print 2;
    mp0=sub(getId(last sizeMatrix_0,allHomogenizers_0)||allMatrices_0,bigRing);
    print 3;
    mp1=sub(allMatrices_1,bigRing);
    print W;
    print 4;
    mp2=sub(getId(last sizeMatrix_0,allHomogenizers_2)|transpose allMatrices_2,bigRing);
    print (mp0,mp1,mp2);
    md0=sub((transpose allMatrices_0)||getId(first sizeMatrix_3,-allHomogenizers_0),bigRing);
    md1=sub(allMatrices_3,bigRing);
    print md1;    
    md2=transpose sub(transpose allMatrices_2||getId(last sizeMatrix_3,-allHomogenizers_2),bigRing);
    print md2;
    print (md0,md1,md2);
    P=hdc*(product\\{mp0,mp1,mp2});
    print P;
    Q=hpc*(product\\{md0,md1,md2});
    print Q;
    scan(#L,i->Q=Q+hpc*hps*hds*sub((gens lagRing)_(i+1),bigRing )*sub(L_i,bigRing));
    linearSpace:=apply(#L,i->makeB'Section(flatten entries P));    
    print linearSpace;
    dataSlices={};
--    (hps,hpc,hds,hdc,hu,hw)
    scan(m,i->scan(n,
	    j->dataSlices=dataSlices|{
		makeB'Section({P_(i,j),-Q_(i,j),hpc*hdc*hps*hds*U_(i,j)},
		    B'NumberCoefficients=>{1,W_(i,j),-1})})
    ); --(x-u=w y) (x-u)
--    return((mp0,mp1,mp2),(md0,md1,md2),dataSlices,linearSpace)
    dir=temporaryFileName();
    print dir;
    if not fileExists dir then mkdir dir;
--    HVG={gens ringPrimalSpan, gens ringPrimalCenter, 
--	gens ringDualSpan, (gens ringDualCenter)|drop(gens lagRing,1)};    
    HVG=flatten{drop(gens ringPrimalSpan,-1), drop(gens ringPrimalCenter,-1), 
	drop(gens ringDualSpan,-1), (gens ringDualCenter)|drop(gens lagRing,1)};    
    makeB'InputFile(dir,
    	HomVariableGroup=>HVG,
    	B'Polynomials=>linearSpace|dataSlices,
    	B'Functions=>{PSH=>DCH,PCH=>DCH,DSH=>DCH},
    	B'Configs=>{"UseRegeneration"=>1},
    	RandomComplex=>(flatten entries U),
	B'Constants=>apply(flatten entries W,i->i=>1 )	
	);
    return dir
    )
-*

-*
rm=()->matrix for i to 5-1 list for j to 5-1 list random CC
rm()
dir =parameterizeConormalMatrixRankConstraint(2,5,5,{rm(),rm(),rm()},CC)        
runBertini(dir)
R=QQ[p1,p2,p3,p4]

pm=genericMatrix(R,2,2)
l=p1-p2
diff(pm,l)
*-

-*
GEd(X cap L^s)-UED(X cap L^2)=GED(Z cap L^s)
where Z=sing(X cap isoQ)
R=QQ[x1,x2,x3,x4]
Q=ideal sum (gens R/(i->i^2))
X=minors(2,genericMatrix(R,2,2))
decompose ideal singularLocus(Q+X)--4 points

loadPackage"Bertini"
R=QQ[x1,x2,x3,x4,x5,x6,x7,x8,x9]
Q=ideal sum (gens R/(i->i^2))
X=minors(2,genericMatrix(R,3,3))
X=minors(2,genericMatrix(R,2,4))--2 components of degree 2 in dim3
--bertiniPosDimSolve flatten entries gens ideal singularLocus(Q+X)
Z=flatten entries gens radical ideal singularLocus(Q+X)
bertiniPosDimSolve Z--This has two components of degree 2. 
printGens  
ideal Z==radical ideal Z
conjecture--
loadPackage"Bertini"
(r,m,n)=(1,2,4)

R=QQ[apply(m*n,i->"x"|i)]**QQ[apply((m-r)*(n-r),i->"y"|i)];
Q=basis({1,0})//entries//flatten/(i->i^2)//sum//ideal
X=genericMatrix(R,m,n)


bertiniPosDimSolve flatten entries gens ideal singularLocus(Q+X)


*-



-*
experimentDualityDifference=method()
dualVariety=(F,codF)->(
    R1:=ring first F;
    kk:=coefficientRing R1;
    R2:=kk[apply(#gens R1,i->"y"|i)];
    R:=R1**R2;
    M:=sub(matrix {gens R2},R)||sub(matrix makeJac(F,gens R1),R);
    win:=sub(ideal(F),R)+minors(codF+1,M);        
    E:=sub(eliminate(flatten entries basis({1,0},R),first decompose win),R2);
    print"computed dual variety";
    return E
    )
experimentDualityDifference(List,ZZ,ZZ):=(G,s,codF)->(
    R1:=ring first G;
    HS:=apply(s,i->random({1},R1));
    F:=G|HS;    
    adeg:=determinantalGenericEuclideanDistanceDegree F;
    print("generic X cap Hs",adeg);
    bdeg:=determinantalUnitEuclideanDistanceDegree F;
    print("unit X cap Hs",bdeg);
    R2:=QQ[apply(#gens R1,i->"y"|i)];
    dF:=flatten entries gens dualVariety(F,codF+s);
    cdeg:=determinantalGenericEuclideanDistanceDegree dF;
    print("generic X^* cap Hs",cdeg);
    ddeg:=determinantalUnitEuclideanDistanceDegree dF;
    print("unit X* cap Hs",ddeg);
    print(adeg,bdeg,cdeg,ddeg);
    adeg-bdeg==cdeg-ddeg )
*-


-*
restart
path=prepend("/Users/jo/Documents/GoodGit/EuclideanDistanceDegree",path)
loadPackage"EuclideanDistanceDegree"
unitEu
experimentDualityDifference
R=QQ[x0,x1,x2,x3,x4,x5,x6]
F={sum apply(gens R,i->i*i^2)}
IQ=(L)->sum  apply(L,i->i^2)
F={x0+x1,x2-x3,IQ({x1,x2,x3,x4,x5,x6})}
(s,codF)=(1,#F)
experimentDualityDifference(F,s,codF)

R=QQ[x0,x1,x2,x3,x4,x5,x6]
F={sum apply(gens R,i->i*i^2)}
IQ=(L)->sum  apply(L,i->i^2)
F={x0+x1,x2-x3,IQ {x1,x2,x3}, IQ{x2,x4,x5}}
(s,codF)=(2,#F)
experimentDualityDifference(F,s,codF)

*-



-*
restart
loadPackage"EuclideanDistanceDegree"
R=QQ[x,y,z,w]
--Calyx
F={x^2+y^2*z^3-z^4}/(i->homogenize(i,w))
determinantalUnitEuclideanDistanceDegree F
determinantalGenericEuclideanDistanceDegree F
experimentDualityDifference(F,1,1)

determinantalUnitEuclideanDistanceDegree(F)--21
primaryDecomposition ideal singularLocus ideal F

--Calypso
F={x^2+y^2*z-z^2}/(i->homogenize(i,w))
decompose radical ideal singularLocus ideal F
determinantalUnitEuclideanDistanceDegree F
determinantalGenericEuclideanDistanceDegree F

experimentDualityDifference(F,1,1)

determinantalUnitEuclideanDistanceDegree(F)--10
primaryDecomposition ideal singularLocus ideal F

--Crixxi
F={(y^2+z^2-1)^2 +(x^2+y^2-1)^3}/(i->homogenize(i,w))
experimentDualityDifference(F,1,1)
decompose radical ideal singularLocus ideal F
determinantalUnitEuclideanDistanceDegree F
determinantalGenericEuclideanDistanceDegree F


determinantalUnitEuclideanDistanceDegree(F)--22
primaryDecomposition ideal singularLocus ideal F

--Cube
R=QQ[x,y,z]
F={x^6+y^6+z^6-1}/(i->homogenize(i,w))
experimentDualityDifference(F,1,1)

determinantalUnitEuclideanDistanceDegree(F)--180
primaryDecomposition ideal singularLocus ideal F

--Geisha
F={x^2*y*z + x^2*z^2 - y^3*z - y^3 }/(i->homogenize(i,w))
experimentDualityDifference(F,1,1)

determinantalUnitEuclideanDistanceDegree(F)--15
primaryDecomposition ideal singularLocus ideal F

--Helix
F={6*x^2-2*x^4-y^2*z^2}/(i->homogenize(i,w))
experimentDualityDifference(F,1,1)
determinantalUnitEuclideanDistanceDegree(F)--20
primaryDecomposition ideal singularLocus ideal F



--Himmel und Hölle --RECUCIBLE
F={x^2-y^2*z^2}/(i->homogenize(i,w))
experimentDualityDifference(F,1,1)
determinantalUnitEuclideanDistanceDegree(F)--10
primaryDecomposition ideal singularLocus ideal F

--Kolibri
F={x^3 + x^2*z^2 - y^2}/(i->homogenize(i,w))
experimentDualityDifference(F,1,1)
determinantalUnitEuclideanDistanceDegree(F)--15
primaryDecomposition ideal singularLocus ideal F




*-





-*
peek first pairWeight
peek first pairData
    stage=stageTwo;
    if stage>=stageOne then (
    	writeSolveInputFile(stageOne); 
    	runBertini(NCO#"Directory",NameB'InputFile=>);
    	readFile(NCO#"Directory");
	moveB'File(NCO#"Directory","nonsingular_solutions","stageOne_solutions",CopyB'File=>true);
	moveB'File(NCO#"Directory","nonsingular_solutions","start",CopyB'File=>true);
	moveB'File(NCO#"Directory","nonsingular_solutions","member_points",CopyB'File=>true));
    readFile(NCO#"Directory");
    if stage==stageTwo then(
    	writeSolveInputFile(stageTwo) 	;
    	writeParameterFile(NCO#"Directory",{0},NameParameterFile=>"start_parameters");
    	writeParameterFile(NCO#"Directory",{1},NameParameterFile=>"final_parameters");
    	runBertini(NCO#"Directory",NameB'InputFile=>"input_second_solve");
	moveB'File(NCO#"Directory","nonsingular_solutions","stageTwo_solutions",CopyB'File=>true);
	moveB'File(NCO#"Directory","nonsingular_solutions","start",CopyB'File=>true);
	moveB'File(NCO#"Directory","nonsingular_solutions","member_points",CopyB'File=>true));
    readFile(NCO#"Directory");
    print(pairJac);
    print (peek first pairGradient);
    print(pairScale);
    print(peek first pairData);
    print(peek first pairWeight);
--hyperplane
    if stage==1 or stage==0 or stage==2 then hyperplaneAtInfinity:=makeB'Section(
    	sum apply(nc,i->{data_i*(primalList_i)}),
	B'NumberCoefficients=>{1},
	NameB'Section=>numerHB);
----Input file for stage 1 and stage 2.
    win:=L|G|randomizedCritConditions;
--Gradient conditions (RHS)  (STAGE ONE)
    if stage==0 or stage==1 then    RHS:=apply(nc,i->makeB'Section(
	{topDenomQ*data_i,-topNumerHB*primalList_i*startWeight_i},
	NameB'Section=>"RHS"|i,
	B'NumberCoefficients=>{topL0*topNumerHB^(first degRescale),toString(topL0*topNumerHB^(first degRescale))}
	));
    if stage==0 or stage==1 then isoQ:=makeB'Section(
    	sum apply(nc,i->{startWeight_i*(primalList_i)^2}),
	B'NumberCoefficients=>{1},
	NameB'Section=>denomQ);
--Jacobian ring
    theR:=ring first F;
    numX:=#gens theR;
    kk1:=coefficientRing ring first F;
    jacS:=theR**kk1[apply(#L+#G,i->lagMult|i+1)]**kk1[{numerHB,denomQ}|{tWeight}];
    jacLamList:=flatten entries basis({0,1,0},jacS);
    (jacNumerHB,jacDenomQ,jacTWeight):=toSequence flatten entries basis({0,0,1},jacS);
    jacLV:=apply(jacLamList,drop(degRescale,1),(lam,j)->if j==0 
	then lam else if j>0 then lam*jacNumerHB^j 
	else print "Error: Homogenized incorrectly.");
    --print LV; 
    print 7;
    startJacStartCondition:=flatten entries (matrix{jacLV}*sub((jacL||jacG),jacS));    
    LHS:=apply(nc,i->"LHS"|i=>startJacStartCondition_i);
--Jacobian definition conditions (LHS) 
---SUPPORT FUNCTIONS
--Writing functions
    print 8;
    runWrite:=(stage,PG,nif,bfs)->(
	makeB'InputFile(NCO#"Directory",NameB'InputFile=>nif,
	    HomVariableGroup=>(NCO#"HomogeneousVariableGroups")|{{topL0}|jacLamList},
    	    AffVariableGroup=>NCO#"AffineVariableGroups",
	    B'Configs=>{
	    	"UseRegeneration"=>1,
	    	"TrackType"=>0,
	    	"ParameterHomotopy"=>stage,
	    	"PrintPathProgress"=>1000}|(NCO#"BertiniStartFiberSolveConfiguration"),
	    B'Polynomials=>win,
    	    ParameterGroup=>PG,
	    B'Functions=>bfs,
	    B'Constants=>NCO#"BertiniConstants"));    
    writeMTFile:=(s,k,bp,bfs)->makeB'InputFile(theDir,NameB'InputFile=>(defaultMTName|s|toString k),
	--Which variables come first?
	AffVariableGroup=>flatten flatten{NCO#"HomogeneousVariableGroups",{{topL0}|jacLamList},NCO#"AffineVariableGroups"},
	B'Configs=>{"TrackType"=>k,"PrintPathProgress"=>1000}|(NCO#"BertiniMembershipTestConfiguration"),
	B'Polynomials=>bp,
	B'Functions=>bfs,
	B'Constants=>NCO#"BertiniConstants"
	);
    print 9;
    writeManyMT:=(stage,bfs)->(
	writeMTFile("Residual"|stage|"_",1,{first last critConditions},bfs);
    	writeMTFile("Residual"|stage|"_",3,{first last critConditions},bfs);
    	writeMTFile("Degenerate"|stage|"_"|0|"_",1,{lagMult|"0"},bfs);
  	writeMTFile("Degenerate"|stage|"_"|1|"_",1,{numerHB},bfs);
  	writeMTFile("Degenerate"|stage|"_"|2|"_",1,{denomQ},bfs);
    	writeMTFile("Degenerate"|stage|"_"|0|"_",3,{lagMult|"0"},bfs);
  	writeMTFile("Degenerate"|stage|"_"|1|"_",3,{numerHB},bfs);
  	writeMTFile("Degenerate"|stage|"_"|2|"_",3,{denomQ},bfs);
    	scan(#F,i->(
    	    writeMTFile("Hypersurface"|stage|"_"|i|"_",1,{F_i},bfs);
    	    writeMTFile("Hypersurface"|stage|"_"|i|"_",3,{F_i},bfs);        ))  );
---Run membershipTest
    print 10;
    runMT:=(s)->(
   	runBertini(theDir,NameB'InputFile=>defaultMTName|s|"1");
	print (defaultMTName|s|"1");
    	moveB'File(theDir,"bertini_session.log","bertini_session_MT_"|s|"1.log",CopyB'File => true);
    	runBertini(theDir,NameB'InputFile=>defaultMTName|s|"3");
	print (defaultMTName|s|"3");
    	moveB'File(theDir,"bertini_session.log","bertini_session_MT_"|s|"3.log",CopyB'File => true);
    	outIM:=importIncidenceMatrix(theDir);
    	print outIM;
    	return outIM);                                                                           
    --Run Sort
    print 11;
    runSort:=(stage)->(
--	moveB'File(theDir,"nonsingular_solutions","member_points");
	print "isResidual";
	imResidual:=runMT("Residual"|stage|"_");
	--Degenerate
	print "isDegenerate";
	imAllDegenerate:=apply(3,i->runMT("Degenerate"|stage|"_"|i|"_"));
	--Hypersurfaces
	print "isMemberOfVariety";
	imAllHypersurfaces:=apply(#F,i->runMT("Hypersurface"|stage|"_"|i|"_"));
	EDDeg:=0;
	isMemberEveryHypersurface:=(i)->(
	    output:=true;
	    scan(imAllHypersurfaces,j->if {}==j_i then (output=false;break));
	    return output);
	isMemberAnyDegenerate:=(i)->(
	    output:=false;
	    scan(imAllDegenerate,j->if {}=!=j_i then (output=true;break));
	    return output);
    	ts:={};
	scan(#imResidual,i->print( imResidual_i=!={}, not isMemberAnyDegenerate(i), isMemberEveryHypersurface(i)));
	scan(#imResidual,i->if imResidual_i=!={} and not isMemberAnyDegenerate(i) and isMemberEveryHypersurface(i) 
	    then (EDDeg=EDDeg+1; ts=ts|{1}) else ts=ts|{0});
	NCO#"TrackSolutions"=ts;
	print("EDDeg",EDDeg,"Stage",stage);
	return EDDeg);
    --RUN  more writing functions
    print 11;    
--END Support functions
    print 12;
--STAGE ONE
    if stage==1 or stage==0
    then (
	nif:="inputCriticalPointSuperSet";
    	bfs:=NCO#"BertiniSubstitute"|primalSub|{hyperplaneAtInfinity,isoQ}|RHS|LHS|critConditions;
    	print(13,"A");
    	runWrite(stageOne,{"asdfadagds"},nif,bfs);
    	runBertini(theDir,NameB'InputFile=>nif);
	print nif; 
	moveB'File(theDir,"bertini_session.log","bertini_session_"|nif|".log",CopyB'File => true);
	moveB'File(theDir,"nonsingular_solutions","member_points",CopyB'File => true);
	moveB'File(theDir,"nonsingular_solutions","dummy");
    	print(13,"B");
	writeManyMT(stageOne,bfs);
    	print(13,"C");
    	GED:=runSort(stageOne));
    print 9;
    filterSolutionFile(NCO,"start",nc);
    print 10;
--Gradient conditions (RHS)  (STAGE TWO)
    if stage==2  or stage==0
    then (writeParameterFile(theDir,{0},NameParameterFile=>"start_parameters");
    	writeParameterFile(theDir,{1},NameParameterFile=>"final_parameters"));
    print("D",1);
    if stage==0 or stage==2 then    RHS=apply(nc,i->makeB'Section(
	{topDenomQ*data_i,-topNumerHB*primalList_i*startWeight_i,-topNumerHB*primalList_i*targetWeight_i},
	NameB'Section=>"RHS"|i,
	B'NumberCoefficients=>{topL0*topNumerHB^(first degRescale),
		    "(1-"|tWeight|")*"|toString(topL0*topNumerHB^(first degRescale)),
		    tWeight|"*"|toString(topL0*topNumerHB^(first degRescale))}
	));
    if stage==2 then print("RHSMT",peek first RHS);
    if stage==0 or stage==2 then    RHSMT:=apply(nc,i->makeB'Section(
	{topDenomQ*data_i,-topNumerHB*primalList_i*targetWeight_i},
	NameB'Section=>"RHS"|i,
	B'NumberCoefficients=>{topL0*topNumerHB^(first degRescale),		   
		    toString(topL0*topNumerHB^(first degRescale))}
	));
    if stage==2 then     print("RHSMT",peek first RHSMT);
    if stage==0 or stage==2 then isoQ=makeB'Section(
    	sum apply(nc,i->{startWeight_i*(primalList_i)^2,targetWeight_i*(primalList_i)^2}),
	B'NumberCoefficients=>{"(1-"|tWeight|")",tWeight},
	NameB'Section=>denomQ);
    if stage==2 then     print ("ISOQ",peek isoQ);
    if stage==0 or stage==2 then isoQMT:=makeB'Section(
    	sum apply(nc,i->{targetWeight_i*(primalList_i)^2}),
	B'NumberCoefficients=>{1},
	NameB'Section=>denomQ);
    if stage==2 then     print ("ISOQMT",peek isoQMT);
    if stage==2 or stage==0
    then (
	nif="inputParameterHomotopySuperSet";
    	bfs=NCO#"BertiniSubstitute"|primalSub|{hyperplaneAtInfinity,isoQ}|RHS|LHS|critConditions;
    	print(8,"B");
    	runWrite(stageTwo,{tWeight},nif,bfs);
    	runBertini(theDir,NameB'InputFile=>nif);
	print nif; 
	moveB'File(theDir,"bertini_session.log","bertini_session_"|nif|".log",CopyB'File => true);
	moveB'File(theDir,"nonsingular_solutions","member_points",CopyB'File => true);
	moveB'File(theDir,"nonsingular_solutions","dummy2");
    	print(8,"B");
	RHS=RHSMT;
	isoQ=isoQMT;
    	bfs2:=NCO#"BertiniSubstitute"|primalSub|{hyperplaneAtInfinity,isoQ}|RHS|LHS|critConditions;
	writeManyMT(stageTwo,bfs2);
    	print(8,"C");
    	UED:=runSort(stageTwo));
    return(GED=>UED));
*-
-*   
runBertiniStartEDDegree=method()
runBertiniStartEDDegree(NumericalComputationOptions):=(NCO)->runBertiniStartEDDegree(NCO,(0,0,0),1,#NCO#"Model")
runBertiniStartEDDegree(NumericalComputationOptions,Sequence,ZZ):=(NCO,ht,stage)->runBertiniStartEDDegree(NCO,ht,stage,#NCO#"Model")
runBertiniStartEDDegree(NumericalComputationOptions,Sequence,ZZ,ZZ):=(NCO,ht,stage,n)->(
    theDir:=NCO#"Directory";
    if stage===1 then nif:="inputCriticalPointSuperSet" 
    else if stage===2 then nif="inputParameterHomotopySuperSet";        
    (pvM,pvD,pvW):=ht;--weight is last
    pgStart:=ht/(i->if i===null then 0 else i)//toList;
    pgTarget:=ht/(i->if i===null then 1 else i)//toList;
    if stage==2 
    then (writeParameterFile(theDir,pgStart,NameParameterFile=>"start_parameters");
    	writeParameterFile(theDir,pgTarget,NameParameterFile=>"final_parameters"));
    runBertini(theDir,NameB'InputFile=>nif);
    print nif; 
    moveB'File(theDir,"bertini_session.log","bertini_session_"|nif|".log",CopyB'File => true);
    moveB'File(theDir,"nonsingular_solutions","member_points");
--Residual
    print "isResidual";
    imResidual:=runMT("Residual"|stage|"_");
--Degenerate
    print "isDegenerate";
    imDegenerate:=runMT("Degenerate"|stage|"_");
--Hypersurfaces
    print "isMemberOfVariety";
    imAllHypersurfaces:=apply(n,i->runMT("Hypersurface"|stage|"_"|i|"_"));
    EDDeg:=0;
    memberEveryHypersurface:=(i)->(
	output:=true;
	scan(imAllHypersurfaces,j->if {}==j_i then (output=false;break));
	return output);
    ts:={};
    scan(#imResidual,i->if imResidual_i=!={} and imDegenerate_i=={} and memberEveryHypersurface(i) 
	then (EDDeg=EDDeg+1; ts=ts|{1}) else ts=ts|{0});
    NCO#"TrackSolutions"=ts;
--    moveB'File(theDir,"bertini_session_CriticalPointSuperSet.log","bertini_session.log");
--    return(imResidual,imDegenerate)
    return(EDDeg)
     )
*- 













-*
weightEDDegreeHomotopy=method()
weightEDDegreeHomotopy(String,Sequence,List):=(theDir,P,TWV)->(
    print ("A",0);
    NCO:=newNumericalComputationOptions(theDir,P);
    NCO#"TargetWeight"=TWV;
    nc:=#gens ring first (NCO#"Model")+1+#NCO#"WitnessModel"+#NCO#"StartSubmodel";
    print("nc",nc);
    numF:=#(NCO#"Model");
    homotopyType:=(0,0,null);
    print ("A",1);
    startEDDegree(NCO,homotopyType,stageOne);
    print ("A",2);
    GED:=runBertiniStartEDDegree(NCO,homotopyType,stageOne);    
    print (GED,"GED");
    filterSolutionFile(NCO,"start",nc) ;
    readFile(NCO#"Directory","start",100000);
    print ("A",3);
    startEDDegree(NCO,homotopyType,stageTwo);
    UED:=runBertiniStartEDDegree(NCO,homotopyType,stageTwo);
    print ("A",4);
    return  (GED=>UED)
    )
*-    



---EXAMPLES
--restart
--path=prepend("/Users/jo/Documents/GoodGit/EuclideanDistanceDegree",path)
--loadPackage("EuclideanDistanceDegree",Reload=>true)
R=QQ[x0,x1,x2,x3]
(a,b,c,d)=(1,3, 1,3)
F={x0^a*x1^b-x2^c*x3^d}
F=F|{random({1},R)+10*random({1},R)}
determinantalUnitEuclideanDistanceDegree F
determinantalGenericEuclideanDistanceDegree F

R=QQ[x0,x1,x2,x3]
(a,b,c,d)=(1,3, 1,3)
F={x0^a*x1^b-x2^c*x3^d}
euler Proj(R/ideal F)
F=F|{2*x0+13*x1+335*x2+17*x3}
euler Proj(R/ideal F)

help 




F={x0^a*x1^b-x2^c*x3^d,x0^2+x1^2+x2^2+x3^2}
I=ideal F
primaryDecomposition ideal singularLocus I
decompose ideal singularLocus I
oo/codim
ooo/degree

(a,b,c)=(3,3, 3)
d=a+b+c
F={x0^a*x1^b*x2^c+x3^d}






help EuclideanDistanceDegree
factor first F
radical ideal singularLocus ideal F
--[EX 1] 
R=QQ[x0,x1,x2,y0,y1,y2];
F=flatten entries gens minors(2,genericMatrix(R,3,2))
G=drop(F,-(#F-2))
L={}
startEDDegree(storeBM2Files,F,G,L,Weight=>"Generic")
runBertiniStartEDDegree(storeBM2Files,#F)--10

startEDDegree(storeBM2Files,F,G,{},Weight=>"Unit")
runBertiniStartEDDegree(storeBM2Files,#F)--2

--[EX 2] 
----Key words: 3 by 3 matrices rank two matrices, singular variety
--storeBM2Files="/Users/jo/Desktop/BertiniOutputFiles/****"
R=QQ[x11,x12,x13,
    x21,x22,x23,
    x31,x32,x33];
F=flatten entries gens minors(3,genericMatrix(R,3,3))
P=(F,F,L)
NCO=newNumericalComputationOptions(storeBM2Files,P)

methods homotopyEDDegree
homotopyEDDegree(NCO,"Weight",true,true)

(storeBM2Files,F,G,{},Weight=>"Unit")
runBertiniStartEDDegree(storeBM2Files,#F)--3

startEDDegree(storeBM2Files,F,G,L,Weight=>"Generic")
runBertiniStartEDDegree(storeBM2Files,#F)--39

--These results agree with those on page 5 of https://www.researchgate.net/publication/258374161_Exact_Solutions_in_Structured_Low-Rank_Approximation/download
L={x12-x21,x31-x22,x31-x13,x32-x23}

startEDDegree(storeBM2Files,F,G,L,Weight=>"Unit")
runBertiniStartEDDegree(storeBM2Files,#F)--9
startEDDegree(storeBM2Files,F,G,L,Weight=>"Generic")
runBertiniStartEDDegree(storeBM2Files,#F)--13


---
xVars=flatten apply(5,i->apply(5,j->value("x"|i|j)))
R=CC[xVars];
M=genericMatrix(R,5,5)
F=flatten entries gens minors(3,M)
--G=apply(5-2,i->apply(5-2,j->({0,1,2}+{i,i,i},{0,1,2}+{j,j,j})))
G=flatten apply(5-2,i->apply(5-2,j->det submatrix(M,{0,1,2}+{i,i,i},{0,1,2}+{j,j,j})))
--L={random({1},R)}
L={}
startEDDegree(storeBM2Files,F,G,{},Weight=>"Unit")
runBertiniStartEDDegree(storeBM2Files,#F)--5 choose 2

startEDDegree(storeBM2Files,F,G,L,Weight=>"Generic")
runBertiniStartEDDegree(storeBM2Files,#F)--


R=QQ[t]






---
--[EX 1] 
R=QQ[x,y];
F={x^4+y^4-1}
G=F
L={}
apropos "EDD"
determinantalUnitEuclideanDistanceDegree(F)
determinantalGenericEuclideanDistanceDegree(F)
leftKernelUnitEDDegree(storeBM2Files,1,F)
runBertiniEDDegree(storeBM2Files)

symbolicWeightEDDegree
startEDDegree(storeBM2Files,F,G,L,Weight=>"Generic")
runBertiniStartEDDegree(storeBM2Files,#F)--10

restart
loadPackage("EuclideanDistanceDegree",Reload=>true)
R=QQ[x0,x1,x2]
--f=x0^2*x1-x2*x3^2
f=x0*x1-x2*(x1-x0)
F={f}
Z=radical  (ideal(sum apply(gens R,i->i^2))+ideal F)
bertiniPosDimSolve flatten entries gens Z-- two lines
determinantalGenericEuclideanDistanceDegree F
determinantalUnitEuclideanDistanceDegree F


determinantalGenericEuclideanDistanceDegree Z
determinantalUnitEuclideanDistanceDegree Z




restart
loadPackage("EuclideanDistanceDegree",Reload=>true)
R=QQ[x0,x1,x2,t,s,lam]
xList={x0,x1,x2,t,s}
f=x0*x1-x2*(x1-x0)
--f=x0^2+x1^2-x2^2
--F={f,t*(x0^2+x1^2+x2^2)}

xList={x0,x1,x2}
F={f}
Z=radical  (ideal(sum apply(xList,i->i^2))+ideal F)
bertiniPosDimSolve flatten entries gens Z-- two lines
determinantalGenericEuclideanDistanceDegree F
determinantalUnitEuclideanDistanceDegree F
win=ideal F+ minors(#F+2,(
    matrix transpose apply(xList,v->{v*(s+t*random(1,1000)),random(1,1000)})  )||matrix makeJac(F,xList)
    )
decWin= decompose win;
netList decWin
decWin/degree
I= sub(first decWin,{t=>0,s=>1})
decompose  I
factor ( eliminate({x2},I))_0
coefficients( ( eliminate({x2},first decWin))_0,Variables=>xList)
decompose I




restart
loadPackage("EuclideanDistanceDegree",Reload=>true)
R=QQ[x0,x1,x2,x3,t,s]
f=x0*x1-x2*x3
xList={x0,x1,x2,x3}
F={f}
Z=radical  (ideal(sum apply(xList,i->i^2))+ideal F)
bertiniPosDimSolve flatten entries gens Z-- two lines
determinantalGenericEuclideanDistanceDegree F
determinantalUnitEuclideanDistanceDegree F
win=ideal F+ minors(#F+2,(
    matrix transpose apply(xList,v->{v*(s+t*random(1,1000)),random(1,1000)})  )||matrix makeJac(F,xList)
    )
decWin= decompose win;

netList decWin
decWin/degree
I= sub(first decWin,{t=>0,s=>1})
decI=decompose I
decI/(i->i==i+Z)
oo/degree



I= sub(first decWin,{})

coefficients( ( eliminate({x1,x2},I))_0,Variables=>xList)


decompose  I
oo/degree
coefficients( ( eliminate({x2},I))_0,Variables=>xList)

coefficients( ( eliminate({x2},first decWin))_0,Variables=>xList)
decompose I

---
restart
loadPackage("EuclideanDistanceDegree",Reload=>true)
R=QQ[x0,x1,x2,x3,y,t,s,lam]
xList={x0,x1,x2,x3,y}
f=x0*x1-x2*x3
g=(-y^2+sum apply(xList,i->i^2))-y
F={f,g}
Z=radical  (ideal(sum apply(xList,i->i^2))+ideal F)
bertiniPosDimSolve flatten entries gens Z-- two lines
determinantalGenericEuclideanDistanceDegree F
determinantalUnitEuclideanDistanceDegree F
win=ideal F+ minors(#F+2,(
    matrix transpose apply(xList,v->{v*(random(1,1000)),random(1,1000)})  )||matrix makeJac(F,xList)
    )

win=ideal F+ minors(#F+2,(
    matrix transpose apply(xList,v->{v*(s+t*random(1,1000)),random(1,1000)})  )||matrix makeJac(F,xList)
    )

printGens win
decWin= decompose win;

netList decWin
decWin/degree
I= sub(first decWin,{t=>0,s=>1})
decompose I

I= sub(first decWin,{})

coefficients( ( eliminate({x1,x2},I))_0,Variables=>xList)


restart
loadPackage"EuclideanDistanceDegree"
R=QQ[x1,x2,x3,x4]
f=det matrix{{x1,x2,x4},
    {x4,0,x3},
    {0,x3,x4}}
factor f
F={f}
determinantalGenericEuclideanDistanceDegree F
determinantalUnitEuclideanDistanceDegree F


restart
loadPackage"EuclideanDistanceDegree"
R=QQ[x1,x2,x3,x4,x5,x6,x7,x8,x9]
M=transpose genericMatrix(R,3,3)
F={x2-x4,x8-x6,x2-x8,det M}--(unit,generic)=(15,21)
--bertiniPosDimSolve F--codim 4 and degree is 3. 
#F==4
P=(F,F,{})
theDir
NCO=newNumericalComputationOptions(theDir,P)
help EuclideanDistanceDegree
homotopyEDDegree(NCO,"Weight",true,true)                    



restart
loadPackage"EuclideanDistanceDegree"
R=QQ[x1,x2,x3,x4,x5,x6,x7,x8,x9]
M=transpose genericMatrix(R,3,3)
F={x2-x4,x8-x6,det M}--(generic,unit)=(39,15)
bertiniPosDimSolve F--codim 4 and degree is 3. 
Q=ideal sum apply(gens R,i->i^2)
--sl= ideal F+ideal mingens ideal singularLocus(Q+ideal F)
--decSL=decompose sl;
 netList decSL;
decSL/codim---{7,7,7}
decSL/degree --{2, 2, 4}  -->ED degrees are (2,2,10)
---each of the first two lines intersects each of the second two lines (like a square)
--2 of these points are also on the quartic. 
--Intersection lattice: {line1a,line1b,line2a,line2b,quartic}--{2,2,2,2,2}
primaryDecomposition ideal mingens ideal singularLocus sl ---4points
radical (decSL_0+decSL_2)
degree radical sum decSL

#F==3
P=(F,F,{})
theDir
NCO=newNumericalComputationOptions(theDir,P)
help EuclideanDistanceDegree
 NCO#"StartData"=apply(#gens R,i->random RR)
 NCO#"StartData"=(.525992249534688+.888630754215339*ii)*{.474323, .269152, .859334, .370283, .785498, .263867, .468432, .743158, .514817}
homotopyEDDegree(NCO,"Weight",true,true)                    
cp=importSolutionsFile(theDir,NameSolutionsFile=>"criticalPointFile");
first cp

#cp
S01=decompose radical(decSL_0+decSL_1)
S02=decompose radical(decSL_0+decSL_2)
S12=decompose radical(decSL_1+decSL_2)
netList apply(S01|S02|S12,i->apply(S01|S02|S12,j->i==j))
S01--two different components
radical (sum S01)
decompose radical sum decSL


radical sum (S01|S02|S12)

--singular locus is four lines. 
quartic=sub(ideal(x3-x7,x1+x5+x9,x6-x8,x2-x4,x4^2+x5^2+x5*x9,x8^2-x5*x9,x4*x7+x5*x8+x8*x9,x5*x7-x4*x8,x7*x8-x4*x9,x7^2+x5*x9+x9^2),R)
singularLocus quartic
bertiniPosDimSolve flatten entries gens quartic
codim quartic
numgens quartic
printGens quartic
G={(x3-x7),
(x1+x5+x9),
(x6-x8),
(x2-x4),
(x4^2+x5^2+x5*x9),
(x8^2-x5*x9),
--(x4*x7+x5*x8+x8*x9),
--(x5*x7-x4*x8),
--(x7*x8-x4*x9),
(x7^2+x5*x9+x9^2)}/(i->sub(i,R))
#G
#G
codim quartic
determinantalUnitEuclideanDistanceDegree
bertiniPosDimSolve G
P2=(flatten entries gens quartic,G,{})
theDir2=storeBM2Files
NCO2=newNumericalComputationOptions(theDir2,P2)

--GED degree of quartic is 10. 
help EuclideanDistanceDegree
homotopyEDDegree(NCO2,"Weight",true,true)                    







restart
loadPackage"EuclideanDistanceDegree"
R=QQ[m1,m2,m3,u1,u2,u3,x,y,z,w1,w2,w3]
xList={x,y,z}
mList={m1,m2,m3}
mList={u1,u2,u3}
f=x^2+y^2-4*z^2
F={f}
Z=radical  (ideal(sum apply(xList,i->i^2))+ideal F)
bertiniPosDimSolve flatten entries gens Z-- two lines
determinantalGenericEuclideanDistanceDegree F
determinantalUnitEuclideanDistanceDegree F
--GED--generic m. 
genericM=matrix{{(1+m1)*(x-u1),(1+m2)*(y-u2),(1+m3)*(z-u3)}}||matrix makeJac(F,xList)
fixGEDProblem={u1=>1,u2=>1,u3=>1}|{m1=>12,m2=>124,m3=>99}

gedI=saturate((ideal F +minors(2,sub(genericM,fixGEDProblem))),ideal(x,y,z))
4==degree gedI
gedE=(eliminate({y,z},gedI))_*//first
--UED
fixUEDProblem={m1=>0,m2=>0,m3=>0}
uedI=saturate((ideal F +minors(2,sub(genericM,fixUEDProblem))),ideal(x,y,z))
2==degree sub(uedI,{u1=>134,u2=>3414,u3=>13444})
uedE=(eliminate({y,z},uedI))_*//first


wM=matrix{{w1*(x-u1),w2*(y-u2),w3*(z-u3)}}||matrix makeJac(feg Z,xList)
zedI=saturate((Z+minors(codim Z+1,wM)),ideal(x,y,z))

degree sub( saturate((Z+minors(codim Z+1,wM)),ideal(x,y,z)),fixUEDProblem|{w1=>134,w2=>2355,w3=>455})
zedE=(eliminate({y,z},zedI))_*//first

doubleProblem=ideal mingens ideal last coefficients(zedE*uedE-gedE,Variables=>{x})
codim 
printGens ideal mingens sub(doubleProblem,{u2=>124,u3=>35,w1=>342,w2=>242})


bigI=uedI+gedI+zedI
decompose bigI

coefficients((eliminate({z,y},saturate(uedI,radical ideal singularLocus ideal F)))_0,Variables=>{x})
coefficients((eliminate({z,y},saturate(gedI,radical ideal singularLocus ideal F)))_0,Variables=>{x})


g1=(eliminate({z,y},saturate(uedI,radical ideal singularLocus ideal F)))_0
g2=(eliminate({z,y},saturate(gedI,radical ideal singularLocus ideal F)))_0

S=frac (QQ[m1,m2,m3,u1,u2,u3])[x,y,z]
coefficientRing S
h1=sub(g1,S)
h2=sub(g2,S)
win=h2%ideal h1
toString (last coefficients win)_(0,0)


T=QQ[m1,m2,m3,u1,u2,u3]
umI=gcd(sub((last coefficients win)_(0,0),T),sub((last coefficients win)_(1,0),T))


--decompose umI

apropos"rder"
help MonomialOrderin
leadCoefficient(g1)
g2% g1



matrix transpose apply(xList,v->{v*(1+mLis),random(1,1000)})  )||matrix makeJac(F,xList)
gedProblem=
ideal F

minors(#F+2,(
    
    )

win=ideal F+ 


----Let's consider 2x2 rank one matrices
restart
loadPackage"EuclideanDistanceDegree"
R=QQ[x1,x2,x3,x4]
M=transpose genericMatrix(R,2,2)
F={det M}--(generic,unit)=(6,2)
bertiniPosDimSolve F--projective dim 2 and degree is 2
Q=ideal sum apply(gens R,i->i^2)
sl= ideal mingens ideal singularLocus(Q+ideal F)
decSL=decompose sl;
 netList decSL
decSL/codim
decSL/degree 
--singular locus is four projective points 
bertiniPosDimSolve flatten entries gens sl--4 projective points. 
#F==1
P=(F,F,{})
theDir
NCO=newNumericalComputationOptions(theDir,P)
help EuclideanDistanceDegree
homotopyEDDegree(NCO,"Weight",true,true)   --(6,2)                 

cp=importSolutionsFile(theDir,NameSolutionsFile=>"criticalPointFile")
netList cp
---
R=QQ[m0,m1,m2,m3,m4,u1,u2,u3,u4,x1,x2,x3,x4,w1,w2,w3,w4,s,t]
xList={x1,x2,x3,x4}
mList={m1,m2,m3,m4}
uList={u1,u2,u3,u4}
wList={w1,w2,w3,w4}
Q=ideal sum apply(xList,i->i^2)
f=x1*x2-x3*x4
F={f}
Z=radical  (ideal(sum apply(xList,i->i^2))+ideal F)
bertiniPosDimSolve flatten entries gens Z-- two lines
determinantalGenericEuclideanDistanceDegree F
determinantalUnitEuclideanDistanceDegree F
--GED--generic m. 

M=matrix{uList}||matrix{wList}*diagonalMatrix xList||matrix makeJac(F,xList)
--B=matrix{}||matrix{mList}||matrix{wList}
wSub=apply(mList,uList/(i->1),(a,b)->a*s+m0*b*t);wSub=apply(wList,wSub,(i,j)->i=>j)
wSub
I=minors(codim ideal F+2,sub(M,wSub))
I=saturate(I,ideal(t,s))
I=saturate(I+ideal F,ideal(t,s))
I=saturate(I,ideal xList);
I=saturate(I,ideal {m0,m1,m2,m3,m4});
I=saturate(I,ideal {m0});

--uSub=uList/(i->i=>random(1,100))
uSub={u1 => 32, u2 => 28, u3 => 13, u4 => 29}
E=eliminate({x1,x2},sub(I,uSub))
printGens sub(E,{s=>0})
(t)^4*(x3-x4)^2*(x3+x4)^2*(m0)^4*(99161*x3^2-226802*x3*x4+99161*x4^2)*(16)


I2= sub(I,{s=>0,t=>1})
A=saturate(I2,m0)
decA=decompose A
apply(decA,i->i+Q==i)--two of the three components are in the isotrpica quadric
twoPointsA= sub(first decA,uSub)
3==codim twoPointsA
2==degree twoPointsA
eliminate({x1,x2},twoPointsA)


twoPointsStandard=first decompose (minors(3,sub(M,uSub|(wList/(i->i=>1))))+ideal F)
codim twoPointsStandard
2===degree twoPointsStandard
twoPointsStandard==twoPointsA







---Let's try 2x3 matrices. Want positive dimensional Z.
---
R=QQ[m0,m1,m2,m3,m4,m5,m6,u1,u2,u3,u4,u5,u6,x1,x2,x3,x4,x5,x6,w1,w2,w3,w4,w5,w6,s,t]
xList={x1,x2,x3,x4,x5,x6}
mList={m1,m2,m3,m4,m5,m6}
uList={u1,u2,u3,u4,u5,u6}
wList={w1,w2,w3,w4,w5,w6}
Q=ideal sum apply(xList,i->i^2)
F=flatten entries gens minors(2,matrix{{x1,x2,x3},{x4,x5,x6}})
Z=radical  (ideal(sum apply(xList,i->i^2))+ideal F)

bertiniPosDimSolve flatten entries gens Z-- #gens R-24==3--codimension is 3 and projective dimension of Z is 5-3
(decompose Z)/gens/entries/flatten/bertiniPosDimSolve
--We have 2 lines and a quartic
determinantalGenericEuclideanDistanceDegree F--10
determinantalUnitEuclideanDistanceDegree F--2
--GED--generic m. 

M=matrix{uList}||matrix{wList}*diagonalMatrix xList||matrix makeJac(F,xList)
--B=matrix{}||matrix{mList}||matrix{wList}
wSub=apply(mList,uList/(i->1),(a,b)->a*s+m0*b*t);wSub=apply(wList,wSub,(i,j)->i=>j)
wSub
uSub={u1 => 32, u2 => 28, u3 => 13, u4 => 29}
I=sub(minors(codim ideal F+2,sub(M,wSub)),uSub);
I=ideal mingens ideal(gens I % ideal F)
I=sub(I,{m0=>1})
printGens I

I=saturate(I,ideal(t,s));
I=saturate(I+ideal F,ideal(t,s));
I=saturate(I,ideal xList);
I=saturate(I,ideal {m0,m1,m2,m3,m4});
I=saturate(I,ideal {m0});

--uSub=uList/(i->i=>random(1,100))

E=eliminate({x1,x2},sub(I,uSub))
printGens sub(E,{s=>0})
(t)^4*(x3-x4)^2*(x3+x4)^2*(m0)^4*(99161*x3^2-226802*x3*x4+99161*x4^2)*(16)


I2= sub(I,{s=>0,t=>1})
A=saturate(I2,m0)
decA=decompose A
apply(decA,i->i+Q==i)--two of the three components are in the isotrpica quadric
twoPointsA= sub(first decA,uSub)
3==codim twoPointsA
2==degree twoPointsA
eliminate({x1,x2},twoPointsA)


twoPointsStandard=first decompose (minors(3,sub(M,uSub|(wList/(i->i=>1))))+ideal F)
codim twoPointsStandard
2===degree twoPointsStandard
twoPointsStandard==twoPointsA



----Max's prediction. 
restart
printingPrecision =100
loadPackage"EuclideanDistanceDegree"
help EuclideanDistanceDegree
R=QQ[x1,x2,x3,x4,x5,x6]
M=transpose genericMatrix(R,3,2)
F=flatten entries gens minors(2,M)
G=drop(F,1)
P=(F,G,{})
theDir=temporaryFileName();mkdir theDir
NCO=newNumericalComputationOptions(theDir,P)
fixM={.935612+.780809*ii, .71813+.874296*ii, .056595+.850869*ii, .980549+.247701*ii, .595609+.191267*ii, .02298+.610646*ii}
fixW=apply(fixM,i->i+1)
fixV={.72466+.412908*ii, .20736+.413345*ii, .161095+.942996*ii, .653861+.917835*ii, .621858+.739543*ii, .22654+.870631*ii}
fixU=apply(#fixW,(i)->fixV_i/fixW_i*fixM_i)
--(1+m)*u=m*u
NCO#"TargetWeight"=fixW
NCO#"StartData"=fixU

homotopyEDDegree(NCO,"Weight",true, true)
elevenPoints=importSolutionsFile(theDir,NameSolutionsFile=>"criticalPointFile");
#elevenPoints==11

Z=radical ideal mingens ideal singularLocus (ideal F+ideal sum apply (gens R,i->i^2))
printGens Z
--bertiniPosDimSolve flatten entries gens Z
--      dim 2:  (dim=2,deg=2) (dim=2,deg=2)
--0==determinantalUnitEuclideanDistanceDegree flatten entries gens Z
--8==determinantalGenericEuclideanDistanceDegree flatten entries gens Z

4==codim Z
printGens Z
zg=Z_*
GZ=ideal {zg_0,zg_2,zg_4,zg_8}
codim Z==codim GZ
decompose GZ
PZ=(Z_*,GZ_*,{})
theDir=temporaryFileName();mkdir theDir
ZNCO=newNumericalComputationOptions(theDir,PZ)
ZNCO#"StartWeight"=fixM
ZNCO#"StartData"=fixV
homotopyEDDegree(ZNCO,"Weight",true, false)

eightPoints=importSolutionsFile(theDir,NameSolutionsFile=>"filterFile");
#eightPoints==8
pickOneOfEight=(i,eightPoints)->(
    onePoint=eightPoints_i;
    onePoint=drop(onePoint,#(GZ_*)+1);
    onePoint=(1/first onePoint)*onePoint    )
onePoint=pickOneOfEight(1,eightPoints)

apply(#eightPoints,i->pickOneOfEight(i,eightPoints))

--drop 5==#(GZ_*)+1 coordinates 
first\ apply(elevenPoints,i->((1/i_(#G+1))*drop(i,#G+1)))
netList\\apply(elevenPoints,i->((1/i_(#G+1))*drop(i,#G+2)))
onePoint

---Let's try symbolic computation.
R=QQ[s,t,x1,x2,x3,x4,x5,x6,m0]
xList={x1,x2,x3,x4,x5,x6}
M=matrix{{x1,x2,x3},{x4,x5,x6}}
F=flatten entries gens minors(2,M)
wFix=apply(xList,i->random(1,100))
uFix=apply(xList,i->random(1,100))
mFix={53, 67, 83, 1, 64, 96}

critM=(matrix{uFix}||
matrix{apply(#xList,i->(mFix_i*s+t)*xList_i)}||
matrix makeJac(F,xList))

Z=radical ideal mingens ideal singularLocus (ideal F+ideal sum apply (xList,i->i^2))
zg=Z_*
GZ=ideal {zg_0,zg_2,zg_4,zg_8}

critZ=Z+minors(2+codim Z,
    matrix{uFix}||(matrix{apply(#xList,i->(mFix_i*s+t*m0)*xList_i)}
	)||matrix makeJac(zg,xList));
decCZ=decompose ideal mingens critZ;
decCZ/degree
last decCZ
printGens last decCZ
printGens 
--degree first decCZ
decCZ/codim

intersectZF=ideal mingens(minors(codim ideal F+2,critM)+ideal F    +last decCZ)
decompose radical intersectZF
degree first oo



---Let's try the nodal curve
restart
printingPrecision =100
loadPackage"EuclideanDistanceDegree"
help EuclideanDistanceDegree
R=QQ[x,y,z]
G=F={x^2-y^3}
P=(F,G,{})
theDir=temporaryFileName();mkdir theDir
NCO=newNumericalComputationOptions(theDir,P)
fixM={.935612+.780809*ii, .71813+.874296*ii, .056595+.850869*ii}
fixW=apply(fixM,i->i+1)
fixV={.72466+.412908*ii, .20736+.413345*ii, .161095+.942996*ii}
fixU=apply(#fixW,(i)->fixV_i/fixW_i*fixM_i)
--(1+m)*u=m*u
NCO#"TargetWeight"=fixW
NCO#"StartData"=fixU

homotopyEDDegree(NCO,"Weight",true, true)
newPoints=importSolutionsFile(theDir,NameSolutionsFile=>"criticalPointFile")

Z=radical ideal mingens ideal singularLocus (ideal F+ideal sum apply (gens R,i->i^2))
printGens Z
--bertiniPosDimSolve flatten entries gens Z
--      dim 2:  (dim=2,deg=2) (dim=2,deg=2)
--0==determinantalUnitEuclideanDistanceDegree flatten entries gens Z
--8==determinantalGenericEuclideanDistanceDegree flatten entries gens Z

4==codim Z
printGens Z
zg=Z_*
GZ=ideal {zg_0,zg_2,zg_4,zg_8}
codim Z==codim GZ
decompose GZ
PZ=(Z_*,GZ_*,{})
theDir=temporaryFileName();mkdir theDir
ZNCO=newNumericalComputationOptions(theDir,PZ)
ZNCO#"StartWeight"=fixM
ZNCO#"StartData"=fixV
homotopyEDDegree(ZNCO,"Weight",true, false)

eightPoints=importSolutionsFile(theDir,NameSolutionsFile=>"filterFile");
#eightPoints==8
pickOneOfEight=(i,eightPoints)->(
    onePoint=eightPoints_i;
    onePoint=drop(onePoint,#(GZ_*)+1);
    onePoint=(1/first onePoint)*onePoint    )
onePoint=pickOneOfEight(1,eightPoints)

--drop 5==#(GZ_*)+1 coordinates 
first\ apply(elevenPoints,i->((1/i_(#G+1))*drop(i,#G+1)))
netList\\apply(elevenPoints,i->((1/i_(#G+1))*drop(i,#G+2)))
onePoint






R=CC[x,y,z]
f=x*y^2-z^3
writeLeftKernelProjectiveGenericEDDegree(theDir,{f})
runBertiniProjectiveEDDegree(theDir)



R=CC[x1,x2,x3,x4,x5,x6,x7,x8,x9]
f=det genericMatrix(R,3,3)
writeLeftKernelProjectiveGenericEDDegree(theDir,{f})--39
runBertiniProjectiveEDDegree(theDir)

writeLeftKernelProjectiveUnitEDDegree(theDir,{f})--3
runBertiniProjectiveEDDegree(theDir)





 loadPackage"EuclideanDistanceDegree"
 kk=QQ[I]/ideal(I^2+1);
 T=kk[x0,x1,x2,x3];
 q=x0^2+x1^2+x2^2+x3^2;
 F={(x1-I*x0)^2+2*(x3-I*x2)^2+q};
 --Symbolic computation (Grobner bases method):
 EDDefect=(determinantalGenericEuclideanDistanceDegree F-
  determinantalUnitEuclideanDistanceDegree F)/(degree kk) 
 --Numerical computation (Continuation method): 
 --  (i7-i8) Create temporary directories 
 --  (i9-i10) Write Bertini input files 
 --  (i11) Run Bertini and computes EDdefect(V(f))
 (dir1,dir2)=(temporaryFileName(),temporaryFileName()); 
 {dir1,dir2}/mkdir; 
 leftKernelGenericEDDegree(dir1,F)
 leftKernelUnitEDDegree(dir2,F)
 EDDefect=runBertiniEDDegree(dir1)-runBertiniEDDegree(dir2)
o11 = 5
