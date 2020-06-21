--This M2 works out some preliminary examples to motivate a project studying generic ED Degrees. 
----Result (1): A homotopy approach to solve nearest point problems for weighted least squares. 
----Result (2): Duality proven for rank one matrices and corank one matrices
----Corollary: Intersecting with a model with a general linear space is now well understood.



------------------------------------------------------------------------------------------------------------
--Example 1: Rank 1 2x3 matrices
------------------------------------------------------------------------------------------------------------
restart
printingPrecision =100
--loadPackage"EuclideanDistanceDegree"
--help EuclideanDistanceDegree
needsPackage("Bertini")

makeVar=(setN,x)->apply(setN,i->value(x|i))
TestConjectureGEDvUED=new Type of MutableHashTable 
newTestConjectureGEDvUED=(setN)->(
    theDir:=temporaryFileName();mkdir theDir;
    print theDir;    
    tc:=new TestConjectureGEDvUED from	{
	"ccR"=>CC[makeVar(setN,"u")|makeVar(setN,"w")|makeVar(setN,"x")|makeVar(setN+1,"L")],
	"ccS"=>CC[r,t],
    	"qqR"=>QQ[makeVar(setN,"u")|makeVar(setN,"w")|makeVar(setN,"x")|makeVar(setN+1,"L")],    	
	"xList"=>makeVar(setN,"x"),
	"wList"=>makeVar(setN,"w"),
	"uList"=>makeVar(setN,"u"),
	"lagList"=>makeVar(setN+1,"L"),
	"Directory"=>theDir};
    print 1;
    tc#"xFix"=apply(tc#"xList",i->i=>random CC);
    tc#"wFix"=apply(tc#"wList",i->i=>random CC*r+t);
    tc#"uFix"=apply(tc#"uList",i->i=>random CC);
    tc#"hyperplane"=makeB'Section(tc#"xList",NameB'Section=>"HX");
    return tc
)
inputModel=(tc,F,G)->(
    M:=matrix{tc#"uList"}||matrix {apply(tc#"xList",tc#"wList",(i,j)->i*j)}||matrix makeJac(G,tc#"xList");
    tc#"F"=F;
    tc#"G"=G;
    tc#"M"=M;
    useL:=apply(#tc#"G"+2,i->(tc#"lagList"#i));
    print useL;
    tc#"cEqu"=(ideal(matrix{useL}*tc#"M"))_*    )

tc=newTestConjectureGEDvUED(6);
peek tc
R= tc#"qqR";use R;
F=flatten entries gens minors(2,matrix{{x0,x1,x2},{x3,x4,x5}})--F is not a complete intersection.
G=drop(F,1)--G is a complete intersection such that V(F) is contained in V(G) as an irreducible component.
inputModel(tc,F,G)

makeB'InputFile(theDir,
    HomVariableGroup=>{xList,{s0,s1,s2,s3}},    
    B'Constants=>uSub|{r=>1,t=>1},
    B'Functions=>wSub|{hyperplane}|{L0=>"s0*HX",L1=>s1,L2=>s2,L3=>s3},
    B'Polynomials=>G|cEqu
    )
runBertini(theDir)
moveB'File(theDir,"nonsingular_solutions","start")

makeB'InputFile(theDir,
    HomVariableGroup=>{xList,{s0,s1,s2,s3}},  
    ParameterGroup=>{r},
    B'Configs=>{"ParameterHomotopy"=>2},  
    B'Constants=>uSub|{t=>1},
    B'Functions=>wSub|{hyperplane}|{L0=>"s0*HX",L1=>s1,L2=>s2,L3=>s3},
    B'Polynomials=>G|cEqu
    )
writeParameterFile(theDir,{1},NameParameterFile=>"start_parameters")
writeParameterFile(theDir,{0},NameParameterFile=>"final_parameters")
runBertini(theDir)
readFile(theDir)
elevenPoints=importSolutionsFile(theDir);
printingPrecision=6
apply(elevenPoints,i->SVD clean(1e-10,matrix{{i_0,i_1,i_2},{i_3,i_4,i_5}}))
---
Z=radical ideal mingens ideal singularLocus radical (ideal F+ideal sum apply (xList,i->i^2))

decompose Z
4==codim Z
printGens Z
zg=Z_*
--bertiniPosDimSolve zg
ZG=(ideal {zg_0,zg_2,zg_4,zg_8})_*
(decompose ideal ZG)/radical/degree

ZM=matrix{uList}||matrix {apply(xList,wList,(i,j)->i*j)}||matrix makeJac(ZG,xList)
ZcEqu=(ideal(matrix{{L0,L1,L2,L3,L4,L5}}*ZM))_*
ZG/degree
theDir=temporaryFileName();mkdir theDir;
makeB'InputFile(theDir,
    HomVariableGroup=>{xList|{"HX"},{s0,s1,s2,s3,s4,s5}},    
--    AffVariableGroup=>flatten{xList,{s0,s1,s2,s3,s4,s5}},    
    B'Constants=>uSub|{r=>1,t=>1},
--    B'Configs=>{UseRegeneration=>1},
    B'Functions=>wSub|{L0=>"s0*HX",L1=>s1,L2=>s2,L3=>s3,L4=>s4,L5=>s5},
--    B'Functions=>wSub|{HX}|{L0=>s0,L1=>s1,L2=>s2,L3=>s3,L4=>s4,L5=>s5},
    B'Polynomials=>ZG|ZcEqu|{makeB'Section(xList|{"HX"})}
--    B'Polynomials=>zg|ZcEqu|{makeB'Section({s0,s1,s2,s3,s4,s5,1}),makeB'Section(xList|{1})}
    )
runBertini(theDir)
newPoints=importSolutionsFile(theDir,NameSolutionsFile=>"nonsingular_solutions");
newPoints=importSolutionsFile(theDir,NameSolutionsFile=>"raw_solutions");
#newPoints
--twentyFourPoints=importSolutionsFile(theDir,NameSolutionsFile=>"singular_solutions");
--seventyTwoPoints=importSolutionsFile(theDir,NameSolutionsFile=>"nonsingular_solutions");
--newPoints=seventyTwoPoints;

apply(elevenPoints,i->delete(false,apply(newPoints,j->if abs(i_0*j_1-i_1*j_0)<1e-8 then true else null)))
apply(elevenPoints,i->SVD clean(1e-10,matrix{{i_0,i_1,i_2},{i_3,i_4,i_5}}))
apply(elevenPoints,i->sum apply({i_0,i_1,i_2,i_3,i_4,i_5},j->j^2))
netList oo
#twentyFourPoints


------------------------------------------------------------------------------------------------------------
--Example 2: Z is singular with no nodes.
------------------------------------------------------------------------------------------------------------
restart
printingPrecision =100
--loadPackage"EuclideanDistanceDegree"
--help EuclideanDistanceDegree
needsPackage("Bertini")
R=CC[u1,u2,u3,u4,u5,u6,w1,w2,w3,w4,w5,w6,x1,x2,x3,x4,x5,x6,L0,L1,L2,L3,L4,L5,L6]
xList= {x1,x2,x3,x4}
Q=sum apply(xList,i->i^2)
f=(x1-ii*x4)^3+2*(x3-ii*x2)^3+Q*(2*x4+3*x1+15*x2-7*x3)
wList={w1,w2,w3,w4}
uList={u1,u2,u3,u4}
lagList={L0,L1,L2,L3,L4}
G=F={f}
theDir=temporaryFileName();mkdir theDir
print theDir
 
M=matrix{uList}||matrix {apply(xList,wList,(i,j)->i*j)}||matrix makeJac(G,xList)
hyperplane=makeB'Section(xList,NameB'Section=>"HX")
cEqu=(ideal(matrix{{L0,L1,L2}}*M))_*
uSub=apply(uList,i->i=>random CC)
uSub={u1 => .437976264949257+.458082647800926*ii, u2 => .202827685631432+.494462510887304*ii, u3 => .265750610397259+.956260475610544*ii, u4 => .386065899883386+.761726882971112*ii, u5 => .813562119489001+.949531286791245*ii, u6 => .907947495546488+.285832262201472*ii}

S=CC[r,t]
wSub=apply(wList,i->i=>random CC*r+t)
print toString oo
wSub={w1 => (.412956862937663+.22500087147758*ii)*r+t, w2 => (.864160843906586+.513961647290348*ii)*r+t, w3 => (.933706921404453+.374950521798492*ii)*r+t, w4 => (.282411917737877+.0392926459311801*ii)*r+t, w5 => (.232646975110094+.898207105162729*ii)*r+t, w6 => (.358104555818471+.782058827435617*ii)*r+t}
M
makeB'InputFile(theDir,
    HomVariableGroup=>{xList,{s0,s1,s2}},    
    B'Constants=>uSub|{r=>1,t=>1},
    B'Functions=>wSub|{hyperplane}|{L0=>"s0*HX^2",L1=>"s1*HX",L2=>s2},
    B'Polynomials=>G|cEqu
    )
runBertini(theDir)
readFile(theDir)--18 GED  non-singular
moveB'File(theDir,"nonsingular_solutions","start")

makeB'InputFile(theDir,
    HomVariableGroup=>{xList,{s0,s1,s2}},  
    ParameterGroup=>{r},
    B'Configs=>{"ParameterHomotopy"=>2},  
    B'Constants=>uSub|{t=>1},
    B'Functions=>wSub|{hyperplane}|{L0=>"s0*HX^2",L1=>"s1*HX",L2=>s2},
    B'Polynomials=>G|cEqu
    )
writeParameterFile(theDir,{1},NameParameterFile=>"start_parameters")
writeParameterFile(theDir,{0},NameParameterFile=>"final_parameters")
runBertini(theDir)
readFile(theDir)--6 UED
critWX=importSolutionsFile(theDir,NameSolutionsFile=>"start");
importSolutionsFile(theDir,NameSolutionsFile=>"raw_solutions")
GED(X)=18=6+


netList oo
#critWX
printingPrecision=6
      +----------------------------------------------------------------------------------+
o90 = |{.212546-.322432*ii, -.406238-.267792*ii, .267792-.406238*ii, -.322432-.212546*ii}|
      +----------------------------------------------------------------------------------+
      |{.30486+.406926*ii, -.588987-.251957*ii, .251957-.588987*ii, .406926-.30486*ii}   |
      +----------------------------------------------------------------------------------+
      |{-.483977-.126918*ii, -.448126-.44337*ii, .44337-.448126*ii, -.126918+.483977*ii} |
      +----------------------------------------------------------------------------------+

---
--
restart
loadPackage"Bertini"
T=QQ[I]/ideal(I^2+1)[x1,x2,x3,x4]
xList= drop(gens T,-1)
xList=gens T
Q=sum apply(xList,i->i^2)
jj=I
f=(x1-jj*x4)^2+2*(x3-jj*x2)^2+Q--*(3*x1+5*x2-7*x3+2*x4)  (6,1)
f=(x1-jj*x4)^3+2*(x3-jj*x2)^3+Q*(3*x1+5*x2-7*x3+2*x4)
loadPackage"EuclideanDistanceDegree"
determinantalGenericEuclideanDistanceDegree {f}  
determinantalUnitEuclideanDistanceDegree {f}

bertiniPosDimSolve apply({x1,x2,x3,x4},i-> diff(i,f))
bertiniPosDimSolve {f}

radical ideal singularLocus ideal f
F={f}
A=  ideal singularLocus  ideal {f %Q,Q};
bertiniPosDimSolve(A_*)--one line
2*2==degree A---degree 4--one line with multiplicity 2
B=   ideal {f %Q,Q};
bertiniPosDimSolve(B_*)--4 lines. one with multiplicity 3.
degree B==2*(1+1+1+3)

C= first decompose radical ideal singularLocus  ideal {f %Q,Q}--L4=Z---one line. 
--ideal (x2 + I*x3, x1 - I*x4)
threeLines = saturate(B,C)
degree threeLines ==2*(1+1+1)
D=threeLines+C--three reduced points
degree D==2*(1+1+1)
(threeLines+C)== radical (threeLines+C)
decompose D
decompose sub(D,{x4=>-I,x1=>1,x3=>I*x2})
(-I:1:x2:I*x2)
x2^3=2*\jj



pDec=primaryDecomposition ideal {f %Q,Q}
degree\pDec
degree\radical \pDec
loadPackage"Bertini"
bertiniPosDimSolve((radical first pDec)_*)

peek oo
radical A==
decompose A
codim\primaryDecomposition 

ideal mingens 
decompose    ideal {f %Q,Q}

loadPackage"EuclideanDistanceDegree"
help leftKernelUnitEDDegree
leftKernelUnitEDDegree(storeBM2Files,1,F)--UED degree is 6
leftKernelGenericEDDegree(storeBM2Files,1,F)--GED degree is 18
leftKernelUnitEDDegree(storeBM2Files,2,F|{Q})
determinantalGenericEuclideanDistanceDegree  (F|{Q})

help EuclideanDistanceDegree
runBertini(storeBM2Files)
readFile(storeBM2Files)
--determinantalUnitEuclideanDistanceDegree F
--determinantalGenericEuclideanDistanceDegree F
--determinantalUnitEuclideanDistanceDegree(F)
Z= ideal singularLocus  (ideal F+ideal sum apply (xList,i->i^2))
primaryDecomposition Z
(degree Z)/2
Z1=  ideal mingens ideal singularLocus  radical (ideal F+ideal sum apply (xList,i->i^2))
degree Z1, codim Z1 --3 points. 

Z2=radical ideal mingens Z1
degree Z2,codim Z2
2*2--
(decompose Z)/codim
(decompose Z)/degree
loadPackage"Bertini"
bertiniPosDimSolve(feg Z)--dim 2, degree 1. 

18=6+2*(+
--Z=ideal mingens ideal (gens Z% (jj^2+1))
Z=saturate(Z,ideal drop(gens T,0))
Z=ideal mingens ideal (gens Z% (jj^2+1))
needsPackage"Bertini"
makeB'InputFile(storeBM2Files,
    HomVariableGroup=>drop(gens T,0),
    B'Polynomials=>Z_*,
    B'Configs=>{"TrackType"=>1},
    B'Constants=>{jj=>ii})

runBertini(storeBM2Files)
readFile(storeBM2Files)
netList importMainDataFile(storeBM2Files)



4==codim Z
printGens Z
zg=Z_*
bertiniPosDimSolve zg
ZG=(ideal {zg_0,zg_2,zg_4,zg_8})_*
(decompose ideal ZG)/radical/degree

ZM=matrix{uList}||matrix {apply(xList,wList,(i,j)->i*j)}||matrix makeJac(ZG,xList)
ZcEqu=(ideal(matrix{{L0,L1,L2,L3,L4,L5}}*ZM))_*
ZG/degree
theDir=temporaryFileName();mkdir theDir;
makeB'InputFile(theDir,
    HomVariableGroup=>{xList|{"HX"},{s0,s1,s2,s3,s4,s5}},    
--    AffVariableGroup=>flatten{xList,{s0,s1,s2,s3,s4,s5}},    
    B'Constants=>uSub|{r=>1,t=>1},
--    B'Configs=>{UseRegeneration=>1},
    B'Functions=>wSub|{L0=>"s0*HX",L1=>s1,L2=>s2,L3=>s3,L4=>s4,L5=>s5},
--    B'Functions=>wSub|{HX}|{L0=>s0,L1=>s1,L2=>s2,L3=>s3,L4=>s4,L5=>s5},
    B'Polynomials=>ZG|ZcEqu|{makeB'Section(xList|{"HX"})}
--    B'Polynomials=>zg|ZcEqu|{makeB'Section({s0,s1,s2,s3,s4,s5,1}),makeB'Section(xList|{1})}
    )
runBertini(theDir)
newPoints=importSolutionsFile(theDir,NameSolutionsFile=>"nonsingular_solutions");
newPoints=importSolutionsFile(theDir,NameSolutionsFile=>"raw_solutions");
#newPoints
--twentyFourPoints=importSolutionsFile(theDir,NameSolutionsFile=>"singular_solutions");
--seventyTwoPoints=importSolutionsFile(theDir,NameSolutionsFile=>"nonsingular_solutions");
--newPoints=seventyTwoPoints;

apply(elevenPoints,i->delete(false,apply(newPoints,j->if abs(i_0*j_1-i_1*j_0)<1e-8 then true else null)))
apply(elevenPoints,i->SVD clean(1e-10,matrix{{i_0,i_1,i_2},{i_3,i_4,i_5}}))
apply(elevenPoints,i->sum apply({i_0,i_1,i_2,i_3,i_4,i_5},j->j^2))
netList oo
#twentyFourPoints

R=QQ



restart
--Quadric example. 
--loadPackage"Bertini"
loadPackage"EuclideanDistanceDegree"
kk=QQ[I]/ideal(I^2+1)
T=kk[x0,x1,x2,x3]
Q=x0^2+x1^2+x2^2+x3^2
f=(x1-I*x0)^2+2*(x3-I*x2)^2+Q--*(3*x1+5*x2-7*x3+2*x4)  (6,1)
--Symbolic computation
EDDefect=1/(degree kk)*(determinantalGenericEuclideanDistanceDegree {f}-determinantalUnitEuclideanDistanceDegree {f})  
--Create directory, write files, run computation.
dir1=temporaryFileName(); mkdir dir1;dir2=temporaryFileName(); mkdir dir2;
leftKernelGenericEDDegree(dir1,codim ideal {f},{f})
leftKernelUnitEDDegree(dir2,codim ideal {f},{f})
EDDefect=runBertiniEDDegree(dir1)-runBertiniEDDegree(dir2)

examples EuclideanDistanceDegree

jj=I
f=(x1-jj*x4)^2+2*(x3-jj*x2)^2+Q--*(3*x1+5*x2-7*x3+2*x4)  (6,1)
f=(x1-jj*x4)^3+2*(x3-jj*x2)^3+Q*(3*x1+5*x2-7*x3+2*x4)
loadPackage"EuclideanDistanceDegree"
determinantalGenericEuclideanDistanceDegree {f}  
determinantalUnitEuclideanDistanceDegree {f}

bertiniPosDimSolve apply({x1,x2,x3,x4},i-> diff(i,f))
bertiniPosDimSolve {f}

radical ideal singularLocus ideal f
F={f}
A=  ideal singularLocus  ideal {f %Q,Q};
bertiniPosDimSolve(A_*)--one line
2*2==degree A---degree 4--one line with multiplicity 2
B=   ideal {f %Q,Q};
bertiniPosDimSolve(B_*)--4 lines. one with multiplicity 3.
degree B==2*(1+1+1+3)

