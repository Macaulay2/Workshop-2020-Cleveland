newPackage(
     "HierarchicalModels",
     Version => "1.0",
     Date => "May 12, 2020",
     Headline => "bla",
     Authors => {
	  {Name => "a"},
	  {Name => "b"}
	  },
     PackageImports => {
	  "FourTiTwo"
	  },
     )

export{}

loadPackage"FourTiTwo"


hmodel = method()
hmodel(List,List) := (r,Facets) -> (
R=QQ[x_(splice{#r:0})..x_r];  -- the source ring
S=QQ; --initiate S to be the ring QQ and  use iteration to construct the target ring
for i from 0 to (#Facets-1) do (S= tensor (S, QQ[y_(splice{#Facets_i:0,i})..y_(append (r_(Facets_i),i))]));
listOfImages={};
apply(flatten entries vars R, j->(c=toString(j);  
    c=substring(2,#c-2,c);
        alpha = value c;  
    accumulateMonomial = 1;
    for i from 0 to (#Facets-1)do (accumulateMonomial= accumulateMonomial*y_(append(alpha_(Facets_i),i)));
    listOfImages=append (listOfImages,accumulateMonomial);));
PSI=map(S,R,listOfImages); -- maps from R to S where the i-th variable goes to the i-th monomial in the list of images.
B=mutableMatrix (ZZ, numgens S, numgens R);
for j from 0 to ( #listOfImages-1) do(
for i from  0  to (numgens S-1) do(if gcd(S_i,listOfImages_j)!=1  then B_(i,j)=1));
A= matrix entries B;
M=toricMarkov(A);--needed for the M-S algorithm
IModel=toBinomial(M,R) 
    );




TEST\\\
r={1,1}
Facets={{0},{1}}
hmodel(r,Facets)
R
S
A
M
\\\

end
------------------------------------------------------------


restart
installPackage "PhylogeneticTrees"
viewHelp PhylogeneticTrees
