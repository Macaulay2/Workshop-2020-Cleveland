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
	  "FourTiTwo",
	  "Polyhedra",
	  "SimplicialComplexes"
	  },
     )

export{}

probRing = method(Options => {})
probRing(List) :=  Ring => opts -> r -> (
    
    p := symbol p;
    
    QQ[x_(splice{#r:1})..p_r]
    )

hierMatrix = method(Options => {})
hierMatrix(List, List) := Matrix => opts -> (r, Facets) -> (
    
    
    
    
    )


--the method hmodel inputs a list of states of length n, and a list of maximal faces for a simplicial complex on a ground set [n]
--it produces the parameter ring R, target ring S, toric map A, ideal IModel,the exponent vectors of gens of the ideal M, and the marginal polytope for it.
hmodel = method()
hmodel(List,List) := (r,Facets) -> (
R=QQ[p_(splice{#r:0})..p_r];  
S=QQ; 
for i from 0 to (#Facets-1) do (S= tensor (S, QQ[y_(splice{#Facets_i:0,i})..y_(append (r_(Facets_i),i))]));
listOfImages={};
apply(flatten entries vars R, j->(c=toString(j);  
    c=substring(2,#c-2,c);
        alpha = value c;  
    accumulateMonomial = 1;
    for i from 0 to (#Facets-1)do (accumulateMonomial= accumulateMonomial*y_(append(alpha_(Facets_i),i)));
    listOfImages=append (listOfImages,accumulateMonomial);));
PSI=map(S,R,listOfImages);
B=mutableMatrix (ZZ, numgens S, numgens R);
for j from 0 to ( #listOfImages-1) do(
for i from  0  to (numgens S-1) do(if gcd(S_i,listOfImages_j)!=1  then B_(i,j)=1));
A= matrix entries B;
margP=convexHull(A);
M=toricMarkov(A);
IModel=toBinomial(M,R); 
    );


TEST\\\
r={1,1}
Facets={{0},{1}}
hmodel(r,Facets)
R
S
A
M
IModel
\\\

--creates the simplicial complex out of Facets where n=#r is the ground set.
makeSim = (Facets, n) -> (
    return unique flatten for f in Facets list delete(null, for a in subsets(n) list if isSubset(a,f) then a);
    )

end
------------------------------------------------------------
