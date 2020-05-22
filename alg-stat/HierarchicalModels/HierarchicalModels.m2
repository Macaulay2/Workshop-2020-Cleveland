newPackage(
    "HierarchicalModels",
  Version => "0.1",
  Date => "May 12, 2020",
  Authors => {
    {Name => "Ben Hollering",
    Email => "bkholler@ncsu.edu",
    HomePage => "https://benhollering.wordpress.ncsu.edu/"},
    {Name => "Aida Maraj",
    Email => "aida.maraj@uky.edu",
    HomePage => "https://sites.google.com/view/aidamaraj"}
  },
  Headline => "A package for Hierarchical Models",
  DebuggingMode => true,
  PackageImports => {
      "FourTiTwo",
      "Polyhedra"
      }
)

export{"pRing"}

--Creates the ring the toric ideal lives in
probRing = method(Options => {});
probRing(List) :=  Ring => opts -> r -> (
    p := symbol p;
    R := QQ[p_(splice{#r:1})..p_r];
    R
    );


-- Creates the ring of parameters of a hierarchhical model
parameterRing = method(Options => {});
parameterRing(List, List) := Ring => opts -> (r, Facets) -> (
    parameters := {};
    S := QQ;
    y := symbol y;
    for i from 0 to (#Facets-1) do (
	S = tensor(S, QQ[y_(splice{i+1, #Facets_i:1})..y_(prepend(i+1, r_(Facets_i)))] ));
    S
    );

-- Produces the matrix that encodes the monomial map defining the toric ideal
hierMatrix = method(Options => {});
hierMatrix(List, List) := Matrix => opts -> (r, Facets) -> (
    R := probRing(r);
    S := parameterRing(r, Facets);
    B := mutableMatrix (ZZ, numgens S, numgens R);
    for j from 0 to (numgens R - 1) do(
	probIndex := last baseName (gens R)_j;
	for i from  0 to (numgens S - 1) do(
	    paramIndex := last baseName (gens S)_i;
	    if probIndex_(Facets_(paramIndex_(0) -1)) == drop(paramIndex, 1) then B_(i,j) = 1;
	    );
	);
        A := matrix entries B;
        A
    );

-- Computes the toric ideal of the hierarchical model defined by r and Facets using FourTiTwo
hierToric42 = method(Options => {pRing => null});
hierToric42(List, List) := Ideal => opts -> (r, Facets) -> (
    R := if opts.pRing === null then probRing(r) else opts.pRing;
    I := toricMarkov(hierMatrix(r, Facets), R);
    I
    )

-- Computes the dimension of the hierarchical model
hierDim = method();
hierDim(List,List) := (r,Facets) ->(
    n := #r;
    -- maybe cache faces
    Sim := delete({}, Facets / subsets // flatten // unique);
    dimI := Sim / (i -> i / (j -> r_j)) / product // sum;
    dimI
    )


-- Produces a ring map from the Probability ring to the Parameter Ring. The kernel of this map is the toric ideal of the hierarchical model
hierMap = method(Options => {});
hierMap(List, List) := List => opts -> (r, Facets) -> (
    R := probRing(r);
    S := parameterRing(r, Facets);
    y := (first baseName S_0);
    listOfImages := {};
    for var in gens(R) do (
	ind := last baseName var;
	facetIndices := for k from 0 to (#Facets-1) list prepend(k, ind_(Facets_k));
	listOfImages = append(listOfImages, product apply(facetIndices, k -> (y_k)_S ));
	);
    listOfImages
    );


-- Converts a binomial into a pair of tableau of its indices. 
-- Makes it more amenable for toric fiber products
binomialToTableau = method(Options => {});
binomialToTableau(RingElement) := List => opts -> f -> (
    tabs := f // terms / support / (i -> i / (j -> last baseName j));
    tabs
    )

-- Converts a pair of tableau to a binomial in the given ring R
tableauToBinomial = method(Options => {});
tableauToBinomial(List, Ring) := RingElement => opts -> (tabs, R) -> (
    p := first baseName (gens R)_0;    
    f := product(tabs_0 / (i -> p_i_R)) - product(tabs_1 / (i -> p_i_R));    
    f
    ) 



sortTableau = method(Options => {});
sortTableau(RingElement, List) := List => opts -> (f, S) -> (
    tabs := binomialToTableau(f);
    tabs = tabs / (j -> j / (i -> i_S | i));
    tabs = tabs / (j -> j // sort);
    tabs = tabs / (j -> j / (i -> drop(i, #S)));
    tabs
    )


liftBinomialTableau = method(Options => {});
liftBinomialTableau(List, List, Boolean) := List => opts -> (tabs, k, isFromDelta1) -> (   
    newTabs := {};
    newTab := {};
    
    if isFromDelta1 then (
	
	for i from 0 to 1 do (	
	    
	    newTab = {};
	    
	    for d from 0 to #k-1 do (
		
		
		newTab = append(newTab, tabs_i_d|k_d); 
		
		);
	    
	    newTabs = append(newTabs, newTab);
	    
	    );
	);
    
    if not isFromDelta1 then (
	
	for i from 0 to 1 do (	
	    
	    newTab = {};
	    
	    for d from 0 to #k-1 do (
		
		
		newTab = append(newTab, k_d|tabs_i_d); 
		
		);
	    
	    newTabs = append(newTabs, newTab);
	    
	    );
	);
	
    newTabs
    ) 


--Lifts a polynomial in Delta1 to Delta for reducible decomposition Delta = Delta1 \cup Delta2
liftHierPoly = method(Options => {});
liftHierPoly(RingElement, List, Ring, Boolean) := RingElement => opts -> (f, Delta, R, isFromDelta1) -> (
    r := Delta_0;
    S := Delta_1;
    tabs := sortTableau(f, S);
    kIndices := (set(splice{#r:1}..r))^**(#(tabs_0)) // toList;   
    tabs = kIndices / (k -> liftBinomialTableau(tabs, toList deepSplice k, isFromDelta1));    
    polys := tabs / (i -> tableauToBinomial(i, R));
    polys
    )




-- need the following:
-- lift poly from Delta2 probably using same methods above but adding some conditional logic
-- make methods put stuff in the appropriate rings
-- generate 2x2 minors associated to the tfp 
-- use liftHierPoly and 2x2 minors to generate the whole ideal




-----------------------------------------------------------
----- TESTS -----
-----------------------------------------------------------


-- This tests the method probRing by ensuring it has the right number of variables

TEST ///
r = {2,3,2}
R = probRing(r)
assert(dim R == product(r))
///

-- This tests the method parameterRing by ensuring it has the right number of variables

TEST ///
r = {2,3,2}
Delta = {{0,1}, {1,2}}
S = parameterRing(r, Delta)
assert(dim R == 8)
///

-- This tests the method hierMatrix function using a matrix that was computed by hand

TEST ///
r = {2,2,2}
Delta = {{0,1},{1,2}}
assert(hierMatrix(r, Delta) == matrix {{1, 1, 0, 0, 0, 0, 0, 0}, {0, 0, 1, 1, 0, 0, 0, 0}, {0, 0, 0, 0, 1, 1, 0, 0}, 
 {0, 0, 0, 0, 0, 0, 1, 1}, {1, 0, 0, 0, 1, 0, 0, 0}, {0, 1, 0, 0, 0, 1, 0, 0}, 
 {0, 0, 1, 0, 0, 0, 1, 0}, {0, 0, 0, 1, 0, 0, 0, 1}})
///

-- This tests the method hierToric42 by explicitly constructing the parameterization of the ideal
-- and computing the kernel of this parameterization. 

TEST ///
r = {2,2,3}
Delta = {{0,1}, {1,2}}
S = probRing(r)
R = parameterRing(r, Delta)
phi = map(R, S,  
    {y_{0, 1, 1}*y_{1, 1, 1}, 
     y_{0, 1, 1}*y_{1, 1, 2}, 
     y_{0, 1, 2}*y_{1, 2, 1}, 
     y_{0, 1, 2}*y_{1, 2, 2}, 
     y_{0, 2, 1}*y_{1, 1, 1}, 
     y_{0, 2, 1}*y_{1, 1, 2}, 
     y_{0, 2, 2}*y_{1, 2, 1},
     y_{0, 2, 2}*y_{1, 2, 2}})
assert(hierToric42(r, Delta) == ker phi)
///

-- This tests hierDim using a known example

TEST ///
r = {2,3,2}
Delta = {{0,1}, {1,2}}
assert(hierDim(r, Delta) == 8)
///


------------------------------------------------
--Documentation
-----------------------------------------------
beginDocumentation()

---------------------------------------
-- HierarchicalModels
--------------------------------------

doc///
Key
  HierarchicalModels
Headline
  A package to compute the algebraic objects related to a hierarchical model.
Description
  Text
    {\em HierarchicalModels} is a package for  the algebra and the geometry associated to hierarchical models.
    This package calculates the generating sets for toric ideals of hierarchical models using the package FourTiTwo.
    These ideals and their connection to hierarchical models are introduced in [1].
    In the case of reducible hierarchical models, we compute their generating set as toric fiber product presented in [2] and [3].
    Additionally, the package computes the dimesion of hierarchical  models, which is one less than the dimension of their ideals,
    using the formula in Theorem 2.6 [2].
 
 
    {\em References:}
 
    [1] Persi Diaconis and Bernd Sturmfels, {\em Algebraic Algorithms for sampling from conditional distributions},
    Ann. Statist. 26, 1998.
 
    [2] Serkan Hoşten and Seth Sullivant, { Gröbner bases and polyhedral geometry of reducible and cyclic models},
    J. Combin. Theory,  100, 277301, 2002.

    [3] Seth Sullivant, {\em Toric fiber products}, J. Algebra 316, no. 2, 560577, 2007.
 
----------------------------------------------------
///

end




doc///
 Key
         probRing
         (probRing,List)
    Headline
         Compute the probability ring where the ideals for a hierarchical model with a given number of states live
    Usage
        R=probRing(r)
    Inputs
       r: number of states of the random variables
         A set of positive integers
 
    Outputs
       R: Polynomial ring
          The polynomial ring with variables indexed by the  state space
     
    Example
      R = probRing({2,3,2})

   SeeAlso
    hierToric42
///
-------------------------------------------------------------
-- hierToric42
-------------------------------------------------------------
doc///
Key
   hierToric42
   (hierToric42,List,List)
       Headline
              Compute the ideal associated to the hierarchical model using the FourTiTwo package.
       Usage
               I = hierToric42(r,Facets)
       Inputs
              r: number of states of the random variables
      Facets: a set of maximal dependency relations among random variables, i.e. facets of a simplicial complex
       Description
              Text
         Computes the toric ideal using the function toricMarkov of the FourTiTwo package on the matrix whose columns parametrize the toric variety;
   the toric ideal is the kernel defined by this map.
       Example
              I = hierToric42({2,3,4},{{0,1},{1,2}})  
       SeeAlso
            probRing
hierMatrix    

///
----------------------------------
--hierMatrix
---------------------------------
doc///

Key
   hierMatrix
  (hierMatrix,List,List)
       Headline
              Compute the matrix that encondes the monomial map that has the ideal of hierarchical model as its kernel.
       Usage
               I = hierMatrix(r,Facets)
       Inputs
              r: number of states of the random variables
      Facets: a set of maximal dependency relations among random variables, i.e. facets of a simplicial complex
       Description
              Text
         Computes the matrix that encondes the monomial map that has the ideal of hierarchical model as its kernel.
       Example
              I = hierMatrix({2,3,4},{{0,1},{1,2}})  
       SeeAlso
            probRing
       hierToric42    

///
----------------------------------
--parameterRing
---------------------------------
doc///
Key
   parameterRing
  (parameterRing,List,List)
       Headline
              Compute the target ring  the monomial map that has the ideal of hierarchical model as its kernel.
       Usage
               I = parameterRing(r,Facets)
       Inputs
              r: number of states of the random variables
      Facets: a set of maximal dependency relations among random variables, i.e. facets of a simplicial complex
       Description
              Text
         Computes the target ring  the monomial map that has the ideal of hierarchical model as its kernel.
   The first index in the variables denotes the facet, and the rest of the index vector is in the states
   space defined by this facet.  
       Example
              I = parameterRing({2,3,4},{{0,1},{1,2}})  
       SeeAlso
            probRing
       hierToric42    
        hierMatrix

///
----------------------------------
--hierDim
---------------------------------
doc///
Key
   hierDim
  (hierDim,List,List)
       Headline
              Compute the dimension of the hierarchical model.
       Usage
               I = hierDim(r,Facets)
       Inputs
              r: number of states of the random variables
      Facets: a set of maximal dependency relations among random variables, i.e. facets of a simplicial complex
       Description
              Text
         Computes the dimension of the hierarchical model using a formula by Hoşten and Sullivant.
   The dimension of its ideal is one more than the dimension of the model.
       Example
              I = hierDim({2,3,4},{{0,1},{1,2}})  
       SeeAlso
       hierToric42    
 
///
----------------------------------
--margPolytope
---------------------------------
doc///
Key
   margPolytope
  (margPolytope,List,List)
       Headline
              Compute the marginal polytope associated  to  the hierarchical model.
       Usage
               I = margPolytope(r,Facets)
       Inputs
              r: number of states of the random variables
      Facets: a set of maximal dependency relations among random variables, i.e. facets of a simplicial complex
       Description
              Text
         Computes the marginal polytope associated to the hierarchical model. The marginal polytope is the convex
   hull of column vectors of the matrix that encondes the monomial map that has the ideal of hierarchical model as its kernel.
       Example
              I = margP({2,3,4},{{0,1},{1,2}})  
       SeeAlso
       hierToric42    
 
///
