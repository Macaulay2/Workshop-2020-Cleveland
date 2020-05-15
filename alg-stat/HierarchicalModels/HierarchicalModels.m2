newPackage(
    "HierarchicalModels",
  Version => "0.1",
  Date => "May 12, 2020",
  Authors => {
    {Name => "Ben Hollering",
    Email => "bkholler@ncsu.edu",
    HomePage => "https://benhollering.wordpress.ncsu.edu/"},
    {Name => "Aida Maraj",
    Email => "ama363@g.uky.edu",
    HomePage => "https://sites.google.com/view/aidamaraj"}
  },
  Headline => "A package for Hierarchical Models",
  DebuggingMode => true,
  PackageImports => {
      "FourTiTwo",
      "Polyhedra"
      }
)

export{}

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
	S = tensor(S, QQ[y_(splice{i, #Facets_i:1})..y_(prepend(i, r_(Facets_i)))] ));
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
	    if probIndex_(Facets_(paramIndex_(0))) == drop(paramIndex, 1) then B_(i,j) = 1;
	    );
	);
        A := matrix entries B;
        A
    );

-- Computes the toric ideal of the hierarchical model defined by r and Facets using FourTiTwo
hierToric42 = method(Options => {});
hierToric42(List, List) := Ideal => opts -> (r, Facets) -> (
    R := probRing(r);
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
liftBinomialTableau(List, List) := List => opts -> (tabs, k) -> (
    
    newTabs := {};
    newTab := {};
    
    if isDelta1 then (
	
	for i from 0 to 1 do(
	
	newTab = {};
	
    	for d from 0 to #k-1 do (
	    
	    newTab = append(newTab, tabs_i_d|k_d); 
	
	    );
	
	newTabs = append(newTabs, newTab);
	
	); 
	
	
	)
    
    newTabs
    ) 


--Lifts a polynomial in Delta1 to Delta for reducible decomposition Delta = Delta1 \cup Delta2
liftHierPoly = method(Options => {});
liftHierPoly(RingElement, List, List, Ring) := RingElement => opts -> (f, r, S, R) -> (
    
    
    tabs := sortTableau(f, S);
    kIndices := (set(splice{#r:1}..r))^**(#(tabs_0)) // toList;
    p := first baseName (support f)_0;
    
    tabs = kIndices / (k -> liftBinomialTableau(tabs, toList deepSplice k));
    
    polys := tabs / (i -> tableauToBinomial(i, R));
    
    polys
    )

-- need the following:
-- lift poly from Delta2 probably using same methods above but adding some conditional logic
-- make methods put stuff in the appropriate rings
-- generate 2x2 minors associated to the tfp 
-- use liftHierPoly and 2x2 minors to generate the whole ideal





-----------------------------------------------------------------------------------
----- TESTS -----
-----------------------------------------------------------------------------------


-- This tests the method probRing by ensuring it has the right number of variables

TEST ///
r = {2,2,3}
R = probRing(r)
assert(dim R == product(r))
///

-- This tests the method parameterRing by ensuring it has the right number of variables

TEST ///
r = {2,2,3}
Delta = {{0,1}, {1,2}}
S = parameterRing(r, Delta)
assert(dim R == 17)
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
r = {2,2,3}
Delta = {{0,1}, {1,2}}
assert(hierDim(r, Delta) == 17)
///




end
