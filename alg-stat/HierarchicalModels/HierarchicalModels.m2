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


-- Facets1 simplicial complex on [n]. 
-- Facets2 simplicial complex on [n + k]\[n] \cup S
-- need to check S \subset [n] is a face in each complex 
glueSimpComp(Facets1, Facets2, S)

hierTFP:= method(Options => {});
hierTFP(List, List, List) := Ideal => opts -> (Facets1, Facets2, S) -> (
    
    
    
    
    
    )
    
    


end