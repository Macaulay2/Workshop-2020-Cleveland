newPackage(
  "HierarchicalModels",
  Version => "0.1", 
  Date => "1",
  Authors => {{Name => "a", 
  Email => "b", 
  HomePage => "c"}},
  Headline => "a",
  DebuggingMode => true
)

export {}

-- Code here
hierRing = method(Options => {});
hierRing(List) :=  Ring => opts -> r -> (
    
    x := symbol x;
    
    QQ[x_(splice{#r:1})..x_r]
    )






-- Documentation below

beginDocumentation()

-- template for package documentation
--  doc
--  Key
--    AlgebraicOptimization
--  Headline
--    TODO
--  Description
--    Text
--      Todo
--    Example
--      todo
--  Caveat
--  SeeAlso
--  


-- template for function documentation
--  doc
--  Key
--    todo
--  Headline
--    todo
--  Usage
--    todo
--  Inputs
--    todo
--  Outputs
--    todo
--  Consequences
--    todo
--  Description
--    Text
--      todo
--    Example
--      todo
--    Code
--      todo
--    Pre
--  Caveat
--  SeeAlso
  

 -- TEST 
  -- test code and assertions here
  -- may have as many TEST sections as needed
  

