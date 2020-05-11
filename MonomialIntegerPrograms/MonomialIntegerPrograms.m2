newPackage (
  "MonomialIntegerPrograms",
  Version=>"0.1",
  Authors => {{
      Name => "Lily Silverstein", 
      Email => "lsilverstein@cpp.edu",
      HomePage => "cpp.edu/faculty/lsilverstein"
      }},
  Headline => "using integer programming for fast computations with monomial ideals",
  Configuration => {
      "CustomPath" => ""
      },
  PackageImports => {"LexIdeals"},
  DebuggingMode => true
)

-------------
-- exports --
-------------
export {
    "codimensionIP",    
    "degreeIP",
    "dimensionIP",
    "monomialIdealsWithHilbertFunction",
    "topMinimalPrimesIP",
    "BoundGenerators",
    "FirstBetti",
    "GradedBettis",
    "KnownDim"
    }
exportMutable {
    "ScipPrintLevel"
    }

userPath = MonomialIntegerPrograms#Options#Configuration#"CustomPath";

ScipPath = if userPath == "" then(
    print("Using default executable name \"scip\".\nTo change this, load package using CustomPath option.");
    "scip") else userPath;

ScipPrintLevel = 1;
print("Current value of ScipPrintLevel is 1.")
-------------
-- methods --
-------------

codimensionIP = method();
codimensionIP (MonomialIdeal) := I -> (
    (dir, zimplFile, solFile, errorFile, detailsFile) := tempDirectoryAndFiles("codim");
    zimplFile << codimensionIPFormulation(I) << close;
    run(concatenate("(",ScipPath, 
	    " -c 'read ", zimplFile,
	    "' -c 'optimize'",
	    " -c 'display solution ",
	    "' -c quit;) 1>",
	    solFile,
	    " 2>",
	    errorFile));
    printStatement({zimplFile, solFile, errorFile, "Codim", dir});
    readScipSolution(solFile)
    )

dimensionIP = method();
dimensionIP (MonomialIdeal) := I -> (
    n := numgens ring I;
    n - codimensionIP(I)
    )

degreeIP = method( 
    Options => {KnownDim => -1}
    );
degreeIP (MonomialIdeal) := o -> I -> (
    objValue := if o.KnownDim >= 0 then o.KnownDim else dimensionIP(I);
    (dir, zimplFile, solFile, errorFile, detailsFile) := tempDirectoryAndFiles("deg");        
    if not isSquareFree I then(
	J := polarize(I);
	newDim := numgens ring J - numgens ring I + objValue;
    	zimplFile << degreeIPFormulation(J, newDim) << close;
	)
    else(
    	zimplFile << degreeIPFormulation(I, objValue) << close;
	);
    run(concatenate("(",ScipPath, 
	    " -c 'set emphasis counter'",
	    " -c 'set constraints countsols collect FALSE'",     	    
	    " -c 'read ", zimplFile, "'",
	    " -c 'count'",
	    " -c quit;)",
	    " 1>",
	    solFile,
	    " 2>",
	    errorFile
	    ));
    printStatement({zimplFile, solFile, errorFile, "Degree", dir});
    readScipCount(solFile)
    )

monomialIdealsWithHilbertFunction = method(
    Options => {
	BoundGenerators => -1,
	FirstBetti => "",
	GradedBettis => ""
	}
    );
monomialIdealsWithHilbertFunction (List, Ring) := o -> (D, R) -> (
    if not isHF D then error(
	"impossible values for a Hilbert function! Make sure your Hilbert function corresponds to the QUOTIENT of a homogeneous ideal"
	);
    if o.FirstBetti =!= "" and o.GradedBettis =!= "" then error(
	"cannot specify FirstBetti and GradedBettis options simultaneously"
	);
    n := numgens R;
    Dlist := apply(#D, i -> binomial(n+i-1,i)-D#i);
    if all(Dlist, d -> d==0) then return {monomialIdeal(0_R)};
    (dir, zimplFile, solFile, errorFile, detailsFile) := tempDirectoryAndFiles("hilbert");            
    zimplFile << hilbertIPFormulation(Dlist, n, o) << close;
    run(concatenate("(",ScipPath, 
	    " -c 'set emphasis counter'",
	    " -c 'set constraints countsols collect TRUE'",     
	    " -c 'read ", zimplFile,
	    "' -c 'count'",
	    " -c 'write allsolutions ",
	    solFile,
	    "' -c quit;)",
	    " 1>",
	    detailsFile,
	    " 2>",
	    errorFile));
    printStatement({zimplFile, solFile, errorFile, "Hilbert", dir});
    readAllMonomialIdeals(solFile, R)
    )

topMinimalPrimesIP = method(
    Options => {KnownDim => -1}
    );
topMinimalPrimesIP (MonomialIdeal) := o -> I -> (
    if I == monomialIdeal(1_(ring I)) then return I;
    if not isSquareFree I then I = polarize I;
    k := if o.KnownDim >= 0 then o.KnownDim else dimensionIP(I);
    (dir, zimplFile, solFile, errorFile, detailsFile) := tempDirectoryAndFiles("comps");        
    zimplFile << degreeIPFormulation(I, k) << close;
    run(concatenate("(",ScipPath, 
	    " -c 'set emphasis counter'",
	    " -c 'set constraints countsols collect TRUE'",     	    
	    " -c 'read ", zimplFile,
	    "' -c 'count'",
	    " -c 'write allsolutions ",
	    solFile,
	    "' -c quit;)",
	    " 1>",
	    detailsFile,
	    " 2>",
	    errorFile));
    printStatement({zimplFile, solFile, errorFile, "Minimal primes of codim "|k, dir});
    readAllPrimes(solFile, ring I)
    )

----------------------
-- internal methods --
----------------------

degreeIPFormulation = method();
degreeIPFormulation (List, ZZ, ZZ) := (A, n, knownDim) -> (
    concatenate(dimensionIPFormulation(A, n),"\n",
	"subto dim: sum <i> in N: X[i] == "|toString(knownDim)|";")
    )
degreeIPFormulation (MonomialIdeal, ZZ) := (I, knownDim) -> (
    degreeIPFormulation(monIdealToSupportSets(I), #gens ring I, knownDim)
    )

codimensionIPFormulation = method();
codimensionIPFormulation (List, ZZ) := (A, n) -> (
    concatenate({"set N := {0 .. ",toString(n-1),"};\n",
        "var X[N] binary;\n","minimize obj: sum <i> in N: X[i];\n",
        demark("\n", for i from 0 to #A-1 list(
	concatenate({"subto constraint",toString(i),": ",
	demark("+",apply(A#i, e -> "X["|toString(e)|"]")),
	" >= ",toString(1)|";"})))
    })
)
codimensionIPFormulation (MonomialIdeal) := (I) -> (
    codimensionIPFormulation(monIdealToSupportSets I, #gens ring I)
    )

dimensionIPFormulation = method();
dimensionIPFormulation (List, ZZ) := (A, n) -> (
    concatenate({"set N := {0 .. ",toString(n-1),"};\n",
        "var X[N] binary;\n","maximize obj: sum <i> in N: X[i];\n",
        demark("\n", for i from 0 to #A-1 list(
	concatenate({"subto constraint",toString(i),": ",
	demark("+",apply(A#i, e -> "X["|toString(e)|"]")),
	" <= ",toString(#(A#i)-1)|";"})))
    })
)
dimensionIPFormulation (MonomialIdeal) := (I) -> (
    dimensionIPFormulation(monIdealToSupportSets I, #gens ring I)
    )

hilbertIPFormulation = method(
    Options => {
	BoundGenerators => -1,
	FirstBetti => "",
	GradedBettis => ""
	}
    );
hilbertIPFormulation (List, ZZ) := o -> (D, n) -> (
    db := if o.BoundGenerators > 0 then o.BoundGenerators else #D-1;
    varsCommas := demark(",", toList vars(0..n-1));
    varsPluses := demark("+", toList vars(0..n-1));
    altVarsCommas := demark(",", toList vars(n..2*n-1));    
    altVarsPluses := demark("+", toList vars(n..2*n-1));
    bettiLines := "";
    if o.GradedBettis =!= "" then (
	G := o.GradedBettis; 
	if #G-1 > db then error("degrees of generators cannot be higher than degree bound");
	bettiLines = concatenate({
	    "\nset E := {0 .. maxGenD};\n",
	    "param Q[<degree> in E] := ", demark(", ",apply(#G, i -> "<"|i|">"|G#i)),";\n",
	    "subto specifiedBettis: forall <degree> in E do\n",
	    "    sum <", varsCommas, "> in M with ", varsPluses, " == degree: Y[",varsCommas,"] == Q[degree];\n"
	    })
    );
    if o.FirstBetti =!= "" then (
    	bettiLines = concatenate({"\nsubto totalBetti: sum <", varsCommas, "> in M: Y[",varsCommas,"] == ",toString o.FirstBetti, ";\n"})
	);
    concatenate({
	    "param maxD := ",toString(#D-1),";\n",
	    "param maxGenD := ",toString(db),";\n",
	    "set D := {0 .. maxD};\n",
	    "set M := {<",varsCommas,"> in ", demark("*", n:"D")," with ", varsPluses," <= maxD};\n",
	    "set BELOW[<",varsCommas,"> in M] := {<",altVarsCommas,"> in M with ",
	    demark(" and ", apply(n, i -> (toString vars(n+i))|"<="|(toString vars(i)))),
	    " and (",altVarsPluses," == ",varsPluses,"-1)};\n",
	    "set ABOVE[<",varsCommas,"> in M] := {<",altVarsCommas,"> in M with ",
	    demark(" and ", apply(n, i -> (toString vars(n+i))|">="|(toString vars(i)))),
	    " and (",altVarsPluses," == ",varsPluses,"+1)};\n",
	    "set ALLABOVE[<",varsCommas,"> in M] := {<",altVarsCommas,"> in M with ",
	    demark(" and ", apply(n, i -> (toString vars(n+i))|">="|(toString vars(i)))),
	    " and (",altVarsPluses," >= ",varsPluses,"+1)};\n",
	    "param P[<degree> in D] := ", demark(", ",apply(#D, i -> "<"|i|">"|D#i)),";\n",
	    "var X[M] binary;\n",
	    "var Y[M] binary;\n",
	    "minimize obj: X[", demark(",", n:"0"), "];\n",
	    "subto h: forall <degree> in D do\n",
	    "    sum <", varsCommas, "> in M with ", varsPluses, " == degree: X[",varsCommas, "] == P[degree];\n",
	    "subto ideal: forall <",varsCommas,"> in M with ",varsPluses," <= maxD-1 do\n",    
	    "sum <",altVarsCommas,"> in ABOVE[",varsCommas,"]: X[",altVarsCommas,"] - ",toString n,"*X[",varsCommas,"] >= 0;\n",
	    "subto gensInIdeal: forall <",varsCommas,"> in M do\n X[",varsCommas,"] - Y[",varsCommas,"] >= 0;\n",
	    "subto mingens: forall <",varsCommas,"> in M with ",varsPluses," <= maxD-1 do\n",
    	    "    forall <",altVarsCommas,"> in ALLABOVE[",varsCommas,"] do\n",
	    "        Y[",varsCommas,"] + Y[",altVarsCommas,"] <=1;\n",
	    "subto markGens: forall <",varsCommas,"> in M with ",varsPluses," <= maxD do\n",
	    "    sum <",altVarsCommas,"> in BELOW[",varsCommas,"]: X[",altVarsCommas,"] + Y[",varsCommas,"] - X[",varsCommas,"] >= 0;\n",
	    "subto genDegreeBound: forall <",varsCommas,"> in M with ",varsPluses," >= maxGenD+1 do\n",
	    "    Y[",varsCommas,"] == 0;",
	    bettiLines
	    })
    )

monIdealToSupportSets = method()
monIdealToSupportSets (MonomialIdeal) := (I) -> (
    apply(first entries mingens I, m -> apply(support m, r -> index r))
    )

printStatement = method();
printStatement (List) := L -> (
    (zimplFile, solFile, errorFile, nickname, dir) := toSequence L;
    if ScipPrintLevel >= 3 then print(get zimplFile);
    if ScipPrintLevel >= 4 then print(get solFile);
    if ScipPrintLevel >= 2 then print(get errorFile);
    if ScipPrintLevel >= 1 then print(nickname|" files saved in directory: "|dir);
)

readAllMonomialIdeals = method()
readAllMonomialIdeals (String, Ring) := (solFile, R) -> (
    n := numgens R;
    L := lines get solFile;
    L = apply(L, l -> separate(",",l));
    yIndices := positions(L#0, a -> select("Y",a)=!={});
    exps := for y in yIndices list drop(separate("#",L#0#y),1);
    mons := apply(exps, e -> product apply(n, i-> R_i^(value e_i)));
    L = drop(L, 1);
    allSolutions := apply(L, 
	ln -> monomialIdeal mons_(positions(ln_yIndices, i -> value i == 1))
	)
    )

readAllPrimes = method()
readAllPrimes (String, Ring) := (solFile, R) -> (
    n := numgens R;
    L := lines get solFile;
    mons := apply(select("X#([[:digit:]]+)", L#0), a -> R_(value substring(a, 2)));
    L = drop(L, 1);
    allSolutions := apply(L, 
	ln -> (
	    l := drop(separate(",",ln), 1);
	    l = drop(l, -1);
	    monomialIdeal for i from 0 to #l-1 list if value(l#i)==0 then mons#i else continue
	    )
	)
    )

readScipSolution = method();
readScipSolution (String) := solFile -> (
    solContents := get solFile;
    value first select(///objective value.[[:space:]]+([[:digit:]]+)///, ///\1///, solContents)
)

readScipCount = method();
readScipCount (String) := solFile -> (
    solContents := get solFile;
    value first select(///Feasible Solutions[[:space:]]+:[[:space:]]+([[:digit:]]+)///, ///\1///, solContents)
)

tempDirectoryAndFiles = method()
tempDirectoryAndFiles (String) := (bname) -> (
    dir := temporaryFileName();
    makeDirectory(dir);
    (dir, dir|"/"|bname|".zpl", dir|"/"|bname|".sol", dir|"/"|bname|".errors", dir|"/"|bname|".details")
)

-------------------
-- documentation --
-------------------

beginDocumentation()

doc ///
 Key
  MonomialIntegerPrograms
 Headline
  A package for fast monomial ideal computations using constraint integer programming
 Description
  Text
   This package uses integer program reformulations to perform faster
   computations on monomial ideals. The functions currently available
   are:
   
   @TO codimensionIP@--codimension of a monomial ideal
   
   @TO dimensionIP@--dimension of a monomial ideal
   
   @TO degreeIP@--degree of a monomial ideal, currently for squarefree only
   
   @TO topMinimalPrimesIP@--lists all minimal primes of maximum dimension
   
   @TO monomialIdealsWithHilbertFunction@--lists all monomial ideals in a given ring
   with a given Hilbert function
   
   Additional functions are in development.
  
   {\bf Installation and licensing information.}
   
   This package relies on the constraint integer program solver SCIP, which
   is available at @HREF"https://scip.zib.de/"@. This software is free for
   for academic, non-commercial purposes. Notice that SCIP is not distributed 
   under GPL, but under the ZIB Academic License (@HREF"https://scip.zib.de/academic.txt"@).
  
   To install SCIP, click the {\bf Download} tab on the left-hand side of the
   SCIP home page. The easiest method is to install prebuilt binaries (look for the heading
   {\em Installers (install the scipoptsuite in your computer, without source files)}.
   Choose the appropriate Linux, Windows, or MacOS file. The download is free,
   but you will be asked to submit your name and academic institution, to conform to
   the ZIB Academic License requirements, before the download begins.
  
   Under the heading {\em Source Code}, you can find the files for building
   from source. If building from source, you MUST include the source files for
   the modeling language Zimpl in order to use the Monomial Integer 
   Programs package. This will be included if you choose the download named 
   SCIP Optimization Suite, rather than the one named SCIP. Alternatively, download
   SCIP and then follow the {\em ZIMPL} link at the top of the home page to
   download the source files for Zimpl. When building SCIP, you will have to set
   a flag indicating that Zimpl should be built as well. For more information about
   building SCIP visit their online documentation (@HREF "https://scip.zib.de/doc-6.0.0/html/"@)
   and click on {\em Overview} -> {\em Getting started} ->
   {\em Installing SCIP}.
  
   An excellent user guide to using Zimpl can be found at 
   @HREF"https://zimpl.zib.de/download/zimpl.pdf"@. The author, Thorsten
   Koch, requests that research making use of this software please
   cite his 2004 PhD thesis, {\em Rapid Mathematical Programming}. The
   appropriate BibTeX entry can be found here: @HREF"https://zimpl.zib.de/download/zimpl.bib"@.
   Zimpl is distributed under GPL.
  
   Additionally, any research that uses SCIP needs a proper citation. See the
   {\bf How to Cite} tab on their home page.  
     
 SeeAlso
  codimensionIP
  degreeIP
  dimensionIP
  monomialIdealsWithHilbertFunction
  topMinimalPrimesIP
  symbol ScipPrintLevel
///

doc ///
 Key
  symbol ScipPrintLevel
 Headline
  adjust how much solving information is displayed in MonomialIntegerPrograms
 Description
  Text
   {\tt ScipPrintLevel} is a global symbol defined in Monomial Integer Programs 
   using @TO exportMutable@. After the package has been loaded, 
   the user can change the value of ScipPrintLevel at any time, 
   and the specified behavior will immediately apply to all 
   methods implemented in the package.

   Meaningful options for ScipPrintLevel are:
   
   {\bf 0} return the answers to computations only,  suppressing all other printing  
   
   {\bf 1} return the answer, and print to screen the location of the
   temporary directory which contains all the files related to the computation. By 
   default this is a subdirectory of {\tt /tmp/}, see @TO temporaryFileName@.

   {\bf 2} all the above, plus display any error or warning messages 
   generated by SCIP during the computation, i.e. anything sent by SCIP to stderr.
   See note below about warning messages.

   {\bf 3} all the above, plus print the problem file generated with 
   this package, used as the input to SCIP
      
   {\bf 4} all the above, plus print the solution file generated 
   by SCIP after solving the IP
   
   {\bf 5} all the above, plus print any other information sent by 
   SCIP to stdout during the solve, if any

   The default value of ScipPrintLevel, set every time
   the package is loaded, is 1.
   
   {\bf Why am I getting warnings/why does the solver report infeasibility for
   the degree count?}

   Computing the degree of a monomial ideal is done by counting the number of feasible solutions
   to a certain integer program. SCIP is generally designed to find a single optimal or feasible
   solution, so to count them it uses the following "trick": every time SCIP encounters a feasible
   solution or branch, it is recorded, then a constraint is added to make the new solution/branch infeasible, and the 
   search is continued. Eventually, all the solutions are recorded and the entire problem has been 
   made "infeasible." Thus the solving details for the degree problem print a final result of 
   "problem is infeasible," but the correct count has been taken. For more details, see the SCIP
   documentation page @HREF"https://scip.zib.de/doc/html/COUNTER.php"@.

 SeeAlso
  MonomialIntegerPrograms
///



doc ///
 Key
  degreeIP
  (degreeIP, MonomialIdeal)
  [degreeIP, KnownDim]
 Headline
  compute the degree of a monomial ideal using integer programming
 Usage
  d = degreeIP(I)
  d = degreeIP(I, KnownDim => k)
 Inputs
  I:MonomialIdeal
  k:ZZ
   if known, the dimension of the ideal (optional)
 Outputs
  d:ZZ
   the degree of $I$. That is, if $k$ is the maximum dimension of
   a coordinate subspace in the variety of $I$, then $degree(I)$ is
   the number of $k$-dimensional subspaces in the variety.
 Description
  Text
   If a {\tt KnownDim} is not provided, {\tt degreeIP} will first
   call {@TO dimensionIP@}($I$) to compute the dimension.
   
   An integer programming formulation of the degree problem is
   written to a temporary file directory, then the SCIP
   Optimization Suite is used to solve the IP. Solving details
   are written to a second file in the temporary directory, before
   outputting the answer.
  Example
   R = QQ[x,y,z,w,v];
   I = monomialIdeal(x*y*w, x*z*v, y*x, y*z*v);
   degreeIP(I, KnownDim => 3)
   degreeIP(I)
  Text
   The location of the temporary directory is printed to the
   screen.

   For more information about the SCIP warning messages, and related
   info on how SCIP counts solutions, see the very end of the
   @TO symbol ScipPrintLevel@ info page. 
 Caveat
  {\tt degreeIP} does not verify that a provided {\tt KnownDim} 
  is correct. Providing the wrong dimension will result in an 
  incorrect degree count (and possibly an infeasible program).
 SeeAlso
  (degree, Ideal)
  dimensionIP
  MonomialIntegerPrograms
  symbol ScipPrintLevel
///

doc ///
 Key
  dimensionIP
  (dimensionIP, MonomialIdeal)
 Headline
  compute the dimension of a monomial ideal using integer programming
 Usage
  k = dimensionIP(I)
 Inputs
  I:MonomialIdeal
 Outputs
  k:ZZ
   the dimension of $I$. That is, $k$ is the maximum dimension of
   a coordinate subspace in the variety of $I$.
 Description
  Text
   This function calls @TO codimensionIP@ and then returns $n$-codimensionIP($I$), where 
   $n$ is the number of variables in the polynomial ring where $I$ is defined.
   The integer programming input and output files created will therefore be named
   "codim.zpl", "codim.errors", etc. as with @TO codimensionIP@. 
  Example
   R = QQ[x,y,z,w,v];
   I = monomialIdeal(x*y*w, x*z*v, y*x, y*z*v);
   dimensionIP(I)
  Text   
   The location of input/output files for SCIP solving is printed
   to the screen by default. To change this, see @TO symbol ScipPrintLevel@.
  Example
   ScipPrintLevel = 0;
   J = monomialIdeal(x*y^3*z^7, y^4*w*v, z^2*v^8, x*w^3*v^3, y^10, z^10)
   dimensionIP(J) 
  Text
   The dimension of a monomial ideal is equal to the dimension
   of its radical. Therefore, when looking at the IP formulation written to
   the temporary file "codim.zpl", you will see that exponents are ignored.
 SeeAlso
  (dim, MonomialIdeal)
  codimensionIP
  MonomialIntegerPrograms
  symbol ScipPrintLevel
///

doc ///
 Key
  codimensionIP
  (codimensionIP, MonomialIdeal)
 Headline
  compute the codimension of a monomial ideal using integer programming
 Usage
  c = codimensionIP(I)
 Inputs
  I:MonomialIdeal
 Outputs
  c:ZZ
   the codimension of $I$
 Description
  Text
   The integer programming input and output files created are named
   "codim.zpl", "codim.errors", etc., and saved to a temporary directory.
   By default the location of the temporary directory is printed to the
   screen.
  Example
   R = QQ[x,y,z,w,v];
   I = monomialIdeal(x*y*w, x*z*v, y*x, y*z*v);
   codimensionIP(I)
  Text
   The verbosity of every function in the MonomialIntegerPrograms package is controlled with
   @TO symbol ScipPrintLevel@. For example, to suppress printing the name of
   the directory or any other information and simply return the answer, set
   {\tt ScipPrintLevel} to 0.
  Example
   ScipPrintLevel = 0;
   J = monomialIdeal(x*y^3*z^7, y^4*w*v, z^2*v^8, x*w^3*v^3, y^10, z^10)
   codimensionIP(J) 
  Text
   The codimension of a monomial ideal is equal to the codimension
   of its radical. Therefore, when looking at the IP formulation written to
   the temporary file "codim.zpl", you will see that exponents are ignored.
 SeeAlso
  (codim, MonomialIdeal)
  dimensionIP
  MonomialIntegerPrograms
  symbol ScipPrintLevel
///

doc ///
 Key
  monomialIdealsWithHilbertFunction
  (monomialIdealsWithHilbertFunction, List, Ring)
  [monomialIdealsWithHilbertFunction, BoundGenerators]
 Headline
  find all monomial ideals in a polynomial ring with a particular (partial or complete) Hilbert function
 Usage
  monomialIdealsWithHilbertFunction(L, R)
 Inputs
  L: List
   $\{h(0), h(1), \ldots, h(d)\}$, the values of a valid Hilbert function of a graded ring for degrees $0\ldots d$.
  R: Ring
   a polynomial ring
 Outputs
   :List
    all ideals $I$ of $R$ that satisfy $HF(R/I, i) = h(i)$ for all $0\le i\le d$
 Description
  Text
   Macaulay's Theorem characterizes all integer sequences which may be the Hilbert function of a graded ring. The package
   @TO LexIdeals@ has several functions based on this theorem, including the function @TO isHF@ which takes an integer 
   sequence and returns true if it is a valid (partial) Hilbert function, and false otherwise.
   
   When you call {\tt monomialIdealsWithHilbertFunction(L, R)}, first the function {\tt isHF L} is called to make sure
   that the problem is feasible. 
   
   Another useful function from the @TO LexIdeals@ package is @TO hilbertFunct@, which returns the first
   few values of the Hilbert function of a homogeneous ideal as a list. The default degree limit
   is 20, but this can be adjusted by the user.
  Example
   needsPackage("LexIdeals");
   R = QQ[x,y,z];
   I = monomialIdeal(x*y*z, x^2*y, y^2*z, x^3, y^3);
   hilbertFunct I
   L = hilbertFunct(I, MaxDegree => 5)
  Text
   As an example, let's find all monomial ideals of $R$, generated in degrees at
   most 5, with the same  Hilbert function as $I$. Because there are many, we'll print the first
   few only. The list of monomial ideals has no particular order.
  Example
   ScipPrintLevel = 0;
   M = monomialIdealsWithHilbertFunction(L, R);
   #M
   netList take(M, 5)
  Text
   This function can generate interesting data, such as all possible Betti tables of ideals with
   a given Hilbert function (and bounded generating degrees), along with their frequency.
  Example
   tally apply(M, m -> betti res m)   
  Text
   In the previous example, the list $L$ determines a unique Hilbert function, i.e.
   the only Hilbert function beginning with $\{1,3,6,5,4,4\}$ is the one
   which is constantly 4 after that point. However, uniqueness is not
   necessary to use this function. For instance, let's truncate the same Hilbert function
   at degree 4 and see what happens.
  Example
   L' = hilbertFunct(I, MaxDegree => 4)
   M' = monomialIdealsWithHilbertFunction(L', R);
   #M'
   tally apply(M', m -> hilbertFunct(m, MaxDegree => 10))
  Text
   By using a partial Hilbert function, we get all possible completions of the
   function that correspond to ideals generated in degrees at most 4, in our
   ring, along with the number of monomial ideals corresponding
   to each. We can see that the 306 ideals whose Hilbert function is
   eventually constantly 4 appear in the list, but there are others too.
   
   By default, the degrees of the generators are bounded by the length of the list.
   To set a different degree bound, use the {\tt BoundGenerators} option.
   The next example shows that there are 156 monomial ideals in $k[x,y,z]$ 
   with Hilbert function beginning $(1,3,4,2,1)$ generated in degree at most
   4, but only 48 generated in degree at most 3.
  Example
   #monomialIdealsWithHilbertFunction({1,3,4,2,1}, R)
   #monomialIdealsWithHilbertFunction({1,3,4,2,1}, R, BoundGenerators => 4)   
   #monomialIdealsWithHilbertFunction({1,3,4,2,1}, R, BoundGenerators => 3)
  Text
   At this point it is not possible to specify an entire degree sequence for
   the generators, but stay tuned.
 SeeAlso
  hilbertFunct
  isHF
  LexIdeals
  MonomialIntegerPrograms
  symbol ScipPrintLevel
///

doc ///
 Key
  topMinimalPrimesIP
  (topMinimalPrimesIP, MonomialIdeal)
  [topMinimalPrimesIP, KnownDim]
 Headline
  compute the minimal primes of maximum dimension using integer programming
 Usage
  topMinimalPrimesIP(I)
  topMinimalPrimesIP(I, KnownDim => k)
 Inputs
  I:MonomialIdeal
  k:ZZ
   if known, the dimension of the ideal (optional)
 Outputs
  L:List
   all minimal associated primes of dimension $k$
 Description
  Text
   If a {\tt KnownDim} is not provided, {\tt topMinimalPrimesIP} will first
   call {@TO dimensionIP@}($I$) to compute the dimension.
   
   The IP for this function is similar to the @TO degreeIP@ formulation,
   except that rather than count the number of solutions, SCIP
   uses a sparse data structure to enumerate all feasible solutions.
   
   The location of input/output files for SCIP solving is printed
   to the screen by default. To change this, see @TO symbol ScipPrintLevel@.
  Example
   R = QQ[x,y,z,w,v];
   I = monomialIdeal(y^12, x*y^3, z*w^3, z*v*y^10, z*x^10, v*z^10, w*v^10, y*v*x*z*w);
   ScipPrintLevel = 0;
   minimalPrimes(I)
   apply(oo, p -> dim p)
   topMinimalPrimesIP(I)
  Text
   Notice that if the dimension of a monomial ideal is $k$, each
   of the top minimal primes is generated by $n-k$ variables, where $n$
   is the number of variables in the polynomial ring.
 Caveat
  {\tt topMinimalPrimesIP} does not verify that a provided 
  {\tt KnownDim} is correct. Providing the wrong dimension will 
  result in an incorrect answer or an error.
 SeeAlso
  (topComponents, Ideal)
  degreeIP
  MonomialIntegerPrograms
  symbol ScipPrintLevel
///

doc ///
 Key
  "sample session in Monomial Integer Programs"
 Description
  Example
   R = QQ[x,y];
   L = {1,2,3,4,4,3,2,1,1};
   M = monomialIdealsWithHilbertFunction(L, R); 
   #M
   member(monomialIdeal(x^5*y, x^2*y^2, x*y^4, y^7), M)
  Text
   To look at all possible Betti tables for this Hilbert function:
  Example
   T = tally apply(M, m -> betti res m); 
   netList({keys T, values T}, Alignment => Center, HorizontalSpace => 1)
  Text
   To specify the total number of minimal generators:
  Example
   monomialIdealsWithHilbertFunction(L, R, FirstBetti => 2)
  Text
   The symbol {\tt ScipPrintLevel} controls how much of the inner workings of
   the package are visible to the user. At level 3, for instance, the IP passed
   to SCIP is printed to the screen, as are any warnings or errors sent to stderr
   by SCIP, before returning the answer.
  Example
   ScipPrintLevel = 3;
   monomialIdealsWithHilbertFunction(L, R, FirstBetti => 2)
   ScipPrintLevel = 0; --don't even display the temporary file directory
  Text
   To find the probability of having Hilbert function $L = \{1,2,3,4,4,3,2,1,1,...\}$:
  Example
   S = QQ[p];
   probL = sum apply(M, m -> p^(numgens m)*(1-p)^(-1+sum L));
   factor probL
   substitute(probL, p => 0.2)
  Text
   To find the probability of Hilbert function $L$ and graded Betti numbers $\{0,0,0,0,1,1,1,1,0\}$:
  Example
   B = {0,0,0,0,1,1,1,1,0};
   M' = monomialIdealsWithHilbertFunction(L, R, GradedBettis => B);
   probLB = #M'*p^(sum B)*(1-p)^(-1+sum L);
   factor probLB
   substitute(probLB, p => 0.2)
  Text
   Here is a more complicated example.
  Example
   R = QQ[x,y,z];
   needsPackage("RandomIdeals");
   I = monomialIdeal randomMonomialIdeal({3,3,3,4,4,4,5,5,5,6,6,6},R)
   H = apply(7, i -> hilbertFunction(i,I))
   elapsedTiming(M = monomialIdealsWithHilbertFunction(H, R);)
   #M
   B = for j from 0 to 6 list number(apply(flatten entries mingens I, i -> first degree i), i -> i==j)
   elapsedTiming(M' = monomialIdealsWithHilbertFunction(H, R, GradedBettis => B);)
   #M'
   tally(apply(M', m -> betti res m))
 SeeAlso
  MonomialIntegerPrograms
///

-----------
-- tests --
-----------

TEST /// --dim and codim
R = QQ[x_1..x_10];
I = monomialIdeal(x_1*x_4*x_7^3,x_1^2*x_8^3,x_1*x_2*x_8^2*x_9,x_1*x_4^2*x_9^2,x_1*x_7^2*x_9^2);
assert(
    codimensionIP(I) == codim I
    )
assert(
    dimensionIP(I) == dim I
    )
J = monomialIdeal(x_3^2*x_5*x_6*x_8,x_4^4*x_9,x_7^2*x_8^2*x_9,x_4*x_5*x_8*x_9^2,x_2^2*x_4*x_10^2);
assert(
    codimensionIP(J) == codim J
    )
assert(
    dimensionIP(J) == dim J
    )
K = monomialIdeal(x_4^5,x_2*x_3*x_5^2*x_7,x_2*x_5*x_7^3,x_2*x_3^2*x_7*x_8,x_1^4*x_9,x_4*x_6*x_8*x_9^2,x_1*x_4^3*x_10,x_1^2*x_5*x_6*x_10,x_3^3*x_7*x_10,x_1^2*x_7*x_9*x_10,x_1*x_5*x_8*x_10^2,x_2*x_7*x_8*x_10^2,x_3^2*x_10^3,x_3*x_9*x_10^3);
assert(
    codimensionIP(K) == codim K
    )
assert(
    dimensionIP(K) == dim K
    )
///

TEST /// --degree 
R = QQ[x_1..x_10];
I = monomialIdeal(x_1*x_4*x_7^3,x_1^2*x_8^3,x_1*x_2*x_8^2*x_9,x_1*x_4^2*x_9^2,x_1*x_7^2*x_9^2);
assert(
    degreeIP(I) == degree I
    )
J = monomialIdeal(x_3^2*x_5*x_6*x_8,x_4^4*x_9,x_7^2*x_8^2*x_9,x_4*x_5*x_8*x_9^2,x_2^2*x_4*x_10^2);
assert(
    degreeIP(J) == degree J
    )
K = monomialIdeal(x_4^5,x_2*x_3*x_5^2*x_7,x_2*x_5*x_7^3,x_2*x_3^2*x_7*x_8,x_1^4*x_9,x_4*x_6*x_8*x_9^2,x_1*x_4^3*x_10,x_1^2*x_5*x_6*x_10,x_3^3*x_7*x_10,x_1^2*x_7*x_9*x_10,x_1*x_5*x_8*x_10^2,x_2*x_7*x_8*x_10^2,x_3^2*x_10^3,x_3*x_9*x_10^3);
assert(
    degreeIP K == degree K
    )
///

TEST /// --hilbert
R=QQ[x,y,z];
assert(
    #monomialIdealsWithHilbertFunction({1,2,1,0},R)==9
    )
assert(
    #monomialIdealsWithHilbertFunction({1,3,4,2,1,0},R)==156
    )
R=QQ[x,y,z,w];
assert(
    #monomialIdealsWithHilbertFunction({1,4,3,1,0},R)==244
    )
assert(
    all(monomialIdealsWithHilbertFunction({1,4,10,19,31},R), I -> numgens I == 1)
    )
///

TEST /// --top min primes
R = QQ[x,y,z,w,v];
I = monomialIdeal(x*y*w, x*z*v, y*x, y*z*v);
assert(
    set(topMinimalPrimesIP(I))===set(minimalPrimes I)
    )
J = monomialIdeal(x^2*y*w^3*z, x*y*z*w*v, y*x^8*v, y^5*z*v, x^10, z^10, v^10);
assert(
    topMinimalPrimesIP(J) == {monomialIdeal(x,z,v)}
    )
K = monomialIdeal(x^2*y*w^3*z, x*y*z*w*v, y*x^8*v, y^5*z*v, y*x^10, v*z^10, w*v^10);
assert(
    set(topMinimalPrimesIP(K))===set(select(minimalPrimes(K), p -> 3 == dim p))
    )
L = monomialIdeal(y^12, x*y^3, z*w^3, z*v*y^10, z*x^10, v*z^10, w*v^10, y*v*x*z*w);
assert(
    set(topMinimalPrimesIP(L))===set(select(minimalPrimes(L), p -> 2 == dim p))    
    )
///

 

end--

restart
installPackage("MonomialIntegerPrograms")
viewHelp("sample session in Monomial Integer Programs")
needsPackage("MonomialIntegerPrograms")
