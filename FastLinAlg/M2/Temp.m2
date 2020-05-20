-- -*- coding: utf-8 -*-
newPackage(
	"Temp",
    	Version => "1.0", 
    	Date => "May 12, 2020",
    	Authors => {
	     {Name => "Zhan Jiang", Email => "zoeng@umich.edu", HomePage => "http://www-personal.umich.edu/~zoeng/"},
	     },
    	Headline => "Temp Package",
	AuxiliaryFiles => false -- set to true if package comes with auxiliary files
    	)

-- Any symbols or functions that the user is to have access to
-- must be placed in one of the following two lists
export {
    "mtSearchPoints",
    "MyOption",
    "NumPoints",
    "NumThreads",
    "UsePregeneratedList"
    }
exportMutable {}

mtSearchPoints = method(TypicalValue => List, Options => {NumPoints => 100, NumThreads => 4, UsePregeneratedList => false});
mtSearchPoints(Ideal) := List => opts -> (I) -> (
    genList := first entries gens I;
    R := ring I;
    K := coefficientRing R;
    n := #gens R;
    
    local taskList;
    if (opts.UsePregeneratedList)
    then (
        randomPointsList := apply(
	                           opts.NumPoints * opts.NumThreads, 
			           (i)->(return getAPoint(n, K);)
	                         );
        taskList = apply(
	                  opts.NumThreads, 
			  (i)->(return createTask(
				  modifiedSearchPoints, 
				  (take(randomPointsList, {i * opts.NumPoints, (i + 1) * opts.NumPoints - 1}), R, genList)
				  );)
	                );
         )
    else (
	taskList = apply(
	                  opts.NumThreads, 
			  (i)->(return createTask(searchPoints, (opts.NumPoints, R, genList));)
	                );
         );
     
    apply(taskList, t -> schedule t);
    while true do (
        nanosleep 100000000;--this should be replaced by a usleep or nanosleep command.
        if (all(taskList, t -> isReady(t))) then break;
        );
    myList := apply(taskList, t -> taskResult(t));
    return myList;
);

--some helper functions

getAPoint = (n, K) -> (toList apply(n, (i) -> random(K)));

evalAtPoint = (R, genList, point) -> (
    K := coefficientRing R;
    n := #gens R;
    eval := map(K, R, point);
    for f in genList do ( 
	if not eval(f) == 0 
	then return false;
	);
    return true;
    );

modifiedSearchPoints = (pointsList, R, genList) -> (
    K := coefficientRing R;
    n := #gens R;
    for point in pointsList do (
	if evalAtPoint(R, genList, point)
	then return point
	);
    return {};
    );

searchPoints = (nn, R, genList) -> (
    K := coefficientRing R;
    n := #gens R;
    for i from 1 to nn do (
	point := getAPoint(n, K);
	if evalAtPoint(R, genList, point)
	then return point
	);
    return {};
    );

---

beginDocumentation()
document { 
    Key => Temp,
    Headline => " "
}


----- TESTS -----

TEST ///
assert(true)
///

TEST ///
///
   
end

-- Here place M2 code that you find useful while developing this
-- package.  None of it will be executed when the file is loaded,
-- because loading stops when the symbol "end" is encountered.

installPackage "Temp"
installPackage("Temp", RemakeAllDocumentation=>true)
check Temp

-- Local Variables:
-- compile-command: "make -C $M2BUILDDIR/Macaulay2/packages PACKAGES=SwitchingFields pre-install"
-- End:


