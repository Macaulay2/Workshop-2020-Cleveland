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
    "NumPointsToCheck",
    "NumThreads",
    "UsePregeneratedList"
    }
exportMutable {}

mtSearchPoints = method(TypicalValue => List, Options => {NumPointsToCheck => 100, NumThreads => 4, UsePregeneratedList => false});
mtSearchPoints(Ideal) := List => opts -> (I) -> (
    genList := first entries gens I;
    R := ring I;
    K := coefficientRing R;
    n := #gens R;
    
    local taskList;
    if (opts.UsePregeneratedList)
    then (
        randomPointsList := apply(opts.NumPointsToCheck * opts.NumThreads, (i)->( 
	    return getAPoint(n, K);
	    )
	);
        taskList = apply(opts.NumThreads, (i)->(
	    return createTask(modifiedSearchPoints, (take(randomPointsList, {i * opts.NumPointsToCheck, (i + 1) * opts.NumPointsToCheck - 1}), n, K, R, genList));
	    )
	);
    )
    else (taskList = apply(opts.NumThreads, (i)->(
	    return createTask(searchPoints, (opts.NumPointsToCheck,n,K,R,genList));
	    )
	);
    );
    apply(taskList, t -> schedule t);
    while true do (
        nanosleep 100000000;--this should be replaced by a usleep or nanosleep command.
        if (all(taskList, t->isReady(t))) then break;
        );
    myList := apply(taskList, t -> taskResult(t));
    return myList;
);

--some helper functions

getAPoint = (n,K) -> (toList apply(n, (i)->random(K)));

evalAtPoint = (n, K, R, genList, point) -> (
    eval := map(K, R, point);
    for i in genList do ( 
	if not eval(i) == 0 
	then return false;
	);
    return true;
    );

modifiedSearchPoints = (pointsList, n, K, R, genList) -> (
    for point in pointsList do (
	if evalAtPoint(n, K, R, genList, point)
	then return point
	);
    return {};
    );

searchPoints = (nn, n, K, R, genList) -> (
    for i from 1 to nn do (
	point := getAPoint(n, K);
	if evalAtPoint(n, K, R, genList, point)
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


