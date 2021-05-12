allowableThreads = 2;

threadedSaturate = method();

threadedSaturate(Ideal, List) := (I1, L1) -> (    
    taskList := apply(L1, z -> createTask(saturate, (I1, ideal(z))) );
    apply(taskList, t -> schedule t);
    while true do (
	    nanosleep 1000000; --one thousandth of a second
        if (all(taskList, t -> isReady(t))) then break;
    );
    resultList = apply(taskList, t -> taskResult(t));
    return resultList
);

all(taskList, t -> isReady(t))