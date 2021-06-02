allowableThreads = 12;

threadedSaturate = method();

threadedSaturate(Ideal, List) := (I1, L1) -> (    
    IList := apply(#L1, u -> new Ideal from I1);
    taskList := apply(#L1, i -> createTask(saturate, (IList#i, ideal(L1#i))) );
    apply(taskList, t -> schedule t);
    while true do (
	    nanosleep 1000000; --one thousandth of a second
        if (all(taskList, t -> isReady(t))) then break;
    );
    resultList = apply(taskList, t -> taskResult(t));
    return resultList
);

all(taskList, t -> isReady(t))