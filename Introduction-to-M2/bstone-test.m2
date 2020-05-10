
end

restart
path = {"~/GitHub/Workshop-2020-Cleveland/bstone-test.m2"}|path

load "bstone-test.m2" 

    











myDegree = method()
myDegree (Ideal, ZZ) := List => (I, n) -> (
    local L; local ans; local myDeg;
       
    L = flatten entries gens I;
    
    myDeg = sort apply(L, l -> if (first degree(l) == n) then l else 0);    
    myDeg = delete(0,myDeg);
    
    if myDeg == {}
    then return myDeg
    else return first myDeg
)    
