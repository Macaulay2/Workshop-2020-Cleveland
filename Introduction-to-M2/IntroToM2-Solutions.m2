
--#######################
-- Problem 1:
--
-- input: A List and an optional argument, myPower, as an integer
-- output: A List with the entries of the input list rased to myPower

powersList1 = method(TypicalValue => List, Options => {myPower => 2})
powersList1(List) := List => opts -> userList -> (
    local powersList;
    
    powersList = apply(userList, i -> i^(opts.myPower));
    
    return powersList
    )


powersList2 = method(TypicalValue => List, Options => {myPower => 2})
powersList2(List) := List => opts -> userList -> (
    
    apply(userList, i -> i^(opts.myPower)) -- the last output is automoatically returned

    )


powersList3 = method(TypicalValue => List, Options => {myPower => 2})
powersList3(List) := List => opts -> userList -> (
    --local mutantList; local l;
    
    mutantList := new MutableList from userList; -- allows you to change elements of  list
    
    l := #mutantList;
    for i from 0 to l-1 do (    
	mutantList#i = (mutantList#i)^(opts.myPower);
	);
    
    return new List from mutantList -- need to change back to a List
    )




--#######################
-- Problem 2:
-- input: A monomial ideal I and an integer n
-- output: The list of generators of degree n. If there are 
--     no generators of degree n, then the output is an empty list.
-- 
   
myDegree = method(TypicalValue => List) -- no options, but for documentation reasions we have `TypcicalValue` defined.
myDegree (Ideal, ZZ) := List => (I, n) -> ( -- two inputs here, and ideal and an integer
    local L; local myDeg;
       
    L = flatten entries gens I;
    
    myDeg = apply(L, l -> if (first degree(l) == n) then l else 0);    
    myDeg = delete(0,myDeg);
    
    if myDeg == {}
    then return myDeg
    else return first myDeg
)    


end

restart
path = {"~/GitHub/Workshop-2020-Cleveland/"}|path

load "bstone-test.m2" 
   
-- Problem 1 Tests
assert( {1,4,9} == powersList1({1,2,3}) )
assert( {1,4,9} == powersList2({1,2,3}) )
assert( {1,4,9} == powersList3({1,2,3}) )

assert( {1,8,27} == powersList1({1,2,3}, myPower => 3) )
assert( {1,8,27} == powersList2({1,2,3}, myPower => 3) )
assert( {1,8,27} == powersList3({1,2,3}, myPower => 3) )


-- Problem 2 Tests
R = ZZ/101[x,y,z]
I = ideal"x2,y3,z4"
assert( y^3 == myDegree (I,3))
assert( x^2 == myDegree (I,2)) 
assert( {} == myDegree(I,5))

S = ZZ/101[a,b,c]
J = ideal"x2y3z,xyz3,xy7z"
assert( x^2*y^3*z == myDegree (J,6))
assert( x*y*z^3 == myDegree (J,5))
assert( x*y^7*z == myDegree (J,9))
assert( {} == myDegree(J,2))
    




