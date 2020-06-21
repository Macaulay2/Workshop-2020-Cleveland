
-- input: An integer n
-- output: Either "Hello, World!" if `n=1`, and "D'oh!" otherwise. 
-- Description: The function will take in an integer and print out the 
--    	    	appropriate string. Nothing should be printed to the screen.
-- Example: awesomeFun(5) = "D'oh!"

awesomeFun = n -> ( -- Note the camel case. This is M2 convention.
	if n == 1
	then return "Hello, World!"
	else return "D'o!";
	
	for i from 0 to 10 do (
	    print i
	    )
	) 

-- input: An integer n
-- output: Either "Hello, World!" if `n=1`, and "D'oh!" otherwise. 
-- Description: The function will take in an integer and print out the 
--    	    	appropriate string. Nothing should be printed to the screen.
-- Example: awesomeFun(5) = "D'oh!"
--
awesomeMeth = method(TypicalValue => String, Options => {Hello => "Hello, World!", Doh => "D'oh!"}) 
awesomeMeth ZZ := String => opts -> n -> ( -- You need to add `opts ->`
    	local myStr; 
	
	if n == 1
	then myStr = opts.Hello -- Replace string
	else myStr = opts.Doh; -- Replace string
	
	return myStr; -- Returns desired result
	)


end

restart
path = {"~/GitHub/Workshop-2020-Cleveland/Introduction-to-M2/"}|path --Adds your file to the current path

load "brandens-test.m2" --loads the file whatever.m2

awesomeMeth( 1, Hello =>"Bye")

awesomeFun 5
assert ( awesomeMeth 5 == "D'oh!")
assert ( awesomeMeth 1 == "Hello, World!")
assert ( awesomeMeth 0 == "D'oh!")

