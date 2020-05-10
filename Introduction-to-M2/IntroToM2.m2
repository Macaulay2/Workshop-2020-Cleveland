--#######################
-- Introduction to M2
--#######################
--
--#######################
-- Running M2 in Terminal
-- 
-- One way to use M2 is via the termial. Just open it up and type `M2`
-- Here you can directly run code such as:
restart  
R = ZZ/101[x,y,z]
I = ideal"x2,y3,z4"

-- If you need a package you can just load one

needsPackage"Visualize" 
viewHelp Visualize

-- Some major drawbacks to working in the terminal are
--
-- 1. Ending or Restarting clears all variables (can't hit up arrow).
-- 2. Functions are a pain to debug and repeat. Try this:

f = n -> (
	if n == 1
	then "Hello, World!"
	else "D'oh!"  -- missing semi colon
	
	for i from 0 to 10 do (
	    print i
	    )
	) -- Don't drop this


--#######################
-- Running M2 in Emacs (this is how we code)
--  
-- To set up Emacs (or Aquamacs), run `setup()` in the M2 terminal session
-- Close terminal (and Emacs). 
--
-- 1. Open Emacs and create a new file called `test.m2` (remeber where you saved it!)
-- 2. Now type `CTRL + x, 3` (This is done in two steps. First type `CTRL + x` at the 
--    same time, then type `3`. Your screen should split into two windows.
-- 3. Use your mouse to activate the window for `test.m2` (`CTRL + x, o` for non-mouse 
--    people).
-- 4. To start Macaulay2, hit `F12`. This will start M2 in the other window!
-- 4.5 If you have a Mac, you need to change your keys. 
-- 5. The workflow is to code in the `test.m2`, and move (or execute) the code in the 
--    other window. 
--    To do this hit `F11`. Try this with the following function:

f = n -> (
	if n == 1
	then "Hello, World!"
	else "D'oh!"  -- missing semi colon
	
	for i from 0 to 10 do (
	    print i
	    )
	) -- Don't drop this

f 5 


--#######################
-- Let's create a file to code with.
-- 
-- 1. Create a new file and name it `whatever.m2`. It must have the `.m2` at the end. 
-- 2. Set up the file in the following format. This will be your testing ground.

end

restart
path = {"PATH/TO/YOUR/FILE/whatever.m2"}|path --Adds your file to the current path

load "whatever.m2" --loads the file whatever.m2


--#######################
-- Intro to functions
--
-- We have already created a function `f`. Now let's put it in our new file

awesomeFun = n -> ( -- Note the camel case. This is M2 convention.
	if n == 1
	then "Hello, World!"
	else "D'oh!"  -- missing semi colon
	
	for i from 0 to 10 do (
	    print i
	    )
	) 
    
-- Pro Tip 1: Before writing a function, determine the desired input and output
--    	    and write it down above your code. i.e.

-- input: An integer n
-- output: Either "Hello, World!" if `n=1`, and "D'oh!" otherwise. 
-- Description: The function will take in an integer and print out the 
--    	    	appropriate string. Nothing should be printed to the screen.
-- Example: awesomeFun(5) = "D'oh!"

-- Pro Tip 2: Test and retest your function with `assert`. I.e. 

assert ( awesomeFun 5 == "D'oh!")
assert ( awesomeFun 1 == "Hello, World!")
assert ( awesomeFun 0 == "D'oh!")


-- Pro Tip 3: Once you like your function, place it (along with your comments) 
--    	    above the `end`. You can now load it from the file without using `F11`!




--#######################
-- Intro to Methods
-- 
-- Functions are great, but Methods are better. Let's change our function `awesomeFun`
-- to a method. Using Pro Tip 1 and 2, we will write our input/outpt expectations before the
-- method as well as create tests.


-- input: An integer n
-- output: Either "Hello, World!" if `n=1`, and "D'oh!" otherwise. 
-- Description: The function will take in an integer and print out the 
--    	    	appropriate string. Nothing should be printed to the screen.
-- Example: awesomeFun(5) = "D'oh!"
--
awesomeMeth = method(TypicalValue => String) --Defines the method name and gives typical output
awesomeMeth ZZ := String => n -> (
    	local myStr; 
	
	if n == 1
	then myStr = "Hello, World!"
	else myStr = "D'oh!";
	
	return myStr;		
	)

-- use this notation when applying Pro Tip 3 an pasting above 
-- the `end`. We don't need this now, but you will need this 
-- format when placing your code in the package.
TEST /// 
assert ( awesomeMeth 5 == "D'oh!")
assert ( awesomeMeth 1 == "Hello, World!")
assert ( awesomeMeth 0 == "D'oh!")
///




--#######################
-- Options
--
-- You might want to pass options to a method. 
-- Copy this to `whatever.m2` and play with it!

awesomeMeth = method(TypicalValue => String, Options => {Hello => "Hello, World!", Doh => "D'oh!"}) 
awesomeMeth ZZ := String => opts -> n -> ( -- You need to add `opts ->`
    	local myStr; 
	
	if n == 1
	then myStr = opts.Hello -- Replace string
	else myStr = opts.Doh; -- Replace string
	
	return myStr; -- Returns desired result
	)




--#######################
-- viewHelp
--
-- Help is always given to those that ask. If we want help 
-- with a method/function, we can use `viewHelp`. Write this
-- in your whatever.m2. Does it go above or below the `end`?

viewHelp(apply)

L = apply(10, l -> l) 
L -- List from 0 to 10





--#######################
-- Problem 1:
-- Let's create a method called `powersList()` whose input is a List of 
-- numbers, an option called `Power`, and the output is the list of these 
-- to numbers raised to the power `Power`. I.e. 
--
-- powersList({1,2,3}, Power => 2) = {1,4,9}
--
-- (Don't worry about writing your input/output right now, 
-- but definitely do this in the wild. Tests are always a 
-- good ideal though.)
--
-- @bstone Push into breakout rooms.





--#######################
-- Problem 2:
-- Create a method called `myDegree()` whose input is a monomial ideal I
-- and an integer n. The output is the list of generators of degree n. If there
-- are no generators of degree n, then the output is an empty list.
-- 
-- Here is some code that can help.

R = ZZ/101[x,y,z]
I = ideal"x2,y3,z4"
gensList = flatten entries gens I
first degree(gensList#2)

viewHelp sort -- Look for `sort(List)`
viewHelp BasicList -- all functions you can run on a list

-- your method
myDegree = method()
myDegree (Ideal, ZZ) := List => (I, n) -> (
    
    -- your code here. Write and test this in `whatever.m2`
    
    )

-- Tests, test these in `whatever.m2`
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
