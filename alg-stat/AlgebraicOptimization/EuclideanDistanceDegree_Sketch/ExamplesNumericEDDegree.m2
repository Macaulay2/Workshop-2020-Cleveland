--restart

--Open M2 in the directory containing NumericEDDegree.m2 or add the directory containing NumericEDDegree.m2 to the path. 
--path=prepend("/Users/jo/Dropbox/Euclidean distance degree/Projective varieties/ComputingEDDegree",path)
load"NumericEDDegree.m2"

--INPUTS: 

--storeBM2Files="/Users/jo/Desktop" 
----The input files are stored in the directory storeBM2Files which as a default is set to a temporary directory. Spaces are not allowed in the string. 
----If Bertini is installed to run with M2, then the runBertini commands and readFile will work. 
----The number of nonsingular-solutions equals the ED degree and found in bertini_session.log

--R 
----The coordinate ring of a codimension c variety X. 

--cod 
----The codimension of X 

--F 
----A list of polynomials that generate the ideal of X (assume X is generically reduced)

R = QQ[I][x0,x1,x2]; --I plays the role of the imaginary unit in Bertini. 
F = {x0^2*x2 - x1^2*(x1 + x2)} -- ED degree is 7
F = {x0^2*x1 -(x1 - I*x2)^2*x2};--ED degree is 7
F = {x0^3 - (I*x0^2 + x1^2)*x2};--ED degree is 6
UED = runBertiniEDDegree leftKernelUnitEDDegree(storeBM2Files,F)

