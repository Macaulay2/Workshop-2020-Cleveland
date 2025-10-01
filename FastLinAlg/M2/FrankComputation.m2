loadPackage("RandomPoints", Reload=>true, DebuggingMode=>true)
p = nextPrime(100);
R1=(ZZ/p)[a_{2, 3}, a_{1, 3}, a_{2, 4}, a_{1, 4}, a_{0, 2}, a_{3, 5}, a_{0, 3},a_{5, 7}, a_{2, 5}, a_{1, 5}, a_{0, 4}, a_{5, 8}, a_{2, 6}, a_{1, 6}, a_{5, 9},a_{3, 7}, a_{0, 5}, a_{5, 10}, a_{3, 8}, a_{2, 7}, a_{1, 7}, a_{0, 6}]

cR1=ideal(a_{0, 6},a_{5, 10},a_{5, 9}-a_{3, 7}+a_{0, 5},a_{1, 6},a_{2, 6},a_{5,8},a_{1, 5}+a_{0, 4},a_{3, 5}-a_{0, 3},a_{1, 4},a_{2, 4}+2*a_{0, 2},a_{5,7}*a_{2, 5}+a_{2, 5}^2+2*a_{2, 5}*a_{0, 4}+a_{2, 3}*a_{3, 8}-a_{1, 3}*a_{3,8}+a_{2, 3}*a_{2, 7}-a_{1, 3}*a_{2, 7}-a_{2, 3}*a_{1, 7}+a_{1, 3}*a_{1, 7})

debugLevel = 1
debugLevel = 0
randomPoints(cR1,Homogeneous=>false, Verbose=>true, ExtendField=>true)
randomPoints(cR1,Homogeneous=>true, Verbose=>true, ExtendField=>true)

randomPoints(cR1,Homogeneous=>true, Verbose=>true)

randomPoints(cR1, Homogeneous=>false, Strategy=>LinearIntersection)

randomPoints(cR1, Homogeneous=>true, Strategy=>LinearIntersection)



R1=(ZZ/101)[a_{8, 3}, a_{8, 4}, a_{2, 2}, a_{1, 2}, a_{0, 1}, a_{8, 6}, a_{3, 3}]

cR1=ideal(a_{1, 2}-a_{0, 1},a_{8, 4}-2*a_{2, 2},a_{8, 3},a_{8, 6}^2-a_{8, 6}*a_{3, 3}+a_{3, 3}^2)

randomPoints(cR1,Homogeneous=>false, Verbose=>true, ExtendField=>true)
