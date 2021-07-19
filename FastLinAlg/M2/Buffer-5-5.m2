+ M2 --no-readline --print-width 158
Macaulay2, version 1.17.2.1
with packages: ConwayPolynomials, Elimination, IntegralClosure, InverseSystems, LLLBases, MinimalPrimes, PrimaryDecomposition, ReesAlgebra, Saturation,
               TangentCone

i1 : viewHelp contract
[GFX1-]: glxtest: libEGL initialize failed
[GFX1-]: glxtest: libEGL initialize failed

i2 : R = ZZ/101[x,y,z]

o2 = R

o2 : PolynomialRing

i3 : f = random(4, R)

        4      3       2 2       3      4     3       2          2      3       2 2          2      2 2        3        3      4
o3 = 42x  + 25x y + 12x y  + 5x*y  + 46y  + 2x z + 11x y*z - 6x*y z + 4y z - 39x z  + 25x*y*z  - 11y z  + 11x*z  + 37y*z  + 13z

o3 : R

i4 : contract(x, f)

        3      2         2     3     2                2         2        2      3
o4 = 42x  + 25x y + 12x*y  + 5y  + 2x z + 11x*y*z - 6y z - 39x*z  + 25y*z  + 11z

o4 : R

i5 : diff(x, f)

          3      2         2     3     2                2         2        2      3
o5 = - 34x  - 26x y + 24x*y  + 5y  + 6x z + 22x*y*z - 6y z + 23x*z  + 25y*z  + 11z

o5 : R

i6 : 42*4%101

o6 = 67

i7 : nanosleep(10000000000)
  C-c C-cstdio:7:1:(3): error: interrupted

i8 : nanosleep(1000000)

o8 = 0

i9 : time nanosleep(10000000)
     -- used 0.00001258 seconds

o9 = 0

i10 : time nanosleep(100000000)
     -- used 0.00001294 seconds

o10 = 0

i11 : time nanosleep(10000000000)
  C-c C-cstdio:11:1:(3): error: interrupted

i12 : time sleep(1)
     -- used 0.00001375 seconds

o12 = 0

i13 : elapsedTime sleep(1)
 -- 1.0001 seconds elapsed

o13 = 0

i14 : elapsedTime nanosleep(100000000)
 -- 0.1001 seconds elapsed

o14 = 0

i15 : elapsedTime nanosleep(1000000000)
 -- 1.0001 seconds elapsed

o15 = 0

i16 : help decompose

o16 = decompose
      *********

      Description
      ===========

      This function is a method function, defined in the core so multiple packages can add methods to it.

      See also
      ========

        * "MinimalPrimes" -- minimal primes and radical routines for ideals

      Ways to use decompose :
      =======================

        * "decompose(Ideal)" -- see "minimalPrimes" -- minimal primes of an ideal

      For the programmer
      ==================

      The object "decompose" is a method function with options.

o16 : DIV

i17 : J = intersect(ideal(x-1,y-2,z-3), ideal(x-0, y-5, z-6))

                                      2
o17 = ideal (y - z + 1, x + 34z - 2, z  - 9z + 18)

o17 : Ideal of R

i18 : basis J
stdio:18:1:(3): error: module given is not finite over the base

i19 : basis(R^1/J)

o19 = | 1 z |

o19 : Matrix

i20 : o19*y

o20 = | z-1 8z-18 |

o20 : Matrix

i21 : (o19*y)%J

o21 = | z-1 8z-18 |

o21 : Matrix

i22 : (o19*z)%J

o22 = | z 9z-18 |

o22 : Matrix

i23 : (o19*x)%J

o23 = | -34z+2 -z+6 |

o23 : Matrix

i24 : lift(o23, o19)
stdio:24:1:(3): error: no method found for applying lift to:
     argument 1 :  | -34z+2 -z+6 | (of class Matrix)
     argument 2 :  | 1 z |

i25 : extend(o23, o19)
stdio:25:1:(3): error: no method found for applying extend to:
     argument 1 :  | -34z+2 -z+6 | (of class Matrix)
     argument 2 :  | 1 z | (of class Matrix)

i26 : factor(o23, o19)
stdio:26:1:(3): error: no method found for applying factor to:
     argument 1 :  | -34z+2 -z+6 | (of class Matrix)
     argument 2 :  | 1 z | (of class Matrix)

i27 : help lift

o27 = lift -- lift to another ring
      ****************************

      Synopsis
      ========

        * Usage: 
              lift(f,R)
        * Inputs:
            * f, a ring element, ideal, or matrix
            * R, a ring
        * Optional inputs:
            * Verify => a Boolean value, default value true, whether to give an error message if lifting is not possible, or, alternatively, to return "null"
        * Outputs:
            * a ring element, ideal, or matrix, over the ring R

      Description
      ===========

      (Disambiguation: for division of matrices, which is thought of as lifting one homomorphism over another, see instead "Matrix // Matrix".  For lifting a
      map between modules to a map between their free resolutions, see "extend".)

      The ring R should be one of the base rings associated with the ring of f.  An error is raised if f cannot be lifted to R.

      The first example is lifting from the fraction field of R to R.

      +------------------------------------------+
      |  i1 : lift(4/2,ZZ)                       |
      |                                          |
      |  o1 = 2                                  |
      +------------------------------------------+
      |  i2 : R = ZZ[x];                         |
      +------------------------------------------+
      |  i3 : f = ((x+1)^3*(x+4))/((x+4)*(x+1))  |
      |                                          |
      |        2                                 |
      |  o3 = x  + 2x + 1                        |
      |                                          |
      |  o3 : frac R                             |
      +------------------------------------------+
      |  i4 : lift(f,R)                          |
      |                                          |
      |        2                                 |
      |  o4 = x  + 2x + 1                        |
      |                                          |
      |  o4 : R                                  |
      +------------------------------------------+

      Another use of lift is to take polynomials in a quotient ring and lift them to the polynomial ring.

      +-----------------------------------------------+
      |  i5 : A = QQ[a..d];                           |
      +-----------------------------------------------+
      |  i6 : B = A/(a^2-b,c^2-d-a-3);                |
      +-----------------------------------------------+
      |  i7 : f = c^5                                 |
      |                                               |
      |                   2                           |
      |  o7 = 2a*c*d + c*d  + 6a*c + b*c + 6c*d + 9c  |
      |                                               |
      |  o7 : B                                       |
      +-----------------------------------------------+
      |  i8 : lift(f,A)                               |
      |                                               |
      |                   2                           |
      |  o8 = 2a*c*d + c*d  + 6a*c + b*c + 6c*d + 9c  |
      |                                               |
      |  o8 : A                                       |
      +-----------------------------------------------+
      |  i9 : jf = jacobian ideal f                   |
      |                                               |
      |  o9 = {1} | 2cd+6c           |                |
      |       {1} | c                |                |
      |       {1} | 2ad+d2+6a+b+6d+9 |                |
      |       {1} | 2ac+2cd+6c       |                |
      |                                               |
      |               4       1                       |
      |  o9 : Matrix B  <--- B                        |
      +-----------------------------------------------+
      |  i10 : lift(jf,A)                             |
      |                                               |
      |  o10 = {1} | 2cd+6c           |               |
      |        {1} | c                |               |
      |        {1} | 2ad+d2+6a+b+6d+9 |               |
      |        {1} | 2ac+2cd+6c       |               |
      |                                               |
      |                4       1                      |
      |  o10 : Matrix A  <--- A                       |
      +-----------------------------------------------+

      Elements may be lifted to any base ring, if such a lift exists.

      +---------------------------------+
      |  i11 : use B;                   |
      +---------------------------------+
      |  i12 : g = (a^2+2*a-3)-(a+1)^2  |
      |                                 |
      |  o12 = -4                       |
      |                                 |
      |  o12 : B                        |
      +---------------------------------+
      |  i13 : lift(g,A)                |
      |                                 |
      |  o13 = -4                       |
      |                                 |
      |  o13 : A                        |
      +---------------------------------+
      |  i14 : lift(g,QQ)               |
      |                                 |
      |  o14 = -4                       |
      |                                 |
      |  o14 : QQ                       |
      +---------------------------------+
      |  i15 : lift(lift(g,QQ),ZZ)      |
      |                                 |
      |  o15 = -4                       |
      +---------------------------------+

      The functions lift and "substitute" are useful to move numbers from one kind of coefficient ring to another.

      +----------------------+
      |  i16 : lift(3.0,ZZ)  |
      |                      |
      |  o16 = 3             |
      +----------------------+
      |  i17 : lift(3.0,QQ)  |
      |                      |
      |  o17 = 3             |
      |                      |
      |  o17 : QQ            |
      +----------------------+

      A continued fraction method is used to lift a real number to a rational number, whereas "promote" uses the internal binary representation.

      +------------------------------------+
      |  i18 : lift(123/2341.,QQ)          |
      |                                    |
      |         123                        |
      |  o18 = ----                        |
      |        2341                        |
      |                                    |
      |  o18 : QQ                          |
      +------------------------------------+
      |  i19 : promote(123/2341.,QQ)       |
      |                                    |
      |         7572049608428139           |
      |  o19 = ------------------          |
      |        144115188075855872          |
      |                                    |
      |  o19 : QQ                          |
      +------------------------------------+
      |  i20 : factor oo                   |
      |                                    |
      |        3*811*39877*78045679        |
      |  o20 = --------------------        |
      |                  57                |
      |                 2                  |
      |                                    |
      |  o20 : Expression of class Divide  |
      +------------------------------------+

      For numbers and ring elements, an alternate syntax with "^" is available, analogous to the use of "_" for "promote".

      +------------------------------+
      |  i21 : .0001^QQ              |
      |                              |
      |          1                   |
      |  o21 = -----                 |
      |        10000                 |
      |                              |
      |  o21 : QQ                    |
      +------------------------------+
      |  i22 : .0001_QQ              |
      |                              |
      |          7378697629483821    |
      |  o22 = --------------------  |
      |        73786976294838206464  |
      |                              |
      |  o22 : QQ                    |
      +------------------------------+

      See also
      ========

        * "baseRings" -- store the list of base rings of a ring
        * "liftable" -- whether lifting to another ring is possible
        * "promote" -- promote to another ring

      Ways to use lift :
      ==================

        * "lift(BettiTally,type of ZZ)" -- see "BettiTally" -- the class of all Betti tallies
        * "lift(CC,type of QQ)"
        * "lift(CC,type of RR_*)"
        * "lift(CC,type of ZZ)"
        * "lift(Ideal,type of QQ)"
        * "lift(Ideal,type of RingElement)"
        * "lift(Ideal,type of ZZ)"
        * "lift(Matrix,type of CC_*,type of QQ)"
        * "lift(Matrix,type of CC_*,type of RR_*)"
        * "lift(Matrix,type of CC_*,type of ZZ)"
        * "lift(Matrix,type of Number)"
        * "lift(Matrix,type of QQ,type of QQ)"
        * "lift(Matrix,type of QQ,type of ZZ)"
        * "lift(Matrix,type of RingElement)"
        * "lift(Matrix,type of RR_*,type of QQ)"
        * "lift(Matrix,type of RR_*,type of ZZ)"
        * "lift(Matrix,type of ZZ,type of ZZ)"
        * "lift(QQ,type of QQ)"
        * "lift(QQ,type of ZZ)"
        * "lift(RR,type of QQ)"
        * "lift(RR,type of ZZ)"
        * "lift(ZZ,type of ZZ)"
        * "lift(Matrix,type of CC_*,type of CC_*)"
        * "lift(Matrix,type of RR_*,type of RR_*)"
        * "lift(Module,type of InexactNumber')"
        * "lift(Module,type of InexactNumber)"
        * "lift(Module,type of Number)"
        * "lift(Module,type of RingElement)"
        * "lift(MutableMatrix,type of InexactNumber')"
        * "lift(MutableMatrix,type of InexactNumber)"
        * "lift(MutableMatrix,type of Number)"
        * "lift(MutableMatrix,type of RingElement)"

      For the programmer
      ==================

      The object "lift" is a method function with options.

o27 : DIV

i28 : o23//o19

o28 = {0} | -34z+2 -z+6 |
      {1} | 0      0    |

              2       2
o28 : Matrix R  <--- R

i29 : o23

o29 = | -34z+2 -z+6 |

o29 : Matrix

i30 : o19

o30 = | 1 z |

o30 : Matrix

i31 : o19//o23

o31 = {0} | 0 -3 |
      {1} | 0 0  |

              2       2
o31 : Matrix R  <--- R

i32 : help (extend, ChainComplex, ChainComplex)
stdio:32:1:(3): error: expected (extend,ChainComplex,ChainComplex) to be a method

i33 : help extend

o33 = extend -- extend a module map to a chain map, if possible
      *********************************************************

      Synopsis
      ========

        * Optional inputs:
            * Verify => ..., default value true, extend a module map to a chain map, if possible

      Ways to use extend :
      ====================

        * "extend(ChainComplex,ChainComplex,Matrix)" -- extend a module map to a chain map, if possible

      For the programmer
      ==================

      The object "extend" is a method function with options.

o33 : DIV

i34 : chainComplex o19

                                               2
o34 = cokernel | y-z+1 x+34z-2 z2-9z+18 | <-- R
                                               
      0                                       1

o34 : ChainComplex

i35 : o19

o35 = | 1 z |

o35 : Matrix

i36 : ring o19

o36 = R

o36 : PolynomialRing

i37 : substitute(o19, R)
stdio:37:1:(3): error: ring map applied to module with relations: use '**' or 'tensor' instead

i38 : o19

o38 = | 1 z |

o38 : Matrix

i39 : sub(o19, R)
stdio:39:1:(3): error: ring map applied to module with relations: use '**' or 'tensor' instead

i40 : ring o19

o40 = R

o40 : PolynomialRing

i41 : cokernel o19

o41 = cokernel | 1 z y-z+1 x+34z-2 z2-9z+18 |

                             1
o41 : R-module, quotient of R

i42 : R

o42 = R

o42 : PolynomialRing

i43 : vars R

o43 = | x y z |

              1       3
o43 : Matrix R  <--- R

i44 : ideal R

o44 = ideal ()

o44 : Ideal of R

i45 : first entries vars o19
stdio:45:15:(3):[1]: error: no method found for applying vars to:
     argument   :  | 1 z | (of class Matrix)

i46 : first entries o19

o46 = {1, z}

o46 : List

i47 : ring ((first entries o19)#0)

o47 = R

o47 : PolynomialRing

i48 : ring ((first entries o19)#1)

o48 = R

o48 : PolynomialRing

i49 : keys o91
stdio:49:1:(3): error: expected a hash table, database, or dictionary

i50 : keys o19

o50 = {source, ring, RawMatrix, target, cache}

o50 : List

i51 : o19#source
stdio:51:4:(3): error: key not found in hash table

i52 : o19.source

       2
o52 = R

o52 : R-module, free, degrees {0..1}

i53 : o19.target

o53 = cokernel | y-z+1 x+34z-2 z2-9z+18 |

                             1
o53 : R-module, quotient of R

i54 : matrix entries o19

o54 = | 1 z |

              1       2
o54 : Matrix R  <--- R

i55 : M = matrix entries o19

o55 = | 1 z |

              1       2
o55 : Matrix R  <--- R

i56 : N = matrix entries o19

o56 = | 1 z |

              1       2
o56 : Matrix R  <--- R

i57 : N = matrix entries o23

o57 = | -34z+2 -z+6 |

              1       2
o57 : Matrix R  <--- R

i58 : extend(chainComplex M, chainComplex N, matrix{{1,0},{0,1}})
stdio:58:1:(3): error: maps not composable

i59 : extend(chainComplex M, chainComplex N, matrix{{1_R}})

           1             1
o59 = 0 : R  <--------- R  : 0
                | 1 |

           2                           2
      1 : R  <----------------------- R  : 1
                {0} | -34z+2 -z+6 |
                {1} | 0      0    |

o59 : ChainComplexMap

i60 : M//N

o60 = {1} | 0 -3 |
      {1} | 0 0  |

              2       2
o60 : Matrix R  <--- R

i61 : N//M

o61 = {0} | -34z+2 -z+6 |
      {1} | 0      0    |

              2       2
o61 : Matrix R  <--- R

i62 : M

o62 = | 1 z |

              1       2
o62 : Matrix R  <--- R

i63 : N

o63 = | -34z+2 -z+6 |

              1       2
o63 : Matrix R  <--- R

i64 : extend(chainComplex N, chainComplex M, matrix{{1_R}})
stdio:64:1:(3): error: map cannot be extended

i65 : coefficients M

o65 = (| z 1 |, {1} | 0 1 |)
                {0} | 1 0 |

o65 : Sequence

i66 : coefficients N

o66 = (| z 1 |, {1} | -34 -1 |)
                {0} | 2   6  |

o66 : Sequence

i67 : (coefficients N)#1

o67 = {1} | -34 -1 |
      {0} | 2   6  |

              2       2
o67 : Matrix R  <--- R

i68 : ((coefficients M)#1)*((coefficients N)#1)

o68 = {1} | 2   6  |
      {0} | -34 -1 |

              2       2
o68 : Matrix R  <--- R

i69 : (coefficients N)

o69 = (| z 1 |, {1} | -34 -1 |)
                {0} | 2   6  |

o69 : Sequence

i70 : ((coefficients N)#0)*((coefficients N)#1)

o70 = | -34z+2 -z+6 |

              1       2
o70 : Matrix R  <--- R

i71 : N

o71 = | -34z+2 -z+6 |

              1       2
o71 : Matrix R  <--- R

i72 : J

                                      2
o72 = ideal (y - z + 1, x + 34z - 2, z  - 9z + 18)

o72 : Ideal of R

i73 : basis(R^1/J)

o73 = | 1 z |

o73 : Matrix

i74 : J = intersect(ideal(x-1,y-2,z-3), ideal(x-0, y-5, z-6), ideal(x-5,y-0,z-0))

                                2                               2
o74 = ideal (x - 3y + 37z - 5, z  - 18y + 9z, y*z - 18y + 10z, y  - 17y + 10z)

o74 : Ideal of R

i75 : basis(R^1/J)

o75 = | 1 y z |

o75 : Matrix

i76 : (o75*x)%J

o76 = | 3y-37z+5 -4y+37z -6y+5z |

o76 : Matrix

i77 : coefficients ((o75*x)%J)
stdio:77:1:(3): error: expected target to be a free module

i78 : coefficients ((matrix entries o75)*x)%J)
stdio:78:40:(3): error: syntax error: unmatched )

i79 : coefficients (((matrix entries o75)*x)%J)

o79 = (| y z 1 |, {1} | 3   -4 -6 |)
                  {1} | -37 37 5  |
                  {0} | 5   0  0  |

o79 : Sequence

i80 : x*(id_(R^3))

o80 = | x 0 0 |
      | 0 x 0 |
      | 0 0 x |

              3       3
o80 : Matrix R  <--- R

i81 : x*(id_(R^3)) - (o79#1)

o81 = | x-3 4    6  |
      | 37  x-37 -5 |
      | -5  0    x  |

              3       3
o81 : Matrix R  <--- R

i82 : det(x*(id_(R^3)) - (o79#1))

       3      2
o82 = x  - 40x  - 7x

o82 : R

i83 : J

                                2                               2
o83 = ideal (x - 3y + 37z - 5, z  - 18y + 9z, y*z - 18y + 10z, y  - 17y + 10z)

o83 : Ideal of R

i84 : o82%J

o84 = - 10y - 42z - 1

o84 : R

i85 : isSubset(ideal(o82), J)

o85 = false

i86 : det(o79#1)

o86 = 0

o86 : R

i87 : coefficients (((matrix entries o75)*y)%J)

o87 = (| y z |, {1} | 1 17  18  |)
                {1} | 0 -10 -10 |

o87 : Sequence

i88 : coefficients (((matrix entries o75)*z)%J)

o88 = (| y z |, {1} | 0 18  18 |)
                {1} | 1 -10 -9 |

o88 : Sequence

i89 : coefficients ((matrix entries o75)*random(1, R))%J)
stdio:89:51:(3): error: syntax error: unmatched )

i90 : coefficients (((matrix entries o75)*(x+2*y-5*z))%J)

o90 = (| y z 1 |, {1} | 5   41  41 |)
                  {1} | -42 -34 30 |
                  {0} | 5   0   0  |

o90 : Sequence

i91 : det (o90#0)
stdio:91:1:(3): error: expected a square matrix

i92 : det (o90#1)

o92 = -10

o92 : R

i93 : l = x+2*y-5*z

o93 = x + 2y - 5z

o93 : R

i94 : id_(R^3)*
      l

o94 = | x+2y-5z 0       0       |
      | 0       x+2y-5z 0       |
      | 0       0       x+2y-5z |

              3       3
o94 : Matrix R  <--- R

i95 : id_(R^3)*l - (o90#1)

o95 = | x+2y-5z-5 -41        -41     |
      | 42        x+2y-5z+34 -30     |
      | -5        0          x+2y-5z |

              3       3
o95 : Matrix R  <--- R

i96 : det(id_(R^3)*l - (o90#1))

       3     2         2     3      2                 2         2        2      3      2              2                      2
o96 = x  + 6x y + 12x*y  + 8y  - 15x z + 41x*y*z + 41y z - 26x*z  + 49y*z  - 24z  + 29x  + 15x*y + 15y  + 13x*z + 26y*z + 18z  + 34x - 33y + 32z + 10

o96 : R

i97 : o96%J

o97 = 12y - 30z + 20

o97 : R

i98 : decompose S
stdio:99:1:(3): error: no method found for applying decompose to:
     argument   :  S (of class Symbol)

i99 : decompose J

o99 = {ideal (z, y, x - 5), ideal (z - 3, y - 2, x - 1), ideal (z - 6, y - 5, x)}

o99 : List
