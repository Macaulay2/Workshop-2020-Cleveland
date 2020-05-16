 
cyclicCode = method (TypicalValue => LinearCode) 


cyclicCode(RingElement, ZZ) := LinearCode => (G,n) -> (
    --we assume that G is a polynomial over a GaloisField and G divides x^n-1.
    --Constructor for Cyclic Codes generated by a polynomial.
    -- input: The generating polynomial and the lenght of the code
    --outputs: a cyclic code defined by the initial polynomial .
    
    -- We should make a list of the coefficients of the polynomial. 
    ring G;
    x:=(gens ring G)#0;
    f := x^n-1;
    t:=quotientRemainder(G,f);
    g:=t#1;
    l:=toList apply(0.. (n-1),i->first flatten entries sub(matrix{{g//x^i}},x=>0));
    -- Generate the code using the method linearCode with the GaoilsField and L as argument. 
         L;=toList apply(toList(0..n-1), i -> apply(toList(0..n-1),j -> l_((j-i)%n)));
    return linearCode(coefficientRing (ring G),L)
    
       )

-*
GF(5)
G=x-1
cyclicCode(G,11)
    Code with Generator Matrix:  | -1 1  0  0  0  0  0  0  0  0  0  |
                                 | 0  -1 1  0  0  0  0  0  0  0  0  |
                                 | 0  0  -1 1  0  0  0  0  0  0  0  |
                                 | 0  0  0  -1 1  0  0  0  0  0  0  |
                                 | 0  0  0  0  -1 1  0  0  0  0  0  |
                                 | 0  0  0  0  0  -1 1  0  0  0  0  |
                                 | 0  0  0  0  0  0  -1 1  0  0  0  |
                                 | 0  0  0  0  0  0  0  -1 1  0  0  |
                                 | 0  0  0  0  0  0  0  0  -1 1  0  |
                                 | 0  0  0  0  0  0  0  0  0  -1 1  |
                                 | 1  0  0  0  0  0  0  0  0  0  -1 |

    


G(5)
f=x^2+x+1
cyclicCode(f,11)
GF(5)[x]
G=x-1
cyclicCode(G,11)

Code with Generator Matrix:       | 1 1 1 0 0 0 0 0 0 0 0 |
                                  | 0 1 1 1 0 0 0 0 0 0 0 |
                                  | 0 0 1 1 1 0 0 0 0 0 0 |
                                  | 0 0 0 1 1 1 0 0 0 0 0 |
                                  | 0 0 0 0 1 1 1 0 0 0 0 |
                                  | 0 0 0 0 0 1 1 1 0 0 0 |
                                  | 0 0 0 0 0 0 1 1 1 0 0 |
                                  | 0 0 0 0 0 0 0 1 1 1 0 |
                                  | 0 0 0 0 0 0 0 0 1 1 1 |
                                  | 1 0 0 0 0 0 0 0 0 1 1 |
                                  | 1 1 0 0 0 0 0 0 0 0 1 |
*-


document {
    Key => {cyclicCode, (cyclicCode, RingElement, ZZ)},
    Headline => "Generates a cyclic code of lenght n over the same GaloisField that the polynomial.",
    Usage => "cyclicCode(G, n)",
    Inputs => {
	"G" => RingElement => {"A polynomial over a GaloisField."},
	"n" => ZZ => {"The lenght of the code."}
	},
    
    Outputs => {
	  "C" => LinearCode => {"Cyclic Code with generating polynomial G and lenght n."}
	  },
      "G is a polynomial over a Gaoilsfield and n is an integer.",
      "Returns the Cyclic code over the same GaloisField that G and lenght n.",
      EXAMPLE{
	  "GF(5)[x]
	   G=x-1
	   C1=cyclicCode(G,8);",
	   "C1.ParityCheckMatrix"
	   }
       
	  }