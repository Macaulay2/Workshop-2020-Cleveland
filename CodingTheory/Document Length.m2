
  
document {
    Key => {length, (length, ZZ, LinearCode)},
    Headline => "Given a linear code compute the length.",
    Usage => "length(LinearCode)",
    "The funtion compute one of the most importat parameters of the code.",
    Inputs => {
	"C" => LinearCode => {"A linear code."}
	      },
    Outputs => {
	ZZ => {"The length of the code C"}
	       },
    EXAMPLE {
	"F = GF(5)",
	"R = F[x]",
 	"G = x-1",
 	"C1 = cyclicCode(F,G,8)",
	"length(C1)"
	  }
      }