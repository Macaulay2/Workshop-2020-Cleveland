ToricHilbertSeries = method()

ToricHilbertSeries (Matrix, ZZ) := Thing => (W, d) -> (
    r := numRows W;
    n := numColumns W;
    W=-W;
    R=QQ[z_1..z_n,t, Inverses => true, MonomialOrder=>Lex];
    for i from 1 to n do(  
	m_i=1;
	for j from 1 to r do(
	    m_i=m_i*z_j^(W_(j-1,i-1));
	    );	
	);
   for i from 1 to n do(
       f_i=1;
       for j from 1 to d do(
	   f_i=f_i+(m_i*t)^j;	   
	   );
       );
   g=1;
   for i from 1 to n do(
       g=g*f_i;
       );
   L=select(terms g, term -> isSubset(support(term),{t}));
   l=#L;
   h=0;
   for i from 0 to l-1 do(
       if first degree(L#i)<= d then(
       h=h+L#i;
       );
       );
    return h
    )


TEST ///
W=matrix {{-1,0,1},{0,-1,1}};
d=9;
s=ToricHilbertSeries(W,d)
R= ring s;
series=1+t^3+t^6+t^9
assert(s === series)
///


