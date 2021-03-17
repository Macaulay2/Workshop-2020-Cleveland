Report on the paper RandomRationalPoints for JSAG

The paper describes a package which introduces a range of methods to produce random K-rational points on an affine or projective scheme V(I) defined over a finite field K.

It gives a nice decription of the method used by the package.

It works very well in sparse example, which however is not too surprising since
these tend to be rational or unirational in many cases. The key for these examples is to to use a sparse birational projection to a hypersuface, and then to intersect with a line.

Maybe the author should add comment why intersecting an absolutely irreducible hypersurface with a line has a K-rational point with high probability.

I recommend the paper for publication in JSAG.

In non-spase examples it does not work too well. Testing some examples, I got the impression that the bottleneck is actually the computation of the dimension of V(I).

Below I include some preliminary code which computes the dimension differently
with a probailistic approach, 
and frequently gets K rational points faster then it takes to compute the dimension  via GB. 

If they want the authors of the package are free to use these code altered in an improved version of their package.

Appendix: Some experimental code

restart
loadPackage("RandomRationalPoints",Reload=>true)
kk=ZZ/nextPrime 10^2


saturateInGenericCoordinates=method()
saturateInGenericCoordinates(Ideal):= I -> (
    x:=last gens ring I;
    saturate(I,ideal x))



randomPointViaMultiplicationTable=method(Options=>{IntersectionAttemps=>20})

randomPointViaMultiplicationTable(Ideal) := opts-> (I) -> (
    d:= (dimDegViaBezout I)_0;
    print d;
    randomPointViaMultiplicationTable(I,d,opts)
    )
    
randomPointViaMultiplicationTable(Ideal,ZZ) := opts-> (I,d) -> (
    -- Input: I, a homogeneous ideal, d its dimension
    --Output: a K-rational point on V(I) where K is  the finite ground field.
    if not isHomogeneous I then error "expect a homogeneous ideal";
    -- we cut down with a linear space to a zero-dimensional projective scheme
    -- and compute how the last two variables act on the quotient ring truncated  
    -- at the regularity. 
    -- In case of an absolutely irreducible I over K, we will find with 
    -- high probability a point, 
    -- since the determinant will has a linear factor in at least 50% of the cases
    S:= ring I;
    attemps:=1;
    while (
	L:=ideal random(S^1,S^{d-1:-1});
	--elapsedTime J=saturate(I+L);
	J:=I+L;
    	 Js:=saturateInGenericCoordinates J;
	 r:=degree ideal last (entries gens gb Js)_0;
        b1 :=basis(r+1,S^1/Js);
	 b2 :=basis(r+2,S^1/Js);
	j:=#gens S-d;
	xx:=(support (vars S%L))_{j-1,j};
	 m0:=contract(transpose matrix entries b2,matrix entries((xx_0*b1)%Js));
	m1:=contract(transpose matrix entries b2,matrix entries((xx_1*b1)%Js));
        M:=map(S^(rank target m0),S^{rank source m0:-1},xx_0*m1-xx_1*m0);
	 DetM:=(M^{0}*syz M^{1..rank source M-1})_(0,0);
	 -- computing DetM is the bottleneck
	 h:=ideal first first factor DetM;
	print degree h <<endl;
	degree h>1 and attemps<opts.IntersectionAttemps) do (attemps=attemps+1);
    if degree h >1 then return {};
     pt:=radical saturateInGenericCoordinates(h+Js);
    flatten (entries syz transpose jacobian pt)
)


dimDegViaBezout=method()

dimDegViaBezout(Ideal) := I -> (
    S:=ring I;
    lowerBound := max(dim S-rank source gens I,0);
    upperBound := dim S;
    mid:= null; increased=null;
    while upperBound - lowerBound >1 do (
	mid = floor((upperBound+lowerBound)/2);
    	L := ideal random(S^1,S^{mid-1:-1});
	Is := saturateInGenericCoordinates(I+L);
	if 
	Is==ideal 1_S 
	then (upperBound=mid;) else (lowerBound=mid;) ;
	--print mid
	);
    d:=lowerBound;
    L= ideal random(S^1,S^{d-1:-1});
    Is = saturateInGenericCoordinates(I+L);
    (d,degree Is)
    )
TEST ///
S=kk[y_0..y_19]
I=ideal random(S^1,S^{5:-1});
elapsedTime dimDegViaBezout I
elapsedTime dim I

I=ideal random(S^1,S^{4:-1,2:-2});
elapsedTime dimDegViaBezout I
elapsedTime dim I

S=kk[y_0..y_20]
I=ideal random(S^1,S^{8:-1});
assert((dimDegViaBezout I)_0==dim I)

///
kk=ZZ/nextPrime 10^2
kk=ZZ/nextPrime 10^3
kk = ZZ/7;
kk = ZZ/2;
S=kk[y_0..y_14]

I=minors(2,random(S^3,S^{5:-1}));
elapsedTime dimViaBezout(I)
elapsedTime (d,deg)=dimDegViaBezout(I)
elapsedTime d=dim I
elapsedTime randomPointViaMultiplicationTable(I,dim I)
elapsedTime randomPoints(I,Strategy=>LinearIntersection, Codimension=>8)
I=minors(2,genericMatrix(S,y_0,3,5));
dim I
elapsedTime pt=matrix{randomPointViaMultiplicationTable(I)}
elapsedTime randomPoints(I)

S=kk[y_0..y_9]
I=ideal random(S^1,S^{-2,-2,-2,-3})+(ideal random(2,S))^2;

elapsedTime (d,deg)=dimDegViaBezout(I) -- 0.317955 seconds elapsed
dim S -rank source gens I==d
elapsedTime randomPointViaMultiplicationTable(I,d)
elapsedTime randomPointViaMultiplicationTable(I)
cd=dim S -d
elapsedTime randomPoints(I,Strategy=>LinearIntersection,Codimension=>cd)
elapsedTime dim I -- 77.9314 seconds elapsed

elapsedTime randomPoints(I,Strategy=>LinearIntersection)
elapsedTime randomPointViaMultiplicationTable(I,d)


