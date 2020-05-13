needsPackage "SRdeformations"
needsPackage "Polyhedra"

EvaluationCode = new Type of HashTable

evaluationCode = method(Options => {})

evaluationCode(Ring,List,List) := EvaluationCode => opts -> (F,P,S) -> (
    -- constructor for the evaluation code
    -- input: a field, a list of points, a set of polynomials.
    -- outputs: a monomial code over the list of points.
    
    -- We should check if all the points lives in the same F-vector space.
    -- Should we check if all the monomials lives in the same ring?
    
    R:= ring S#0;
    I:=intersect apply(P,i->ideal apply(numgens R-1,j->R_j-i#j));
    S=toList apply(apply(S,i->promote(i,R/I)),j->lift(j,R))-set{0*S#0};
    G:=transpose matrix apply(P,i->flatten entries sub(matrix(R/I,{S}),matrix(F,{i})));
    
    new EvaluationCode from{
	symbol AmbientSpace => F^(#P),
	symbol Points => P,
	symbol VanishingIdeal => I,
	symbol MonomialSet => S,
	symbol Code => image G
	}
    )

evaluationCode(Ring,List,Matrix) := EvaluationCode => opts -> (F,P,M) -> (
    -- Constructor for a evaluation (monomial) code.
    -- inputs: a field, a list of points (as a tuples) of the same length and a matrix of exponents.
    -- outputs: a F-module.
    
    -- We should check if all the points of P are in the same F-vector space.
    
    m:=numgens image M;
    R=F[t_1..t_m];
    S:=apply(numgens source M-1,i->vectorToMonomial(vector transpose M^{i},R));
    I:=intersect apply(P,i->ideal apply(m-1,j->R_j-i#(j)));
    S=toList apply(apply(S,i->promote(i,R/I)),j->lift(j,R))-set{0*S#0};
    M=matrix apply(S,i->first exponents i);
    G:=transpose matrix apply(P,i->flatten entries sub(matrix(R/I,{S}),matrix(F,{i})));
    
    new EvaluationCode from{
	symbol AmbientSpace => F^(#P),
	symbol Points => P,
	symbol VanishingIdeal => I,
	symbol ExponentsMatrix => M,
	symbol Code => image G
	}
    )
   
ToricCode = method(Options => {})

ToricCode(ZZ,Matrix) := EvaluationCode => opts -> (q,M) -> (
    -- Constructor for a toric code.
    -- inputs: size of a field, an integer matrix 
    -- outputs: the evaluation code defined by evaluating all monomials corresponding to integer 
    ---         points in the convex hull of the columns of M at the points of the algebraic torus (F*)^n
    
    F:=GF(q, Variable=>z);
    s:=set apply(q-1,i->z^i);
    m:=numgens target M;
    ss:=s;
    for i from 1 to m-1 do (
    	ss=set toList ss/splice**s;
    );
    P:=toList ss/splice;
    R:=F[t_1..t_m];
    Polytop:=convexHull M;
    L:=latticePolints Polytop;
    S:=apply(length(L),i->vectorToMonomial(vector L#i,R));
    evaluationCode(F,P,S);
)    
    
    
       
------------This an example of an evaluation code----------------------------------------
loadPackage "NormalToricVarieties"
loadPackage "NAGtypes"
loadPackage "Polyhedra"
loadPackage "SRdeformations"
loadPackage "RationalPoints"



d=2
q=2
S=3
F_2=GF 2-- Galois fiel
---------------------Defining  points in the Fano plane-----
A=affineSpace(S, CoefficientRing => F_2, Variable => y)
aff=rays A
matrix aff
--------------Points in Fano plane------------------
LL=apply(apply(toList (set(0..q-1))^**(S)-(set{0})^**(3),toList),x -> (matrix aff)*vector deepSplice x)
X=apply(LL,x->flatten entries x)
------------------Defining the ring and the vector space of  homogeneous polynomials with degree 2----------------------------------
R=F_2[vars(0..2)]
LE=apply(apply(toList (set(0..q-1))^**(hilbertFunction(2,R))-(set{0})^**(hilbertFunction(2,R)),toList),x -> basis(2,R)*vector deepSplice x)
Poly=apply(LE,x-> entries x)
-----------------------for each point p_k in Fano plane exists a polynomial f_i s.t f_i(p_k)not=0 ---------------------------------------
f={b^2,c^2,a^2,a^2,b^2,a^2,a^2}
----------------------------Using the package  numerial algebraic geometry----------------------------------
Polynum=apply(0..length LE-1, x->polySystem{LE#x#0})
PolyDem=apply(f,x->polySystem{x})
XX=apply(X,x->point{x})
---------------------Reed-Muller-type code of order 2------------------------------------------
C_d=apply(Polynum,y->apply(0..length f -1,x->(flatten entries evaluate(y,XX#x))#0/(flatten entries evaluate(PolyDem#x,XX#x))#0))
   
    
------------------------------------------------------------------------------------------------------------------------------
d=2
q=4
m=2

F_4=GF(4, Variable=>z)

M=matrix{{1,2,5},{4,5,6}}
P=convexHull M
L=latticePoints P
R=F_4[t_1..t_2]
vector L#1
f=vectorToMonomial(vector L#1,R)
numgens target M
I=ideal apply(m,j->R_j-1)

s=set apply(q-1,i->z^i)
ss=s
for i from 1 to m-1 do (
    ss=set toList ss/splice**s;
    )
P=toList ss/splice
length(P)
P#1
S=apply(length(L),i->vectorToMonomial(vector L#i,R))

evaluationCode F_4,PP,S
S
R


P#1
ToricCode(2,matrix{{1,2,5},{4,5,6}})
M
P
s
P#1
PP=apply(length(P),i->toList P#i)
PP#1
