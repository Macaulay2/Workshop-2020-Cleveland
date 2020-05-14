needsPackage "SRdeformations"

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
    
    m=numgens image M;
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
   
------------This an example of an evaluation code----------------------------------------
loadPackage "NormalToricVarieties"
loadPackage "NAGtypes"

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



----------The incidence matrix code of a Graph G-------
needsPackage  "Graphs"
needsPackage  "NAGtypes"

--These are two procedure for obtain an incidence matrix code of a Graph G
-- be sure that p is a prime number 


--1-- this procedure computes the generatrix matrix of the code---
-- M is the incidence matrix of the Graph G

codeGrahpIncM = method(TypicalValue => Module);
codeGrahpIncM (Matrix,ZZ):= (M,p)->(
tInc:=transpose M;
X:=entries tInc;
R:=ZZ/p[t_(0)..t_(numgens target M-1)];
SetPol:=flatten entries basis(1,R);
SetPolSys:=apply(0..length SetPol-1, x->polySystem{SetPol#x});
XX:=apply(X,x->point{x});
C:=apply(apply(SetPolSys,y->apply(0..length XX -1,x->(flatten entries evaluate(y,XX#x))#0)),toList);
image transpose matrix{C}
)


--2-- this an alternative process. It computes all the points in the code. It computes all the linear forms. 

codeGrahpInc = method(TypicalValue => Sequence);
codeGrahpInc (Graph,ZZ):= (G,p)->(
tInc:=transpose incidenceMatrix G;
X:=entries tInc;
R:=ZZ/p[t_(0)..t_(lentgh vertexSet G-1)];
Poly1:=apply(apply(toList (set(0..p-1))^**(hilbertFunction(1,R))-(set{0})^**(hilbertFunction(1,R)),toList),x -> basis(1,R)*vector deepSplice x); 
Polynums1:=apply(0..length Poly1-1, x->polySystem{Poly1#x#0});
XX:=apply(X,x->point{x});
apply(Polynums1,y->apply(0..length XX -1,x->(flatten entries evaluate(y,XX#x))#0))
)














