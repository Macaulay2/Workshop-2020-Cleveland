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
    
    R := ring S#0;

    I := intersect apply(P,i->ideal apply(numgens R-1,j->R_j-i#j)); -- Vanishing ideal of the set of points.

    S = toList apply(apply(S,i->promote(i,R/I)),j->lift(j,R))-set{0*S#0}; -- Drop the elements in S that was already in I.

    G := matrix apply(P,i->flatten entries sub(matrix(R,{S}),matrix(F,{i}))); -- Evaluate the elements in S over the elements on P.
    
    new EvaluationCode from{
	symbol AmbientSpace => F^(#P),
	symbol Points => P,
	symbol VanishingIdeal => I,
	symbol PolynomialSet => S,
	symbol Code => image G
	}
    )

evaluationCode(Ring,List,Matrix) := EvaluationCode => opts -> (F,P,M) -> (
    -- Constructor for a evaluation (monomial) code.
    -- inputs: a field, a list of points (as a tuples) of the same length and a matrix of exponents.
    -- outputs: a F-module.
    
    -- We should check if all the points of P are in the same F-vector space.

    m := numgens image M; -- number of monomials.

    R := F[t_1..t_m];

    I := intersect apply(P,i->ideal apply(m-1,j->R_j-i#(j))); -- Vanishing ideal of P.

    G := transpose matrix apply(entries M,i->toList apply(P,j->product apply(m,k->(j#k)^(i#k))));    


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
    L:=latticePoints Polytop;
    LL:=transpose matrix apply(L, i-> first entries transpose i);
    G:=matrix apply(entries LL,i->apply(P,j->product apply(m,k->(j#k)^(i#k))));
    
    new EvaluationCode from{
	symbol AmbientSpace => F^(#P),
	symbol ExponentsMatrix => LL,
	symbol Code => image G
	}
)   
    
----------------- Example of ToricCode method ----

M=matrix{{1,2,8},{4,5,6}}
T=ToricCode(4,M)

------------------    
    
    
       
------------This an example of an evaluation code----------------------------------------

needsPackage "NormalToricVarieties"
needsPackage "NAGtypes"

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


codeGrahpIncM = method(TypicalValue => Module);
-- M is the incidence matrix of the Graph G
--inputs: The incidence matrix of a Graph G, a prime number  
-- outputs: f-module

codeGrahpIncM (Matrix,ZZ):= (M,p)->(
K:=ZZ/p;
tInc:=transpose M;
X:=entries tInc;
R:=K[t_(0)..t_(numgens target M-1)];
SetPol:=flatten entries basis(1,R);
SetPolSys:=apply(0..length SetPol-1, x->polySystem{SetPol#x});
XX:=apply(X,x->point{x});
C:=apply(apply(SetPolSys,y->apply(0..length XX -1,x->(flatten entries evaluate(y,XX#x))#0)),toList);
G:=transpose matrix{C};
image G


  new EvaluationCode from{
	symbol AmbientSpace => K^(#X),
	symbol IncidenceMatrix => M,
	symbol Code => image G
	}


)

------------------
--This an example of a incidence matrix code---------
--Petersen graph
G=graph({1,2,3,4,5,6,7,8,9,10}, {{1,2},{1,3},{1,4},{1,5},{1,6},{2,3},{2,4},{2,5},{2,7},{3,4},{3,5},{3,6},{3,8},{4,5},{4,9},{5,10},{6,7},{6,10},{7,8},{8,9},{9,10}})
M=incidenceMatrix G
codeGrahpIncM(M,3)
---------------------------------------------


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


-------------------------------------------------------------------------


cartesianCode = method(Options => {})

cartesianCode(Ring,List,List) := EvaluationCode => opts -> (F,S,M) -> (
    --constructor for a cartesian code
    --input: a field, a list of subsets of F and a list of polynomials.
    --outputs: The evaluation code using the cartesian product of the elements in S and the polynomials in M.
    
    m := #S;
    R := ring M#0;
    I := ideal apply(m,i->product apply(S#i,j->R_i-j));
    P := set S#0;
    for i from 1 to m-1 do P=P**set S#i;
    P = apply(toList(P/deepSplice),i->toList i);
    Mm := toList apply(apply(M,i->promote(i,R/I)),j->lift(j,R))-set{0*M#0};
    G := matrix apply(P,i->flatten entries sub(matrix(R,{Mm}),matrix(F,{i})));
    
    new EvaluationCode from{
	symbol AmbientSpace => F^(#P),
	symbol Sets => S,
	symbol VanshingIdeal => I,
	symbol PolynomialSet => Mm,
	symbol Code => image G
	}
    )

cartesianCode(Ring,List,ZZ) := EvaluationCode => opts -> (F,S,d) -> (
    -- Constructor for cartesian codes.
    -- inputs: A field F, a set of tuples representing the subsets of F and the degree d.
    -- outputs: the cartesian code of degree d.
    m:=#S;
    R:=F[t_0..t_(m-1)];
    M:=apply(flatten entries basis(R/monomialIdeal basis(d+1,R)),i->lift(i,R));
    
    cartesianCode(F,S,M)
    )
   
cartesianCode(Ring,List,Matrix) := EvaluationCode => opts -> (F,S,M) -> (
    -- constructor for a monomial cartesian code.
    -- inputs: a field, a list of sets, a matrix representing as rows the exponents of the variables
    -- outputs: a cartesian code evaluated with monomials
    
    -- Should we add a second version of this function with a third argument an ideal? For the case of decreasing monomial codes.
    
    m := #S;
    R := F[t_0..t_(m-1)];
    I := ideal apply(m,i->product apply(S#i,j->R_i-j));
    P := set S#0;
    for i from 1 to m-1 do P=P**set S#i;
    P = apply(toList(P/deepSplice),i->toList i);
    G := transpose matrix apply(entries M,i->toList apply(P,j->product apply(m,k->(j#k)^(i#k))));
    
    new EvaluationCode from{
	symbol AmbientSpace => F^(#P),
	symbol VanishingIdeal => I,
	symbol ExponentsMatrix => M,
	symbol Code => image G
	}
    )


RMCode = method(TypicalValue => EvaluationCode)
    
RMCode(ZZ,ZZ,ZZ) := CartesianCode => (q,m,d) -> (
    -- Contructor for a generalized Reed-Muller code.
    -- Inputs: A prime power q (the order of the finite field), m the number of variables in the defining ring  and an integer d (the degree of the code).
    -- outputs: The cartesian code of the GRM code.
    
    F := GF(q);
    S := apply(q-1, i->F_0^i)|{0*F_0};
    S = apply(m, i->S);
    
    cartesianCode(F,S,d)
    )


