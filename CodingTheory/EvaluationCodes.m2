needsPackage "SRdeformations"
needsPackage "Polyhedra"
needsPackage  "Graphs"
needsPackage  "NAGtypes"

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



----------Reed–Muller-type code of degree d over a graph using our the algorithm of evaluationCode


evCodeGraph  = method(Options => {});

evCodeGraph (Ring,Matrix,List) := evCodeGraph  => opts -> (F,M,S) -> (
    -- input: a field, Incidence matrix of the graph , a set of polynomials.
    -- outputs: a monomial code over the list of points.
    
    -- We should check if all the points lives in the same F-vector space.
    -- Should we check if all the monomials lives in the same ring?
    
    P := entries transpose M;
 
    R := ring S#0;

    I := intersect apply(P,i->ideal apply(numgens R-1,j->R_j-i#j)); -- Vanishing ideal of the set of points.

    S = toList apply(apply(S,i->promote(i,R/I)),j->lift(j,R))-set{0*S#0}; -- Drop the elements in S that was already in I.

    G := matrix apply(P,i->flatten entries sub(matrix(R,{S}),matrix(F,{i}))) -- Evaluate the elements in S over the elements on P.
    
    
    new EvaluationCode from{
	symbol AmbientSpace => F^(#P),
	symbol Points => P,
	symbol VanishingIdeal => I,
	symbol PolynomialSet => S,
	symbol Code => image G
	}
    )

----------------------This an example of Reed-Muller-type code of degree 1--------------------
G = graph({1,2,3,4}, {{1,2},{2,3},{3,4},{4,3}})
B=incidenceMatrix G
S=ZZ/2[t0,t1,t2,t3]
evCodeGraph(ZZ/2,B,flatten entries basis(1,S))
------------------------------------------------------------------

    
    
       

-------Reed–Muller-type code of degree d over a graph using the function evaluate from package "NAGtypes"---------------


codeGraph  = method(TypicalValue => Module);


codeGraph (Matrix,ZZ,ZZ) := (M,d,p)->(
K:=ZZ/p;
tMatInc:=transpose M;
X:=entries tMatInc;
R:=K[t_(0)..t_(numgens target M-1)];
SetPoly:=flatten entries basis(d,R);
SetPolySys:=apply(0..length SetPoly-1, x->polySystem{SetPoly#x});
XX:=apply(X,x->point{x});
C:=apply(apply(SetPolySys,y->apply(0..length XX -1,x->(flatten entries evaluate(y,XX#x))#0)),toList);
G:=transpose matrix{C};
image G

new EvaluationCode from{
	symbol AmbientSpace => K^(#X),
	symbol IncidenceMatrix => M,
	symbol Code => image G
	}



)



----------------------This an example of Reed-Muller-type code of degree 4--------------------
G = graph({1,2,3,4}, {{1,2},{2,3},{3,4},{4,3}})
B=incidenceMatrix G
codeGraph(B,4,2)
------------------------------------------------------------------


----------The incidence matrix code of a Graph G-------
-- Recall that types of codes are Reed-Muller-type code of degree d=1 over a graph. 
--This a procedure for obtain an incidence matrix code of a Graph G
-- be sure that p is a prime number 


--this procedure computes the generatrix matrix of the code---


codeGraphInc = method(TypicalValue => Module);
-- M is the incidence matrix of the Graph G
--inputs: The incidence matrix of a Graph G, a prime number  
-- outputs: K-module

codeGraphInc (Matrix,ZZ):= (M,p)->(
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
codeGraphIncM(M,3)
---------------------------------------------





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


