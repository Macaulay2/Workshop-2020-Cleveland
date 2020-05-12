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

