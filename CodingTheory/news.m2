path=path|{"~/Dropbox/Matemáticas/Macaulay2020/Workshop-2020-Cleveland/CodingTheory"}
loadPackage("CodingTheory",Reload=>true)


matrixProductCode = method(TypicalValue => LinearCode)

matrixProductCode(List,Matrix) := LinearCode => (L,A) -> (
    -- A product code from the list of codes L and the matrix A.
    -- Input: a list of s codes of the same length and a matrix A of s rows.
    -- Output: The linear code [L]A.
    
    if same(apply(L,i->length i)) then {} else error "Not all the codes are of the same length";
    
    s := #L;
    
    M := A^{0}**(L#0).GeneratorMatrix;
    
    for i from 1 to s-1 do M=M||(A^{i}**(L#i).GeneratorMatrix);
    
    linearCode(M)
    )


Trace = method(TypicalValue => Sequence)

Trace(Ring,Ring) := Sequence => (F,K) -> (
    -- A long way to compute the trace of the field.
    -- inputs: a field F of order q^m and a field K of order q.
    -- output: two maps: the trace of the field (communicating the field F->K) and a function that does the opposite path (K->F).
    
     if (coefficientRing ambient F === coefficientRing ambient K and (degree ambient F)%(degree ambient K)==0) then m=(degree ambient F)//(degree ambient K) else error "Not a subfield!";
     
     q := K.order;
     
     T := e -> sum apply(m,i->e^(q^i));
          
     TrF := toList set apply(F.order-1,i->T((F_0)^i));

     fi := position(TrF, i->#(toList set apply(q-1,j->i^j))==q-1);
     
     x := TrF#fi;
     
     TrF = {0}|toList apply(1..q-1,i->x^i);
     
     Tf := i -> (fi := position(TrF, j->T(i)==j); if fi== 0 then 0 else (K_0)^fi);
     
     Tf,map(F,K,{x})
     )

subfieldCode = method(TypicalValue=>Sequence)

subfieldCode(Ring,LinearCode) := (K,C) -> (
    -- A subfield subcode using Delsarte's Theorem.
    -- inputs: a code C and a subfield K of its base field.
    -- outputs: the subfield subcode and the map to identify K as a subset of F.
    
    F := C.BaseField;
    
    (Tf,invTF) := Trace(F,K);
    
    M := C.GeneratorMatrix;
  
    A := matrix apply(F.order-1,i->{(F_0)^i});
        
    M = M**A;
    
    Ms := matrix apply(entries M,i->apply(i,j->Tf(j)));
    
    Ms = transpose groebnerBasis transpose Ms;
    
    linearCode(Ms), invTF
    )