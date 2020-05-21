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


T = (K,x) -> (
    
    if (coefficientRing ambient F === coefficientRing ambient K and (degree ambient F)%(degree ambient K)==0) then m=(degree ambient F)//(degree ambient K) else error "Not a subfield!";
    
    F := ring x;
    
    q := K.order;
    
    sum apply(m,i->x^(q^i))
    )


Trace = (F,K) -> (
    
     TrF := toList set apply(F.order-1,i->T(K,(F_0)^i));

     q := K.order;
     
     fi := position(TrF, i->#(toList set apply(q-1,j->i^j))==q-1);
     
     x := TrF#fi;
     
     TrF = {0}|toList apply(1..q-1,i->x^i);
     
     Tf := i -> (fi := position(TrF, j->T(K,i)==j); if fi== 0 then 0 else (K_0)^fi);
     
     Tf,map(F,K,{x})
     )

subfieldCode = (K,C) -> (
    
    F := C.BaseField;
    
    (Tf,invTF) := Trace(F,K);
    
    M := C.GeneratorMatrix;
  
    A := matrix apply(F.order-1,i->{(F_0)^i});
        
    M = M**A;
    
    Ms := matrix apply(entries M,i->apply(i,j->Tf(j)));
    
    Ms, invTF
    )