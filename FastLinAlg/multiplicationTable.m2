restart
randomAffinePolynomial=method()
randomAffinePolynomial(ZZ,Ring) := (d,R) -> (
    u := symbol u;
    kk:=coefficientRing R;
    S := kk[gens R|{u}];
    f := random(d,S);
    sub(sub(f,{u=>1}),R))
    
    


kk=ZZ/101
R=kk[x_1..x_4]
randomAffinePolynomial(4,R)
L={1,1,2,3}
I=ideal apply(L,d->randomAffinePolynomial(d,R))
dim I
d=degree I
b=matrix{ sort (entries basis(R^1/I))_0}

z=R_1

multiplicationTable=method()
multiplicationTable(RingElement,Ideal) := (z,I) -> (
    assert(dim I==0);
    R:= ring I;
    b:=matrix{ sort (entries basis(R^1/I))_0};
    d :=rank source b; 
    fz:=b*z%I;
    (b',m):=coefficients(fz);
    assert(b'*m==fz);
    assert(rank source b'==d);
    perm:=apply(rank source b,i->position((entries b')_0,c->c==b_(0,i)));
    assert(b==b'_perm);
    permutationMatrix:= matrix apply(d,i->apply(d,j->if perm_j==i then 1 else 0));
    M=permutationMatrix*map(R^d,R^d,m);
    assert(b*M-fz==0);
    M)

z=R_2
M=multiplicationTable(z,I)
    
chiz=z*id_(R^d)-M
det chiz%I
