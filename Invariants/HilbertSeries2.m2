--INPUT: a matrix W of weights for a torus action
--OUTPUT: the Hilbert series of the ring of invariants
--IDEA: the Hilbert series is 1/product of (1-m*t)
--where m=m(z) is a Laurent monomial
--We separate positive and negative parts and do some
--algebra to isolate the part constant in the z's
molien = W -> (
    --transpose the matrix, but why? is there a dual action?
    weights := entries transpose W;
    --separate positive and negative parts of weights
    pos := apply(weights,w->apply(w,i->max(i,0)));
    neg := apply(weights,w->apply(w,i->-min(i,0)));
    n := length first weights;
    R := ZZ[t][z_1..z_n];
    --create monomials from positive and negative parts of weights
    posMono := apply(pos,e->product apply(gens R,e,(z,i)->z^i));
    negMono := apply(neg,e->product apply(gens R,e,(z,i)->z^i));
    --form denominator and numerator of the Hilbert series
    den := product apply(negMono,posMono,(n,p)->n-p*t);
    num := product negMono;
    c := coefficient(num,den);
    --return as a Divide expression
    expression(1_R)/expression(c)
    )