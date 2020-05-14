--might be the input has to be transposed first
molien = W -> (
    weights := entries W;
    pos := apply(weights,w->apply(w,i->max(i,0)));
    neg := apply(weights,w->apply(w,i->-min(i,0)));
    n := length first weights;
    R := ZZ[t][z_1..z_n];
    posMono := apply(pos,e->product apply(gens R,e,(z,i)->z^i));
    negMono := apply(neg,e->product apply(gens R,e,(z,i)->z^i));
    den := product apply(negMono,posMono,(n,p)->n-p*t);
    num := product negMono;
    c := coefficient(num,den);
    expression(1_R)/expression(c)
    )