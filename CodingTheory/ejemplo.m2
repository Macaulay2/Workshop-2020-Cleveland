K=GF(5)
S=K[x_1..x_3]

-- Trabajaremos sobre los conjuntos S_1=FF_5, S_2=S_3={0,1,2}.

An=ideal(x_1^5-x_1,x_2*(x_2-1)*(x_2-2),x_3*(x_3-1)*(x_3-2))

-- Los puntos donde evaluaremos

loadPackage "RationalPoints"

P=rationalPoints An

-- Tomemos el conjunto generador B={x_1^2*x_3,x_2}.

B={x_1^2*x_3,x_2}

for j from 1 to 3 do d_j=max apply(B,i->degree(x_j,i))

G=for i from 1 to 3 list x_i*B

C={}

for i from 0 to #G-1 do C=C|G#i

--COnstruir el ideal cuyo footprint será nuestro conjunto de información

I=ideal((new List from apply(1..3,i->x_i^(d_i+1)))|C)

M=flatten entries basis(S/I)

--Devolver los monomios al anillo de polinomios original
M=new List from apply(M,i->lift(i,S))

--Matriz del código

m=transpose(matrix( new List from apply(P,i->flatten entries sub(matrix(S,{M}),matrix{i}))))

degree(S/An)-degree(S/ideal(An,x_1*(x_1-1)*x_3))

J=monomialIdeal(An)

for i from 1 to #M list degree(S/An)-max new List from apply(subsets(M,i), j->degree(S/(J+ideal(j))))
