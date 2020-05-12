--Sagbi multiscrew computations
-- Elise Walker, Tim Duff , Jan 28 2020
restart
needsPackage "SubalgebraBases"

-*
the adjoint representation of SE(3,FF) is
SE(3,FF) -> GL(FF^6)
[R|t] -> [R  0]
         [TR R]
	 
(in suitable coordinates on the Lie algebra)
where T w = t x w represents the cross product

Sec 5.1 of Crook, Donelan studies invariants of the translational subgroup G that acts by

(w,v) -> (w,v+Tv) (*)

Want: FF[w,v]^G
Strategy: compute a SAGBI basis for FF[w,v+Tv] in FF[w,v,t] with an order that eliminates t

More generally: we may ask for FF[w_1, .., w_n, v_1, .., v_n]^G w/ acting diagonally as before
*-

restart
needsPackage "SubalgebraBases"
n=2 -- n=1,2 terminate w/ finite SAGBI bases for the given monomial order
R=QQ[t_1,t_2,t_3,w_(0,1)..w_(n-1,3),v_(0,1)..v_(n-1,3),MonomialOrder=>Eliminate 3]
V = transpose matrix apply(n, i -> {v_(i,1),v_(i,2),v_(i,3)})
W = transpose matrix apply(n, i -> {w_(i,1),w_(i,2),w_(i,3)})
T = matrix{
    {0,-t_3,t_2},
    {t_3,0,-t_1},
    {-t_2,t_1,0}
    }
I = map(R^3)
G = (I|0)||(T|I)
actT = G*(W||V)
algT = reshape(R^1,R^(6*n),actT)
elapsedTime wvtSag = subalgebraBasis(algT, PrintLevel=>1);
wvSag = selectInSubring(1,wvtSag)
netList flatten entries wvSag -- the invariants

-- needed to edit working version to get same result (n=1,2) for Strategy=>Engine
elapsedTime wvtSag = subalgebraBasis(algT, PrintLevel=>5, Strategy=>Engine);
