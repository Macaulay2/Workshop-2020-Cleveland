--unrolling the contents of sagbiEng on a simple example
restart
debug Core
needsPackage "SubalgebraBases" -- ask if this doesn't work for you
R=QQ[x,y]
G=matrix{{x+y,x*y,x*y^2}}
errorDepth = 0
sagbi(G,Strategy=>Engine)
rawSubduction(rawMonoidNumberOfBlocks raw monoid R, raw spairs, raw Gmap, raw gbJ)
gens gbJ
spairs

k = coefficientRing R;
nR = 2
nG = numcols G
N = monoid [
    Variables => nR + nG,
    Degrees=>join(degrees source vars R, degrees source G),
    MonomialOrder => append((options R).MonomialOrder, Weights=>2:1)
    ]
RS = k N;
RtoRS = map(RS,R,(vars RS)_{0..nR-1});
--RStoS = map(RS,RS, matrix {toList(nR:0_RS)} | (vars RS)_{nR .. nR+nG-1});
J = ideal((vars RS)_{nR..nR+nG-1}-RtoRS(leadTerm G));
Gmap = map(RS,RS,(vars RS)_{0..nR-1} | RtoRS(G));
gbJ = gb J;
netList flatten entries gens gbJ
binomialSyzygies = selectInSubring(1, gens gbJ)
spairs = submatrixByDegrees(binomialSyzygies, 4);
rawMonoidNumberOfBlocks raw monoid R
Gmap
elapsedTime S=rawSubduction(rawMonoidNumberOfBlocks raw monoid R, raw spairs, raw Gmap, raw gbJ);
