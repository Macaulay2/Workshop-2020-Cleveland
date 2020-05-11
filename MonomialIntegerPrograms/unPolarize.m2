firstIndexOf := first@@last@@baseName;    --This is a function that takes z_{i,j,k,...} and maps it to i
                                          --baseName: turns the variable into an IndexedVariable
                                          --last: an IndexedVariable is a list where the last element is the index list
                                          --first: we want to get the first index of each variable
lastIndexOf := last@@last@@baseName;      --This function finds the lastIndex of a variable


unPolarize = method();
unPolarize (MonomialIdeal, Ring) := (I, R) -> (
  --This reverses the effect of polarize.
  --I is the ideal we wish to unpolarize.
  --R is the ring that we want to map I too.

  polarizedVariables := (ring I)_*;         --This gets all the variable names in I.
  substitutions := polarizedVariables / (   --We get a list of all the substitutions.
    v -> v => R_(firstIndexOf v)            --All the substitutions look like z_{i, j} => R_i.
                                            --first@@indices would not work because z_{i,j} is not the ith variable in the ring containing I
  );
  substitute(I, substitutions)              --Finally, we apply all these substitutions to I.
)


unPolarizeSome = method();
unPolarizeSome (List, Ring) := (L, R) -> (
  --This applies unPolarize to the ideals in L where all the last indices are 0.
  for I in L list (                                     --loop through the list
    if not all(I_*, zero@@lastIndexOf) then continue;   --If one of the last indices is zero, we skip this and go to the next ideal and add nothing.
    unPolarize(I, R)                                    --Otherwise, we unPolarize the ideal and add it to the list
  )
);


end--

restart
needsPackage("MonomialIntegerPrograms")
load("unPolarize.m2")
rmi := (R, j, k, l) -> monomialIdeal(apply(j, i -> product apply(take(random gens R, 1 + random k), x -> x^(1 + random l))))


R = QQ[a..j];
I = rmi(R, 10, 5, 2);
print I
minimalPrimes I
topMP = select(oo, x -> # first entries gens x == codim I);
isSquareFree I
topMPIP = if isSquareFree I then(
  topMinimalPrimesIP I
) else (
  unPolarizeSome(topMinimalPrimesIP I, R)
);
isSquareFree I
print netList transpose{topMP, topMPIP}
