needsPackage "Graphs";
needsPackage "Matroids";

--Perform BFS to find shortest path between a vertex and a set of
--vertices in a digraph
shortestPath = method(TypicalValue => List)
shortestPath (Digraph, Thing, List) := List => (D,start,finishSet) -> (
    V    := vertexSet(D);
    assert(member(start, V));
    r    := length vertexSet(D);
    --just pick some dummy variable to initialize predecessor array
    local dummy;
    dummy = symbol dummy;
    pred := new MutableHashTable from apply(V,i-> i=>dummy);
    dist := new MutableHashTable from apply(V,i-> i=>infinity);
    visited := new MutableHashTable from apply(V,i-> i=>false);
    dist#start = 0;
    visited#start = true;
    queue := {start};
    
    while not queue == {} do (
    	v := first queue;
	queue = drop(queue,1);
	for u in elements children(D,v) do (
	    if (visited#u) == false 
	    then (
		visited#u = true;
	    	dist#u = (dist#v) + 1;
		pred#u = v;
	    	queue=append(queue,u);
	    	if member(u, finishSet) 
	    	then (
		    P := {u};
		    back := u;
		    while(not (pred#back) === dummy) do (
		    	P = prepend(pred#back,P);
		    	back = pred#back;
		    );
		return P;
		);
	    );
	);
    );
    return {};
)

--input: A list of matroids with the same ground set
--output: A partition if possible. Otherwise, the emptylist.
matroidPartition = method(TypicalValue => List)
matroidPartition List := List => mls -> (
    --check to make sure list of matroids with same ground set
    r   := length mls;
    assert(all(0..r-1, i-> instance(mls_i,Matroid)));
    E   := (mls_0).groundSet;
    assert(all(0..r-1, i->((mls_i).groundSet)===E));
    
    --set up initial values: special symbols z and list of lists that'll hopefully become our partition
    local z;
    Z   := apply(new List from 1..r, i-> symbol z_i);
    Els := new MutableList from prepend(elements(E),apply(new List from 1..r, i->{}));
    
    
    --function to make relation for the digraph
    arrow := (x,y) -> (
	if (member(y,Els#0) or member(x,Z) or x===y) then return 0;
	if member(y,Z) 
	then if (not isDependent(mls_(((baseName y)#1)-1),append(Els#((baseName y)#1),x)))
	    then return 1
	    else return 0
	else (
	    j := first select(1..r, i->member(y,Els#i));
	    if not isDependent(mls_(j-1),append(delete(y,Els#j),x)) 
	    then return 1
	    else return 0
	    )
    );
    
    --Once shortest path is found between x and z_j, update the partition!
    repaint := (P,Els) -> (
	l := (length P)-2;
	for i from 1 to l do (
	    --We are traversing the path a 2-tuple at a time starting with (P_0,P_1)
	    --We want to replace P_i from its current set of partition with P_(i-1) until we get to some element of Z
	    j1 := first select(0..r,k->member(P_(i-1),Els#k));
	    j2 := first select(0..r,k->member(P_i,Els#k));
	    Els#j1 = delete(P_(i-1),Els#j1);
	    Els#j2 = append(Els#j2,P_(i-1));
	    );
	--P_(i-1) is a z_j, so just rip off index
	j1 := first select(0..r,k->member(P_l,Els#k));
	Els#j1 = delete(P_l,Els#j1);
	Els#((baseName P_(l+1))#1) = append(Els#((baseName P_(l+1))#1),P_l);
	);
    
    --unless we've exhausted elements, try to make a partition!
    while not (Els#0) == {} do (
	newVertex   := first first Els;
	constructed := mingle drop(Els,1);
	V   := join({newVertex},constructed, Z);
    	M   := matrix for x in V list for y in V list arrow(x,y);
	D   := digraph(V,M);
	if any(1..r, i->isReachable(D,Z_(i-1),newVertex))
	then repaint(shortestPath(D,newVertex,Z),Els)
	--WOMP. No partition.
	else return {};
    );
    --We found a partition! Now sort it by length, largest to smallest
    return apply(rsort apply(new List from drop(Els,1),i->(#i,i)),i->i_1);
)

reduceMatrix = method(TypicalValue => Matrix)
reduceMatrix(Matrix) := Matrix => M -> (
   -- check if matrix is of full rank:
   if (rank M == min(rank M.source,rank M.target)) then {
    return M
    } else return transpose gb transpose M
   )

weight = method(TypicalValue => Number)
weight BasicList := Number => c -> (
    sum(new List from (apply(0..length c-1, i-> if c_i == 0 then 0 else 1)))
    )

ambientWords = method(TypicalValue => List)
ambientWords LinearCode := List => C -> (
    S := C.AmbientModule;
    apply(toList(toList (set(alphabet C))^**(length C.Generators)/deepSplice), i->toList i)
    )

minimumWeight = method(TypicalValue => Number)
minimumWeight LinearCode := Number => C -> (
    M := matrix C.Generators;
    F := C.BaseField;
    k := length C.Generators; --Assumes generators are linearly independent?
    n := length C;
    l := ceiling(n/k);
    D := l; --D could probably be modified to be better
    w := 1;
    j := 1;
    
    --Partition columns of LinearCode into information sets
    T := matroidPartition(apply(toList(1..l),i->matroid(M)));
    
    r := {}; --list of relative ranks
    currentUnion := set();
    for i from 0 to length T-1 do (
	r = append(r,#(T_i-currentUnion));
	currentUnion = currentUnion + set(T_i);
	);
    nonzeroWords := delete(apply(1..k,i->0),ambientWords(C));
    
    dupper := n-k+1; --Start with Singleton Bound
    dlower := 0;
    while(true) do (
        permutation := join(T_(j-1),toList(0..n-1)-set(T_(j-1)));
        G := reduceMatrix(M_permutation);
        sameWeightWords := select(nonzeroWords, u -> weight(toList u) == w);
        specialCodewords := apply(sameWeightWords, u -> flatten entries ((matrix {toList u})*G));
        dupper = min(join({dupper}, apply(specialCodewords, i->weight i)));
        dlower = sum(toList apply(1..j,i->max(0,w+1-k+r_(i-1))))+sum(toList apply(j+1..D,i->max(0,w-k+r_(i-1))));
        if dlower >= dupper
    	then return dlower
    	else (if j < D then j = j+1
	    else w = w+1);
    	if w > k then error "No minimum weight found.";
    )
)