

--objective function
----We want to test if a function 
kk=QQ
R = kk[a11,a12,a21,a22,b11,b12,b21,b22,t]**kk[x1,x2,y1,y2]
A = matrix{{a11,a12},{a21,a22}}
B = matrix{{b11,b12},{b21,b22}}
--X = transpose matrix{{random CC,random CC}}
--Y = transpose matrix{{random CC,random CC}}
X = transpose matrix{{x1,x2}}
Y = transpose matrix{{y1,y2}}
x={x1,x2,y1,y2}

V = flatten entries (A*B*X-Y)
f=V_0^2+V_1^2

z = {a11,a12,a21,a22,b11,b12,b21,b22}

CE=z/(i->diff(i,f))
G=CE/(i->t*random kk+10*t*random kk)
loadPackage"Bertini"
decompose ideal (CE+G)
degree sub(ideal (CE+G),{t=>1})

makeB'InputFile(storeBM2Files,
    B'Configs=>{"TrackType"=>1},
    AffVariableGroup => z,
    B'Polynomials=>CE,
    RandomComplex=>x    
    )
runBertini(storeBM2Files)
readFile(storeBM2Files)

---Zero dim solve
makeB'InputFile(storeBM2Files,
    B'Configs=>{"TrackType"=>1},
    AffVariableGroup => z,
    B'Polynomials=>CE+G,
    RandomComplex=>x|{t}
    )
runBertini(storeBM2Files)
readFile(storeBM2Files)
