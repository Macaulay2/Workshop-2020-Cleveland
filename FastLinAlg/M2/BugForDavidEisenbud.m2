restart
loadPackage "RandomPoints"
kk = ZZ/(nextPrime 10^4)
A2 = kk[x,y,Degrees=> {2,1}]
I = ideal "x-y2"
elapsedTime randomPoints(I, Verbose=>true, BruteForceAttempts=>0)
elapsedTime randomPoints(I, Verbose=>true, DecompositionStrategy=>Decompose)

restart
uninstallPackage "RandomPoints"
loadPackage("RandomPoints", Reload=>true)
installPackage "RandomPoints"
check RandomPoints