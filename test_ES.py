#!/usr/bin/python3
"""
	This program can be used to generate a CNF
	to determine higher dimensional Erdos-Szekeres numbers
	(c) 2022 Manfred Scheucher <scheucher@math.tu-berlin.de>
"""


from itertools import *
from sys import *


empty = int(argv[1]) # 0 if k-gon, 1 if k-hole
k = int(argv[2]) # size of gon/hole
d = int(argv[3]) # dimension
n = int(argv[4]) # number of points

r = d+1 # rank of oriented matroid = dimension + 1
N = range(n)

assert(empty in [0,1])

all_variables = []
all_variables += [('chi',I) for I in permutations(N,r)]
all_variables += [('I_sep_pq',(I[:r-1],I[r-1],I[r])) for I in permutations(N,r+1)] # hyperplane determined by I separates the two points p and q
all_variables += [('I_cont_p',(I[:r],I[r])) for I in permutations(N,r+1)] # simplex determined by I contains the point p

all_variables_index = {}

num_vars = 0
for v in all_variables:
	all_variables_index[v] = num_vars
	num_vars += 1

def var(L):	return 1+all_variables_index[L]
def var_chi(*L): return var(('chi',L))
def var_hyperplane_separates_2points(*L): return var(('I_sep_pq',L))
def var_simplex_contains_point(*L): return var(('I_cont_p',L)) 

 


constraints = []


print("(0) alternating axioms",len(constraints))
for I in combinations(N,r):
	for J in permutations(I):
		inversions = len([(u,v) for (u,v) in combinations(J,2) if u > v])
		sgn = +1 if inversions % 2 == 0 else -1
		if I == J: assert(sgn == +1)
		constraints.append([-var_chi(*I),+sgn*var_chi(*J)])
		constraints.append([+var_chi(*I),-sgn*var_chi(*J)])


# OM-bible, Theorem 3.6.2 (3-term grassmann pluecker relations)
print("(1) compact exchange axioms",len(constraints))
for X in permutations(N,r):
	x1 = X[0]
	x2 = X[1]
	X_rest = X[2:]
	if X_rest == tuple(sorted(X_rest)): # w.l.o.g. 
		for y1,y2 in permutations(N,2):
			if len({y1,y2}|set(X_rest)) < r: continue # in this case the condition "">= 0" is fulfilled anyhow

			S1 = [+1,-1] if (len({y1,x2}|set(X_rest)) == r and len({x1,y2}|set(X_rest)) == r) else [0]
			S2 = [+1,-1] if (len({y2,x2}|set(X_rest)) == r and len({y1,x1}|set(X_rest)) == r) else [0]
			S0 = [+1,-1]
			for s0 in S0:
				for s1 in S1:
					for s2 in S2:
						C = []
						if s1 != 0: C += [-s1*var_chi(y1,x2,*X_rest),-s1*var_chi(x1,y2,*X_rest)]
						if s2 != 0: C += [-s2*var_chi(y2,x2,*X_rest),-s2*var_chi(y1,x1,*X_rest)]
						C += [-s0*var_chi(x1,x2,*X_rest),+s0*var_chi(y1,y2,*X_rest)]
						constraints.append(C)




print("(2) the antipodal of a point in a simplex is forbidden (assume acyclic oriented matroid)")
for X in permutations(N,r+1):
	for s in [+1,-1]:
		constraints.append([+s*((-1)**i)*var_chi(*I) for i,I in enumerate(combinations(X,r))])



print("(3) wlog: 0,...,r-3 lie on the boundary of convex hull and others are sorted around (to break symmetries)",len(constraints))
for i,j in combinations(range(r-2,n),2):
	constraints.append([var_chi(*range(r-2),i,j)])


print("(4) assert separations",len(constraints))
for I in permutations(N,r+1):
	X = I[:r-1]
	p = I[r-1]
	q = I[r]

	# hyperplane through I separates p and q <=> chi(I+p) != chi(I+q)
	constraints.append([-var_hyperplane_separates_2points(X,p,q),+var_chi(*X,p),+var_chi(*X,q)])
	constraints.append([-var_hyperplane_separates_2points(X,p,q),-var_chi(*X,p),-var_chi(*X,q)])
	constraints.append([+var_hyperplane_separates_2points(X,p,q),-var_chi(*X,p),+var_chi(*X,q)])
	constraints.append([+var_hyperplane_separates_2points(X,p,q),+var_chi(*X,p),-var_chi(*X,q)])



def cyclic_rotations(I): 
	for t in range(len(I)):
		yield I[t:]+I[:t]

print("(5) containment",len(constraints))
for I in permutations(N,r+1):
	X = I[:r]
	p = I[r]

	for Xrot in cyclic_rotations(X):
		constraints.append([-var_simplex_contains_point(X,p),-var_hyperplane_separates_2points(Xrot[:-1],Xrot[-1],p)])
	
	constraints.append([+var_simplex_contains_point(X,p)]+[+var_hyperplane_separates_2points(Xrot[:-1],Xrot[-1],p) for Xrot in cyclic_rotations(X)])

FULL_CONSTRAINTS = True
if empty:
	print("(6) no k-holes",len(constraints))
	# if I does not form a k-hole
	# then there is an r-subset J of I which contains a point p of N.
	# moreover, since the convex hull of I can be triangulated, 
	# J can be chosen so that it contains a fixed extremal point of I (w.l.o.g. the first in the order) 
	for I in combinations(N,k):
		constraints.append([var_simplex_contains_point(J,p) for J in combinations(I,r) for p in set(N)-set(J) if J[0] == I[0] or p == I[0] or FULL_CONSTRAINTS])

else:
	print("(6) no k-gons",len(constraints))
	# if I does not form a k-gon
	# then there is an r-subset J of I which contains a point p of I.
	# moreover, since the convex hull of I can be triangulated, 
	# J can be chosen so that it contains a fixed extremal point of I (w.l.o.g. the first in the order) 
	for I in combinations(N,k):
		constraints.append([var_simplex_contains_point(J,p) for J in combinations(I,r) for p in set(I)-set(J) if J[0] == I[0] or p == I[0] or FULL_CONSTRAINTS])



print("Total number of constraints:",len(constraints))


fp = "_new_instance_empty"+str(empty)+"_k"+str(k)+"_d"+str(d)+"_n"+str(n)+("" if FULL_CONSTRAINTS else "_improved")+".in"
f = open(fp,"w")
f.write("p cnf "+str(num_vars)+" "+str(len(constraints))+"\n")
for c in constraints:
	f.write(" ".join(str(v) for v in c)+" 0\n")
f.close()

print("Created CNF-file:",fp)
 
