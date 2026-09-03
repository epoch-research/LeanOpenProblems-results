"""Exploratory LP for abstract partition moments, NOT for actual primes.

Unknown v(lambda) is the ratio of the candidate mass to uniform-permutation
cycle mass 1/z(lambda). For a selected subpartition mu, the normalized
factorial-moment equation has coefficient 1/z(lambda-mu). Thus all equations
have right side 1. No numerical output of this script is a Lean proof.
"""
from functools import lru_cache
from collections import Counter
from math import factorial, prod
import sys
import numpy as np
from scipy.sparse import coo_matrix
from scipy.optimize import linprog

@lru_cache(None)
def parts(n, cap=None):
    if cap is None: cap = n
    if n == 0: return ((),)
    return tuple((j,) + p for j in range(min(n,cap), 0, -1)
                 for p in parts(n-j,j))

@lru_cache(None)
def z(p):
    return prod(j**c * factorial(c) for j,c in Counter(p).items())

def test(n, root, bound):
    level=n//2
    cutoff=n//root
    outcomes=[p for p in parts(n) if p[0]>cutoff]
    pos={p:i for i,p in enumerate(outcomes)}
    moments=[p for t in range(level+1) for p in parts(t)]
    moments += [(j,) for j in range(level+1,n+1)]
    rr=[]; cc=[]; vv=[]
    for row,mu in enumerate(moments):
        for nu in parts(n-sum(mu)):
            lam=tuple(sorted(mu+nu,reverse=True))
            col=pos.get(lam)
            if col is not None:
                rr.append(row); cc.append(col); vv.append(1/z(nu))
    a=coo_matrix((vv,(rr,cc)),shape=(len(moments),len(outcomes))).tocsr()
    print(f'N={n}, root={root}, cols={len(outcomes)}, rows={len(moments)}, '
          f'nnz={len(vv)}, ratio upper bound={bound}',flush=True)
    sol=linprog(np.zeros(len(outcomes)),A_eq=a,b_eq=np.ones(len(moments)),
                bounds=(0,bound),method='highs',
                options={'primal_feasibility_tolerance':1e-9,
                         'dual_feasibility_tolerance':1e-9})
    print(sol.message,flush=True)
    if sol.success:
        print('max residual',float(np.max(np.abs(a@sol.x-1))),
              'max ratio',float(max(sol.x)),
              'nonzero ratios',int(sum(sol.x>1e-9)),flush=True)
        np.savez(f'/tmp/partition_probe_{n}_{root}.npz',x=sol.x,
                 outcomes=np.array(outcomes,dtype=object))
    return sol.success

if __name__=='__main__':
    n=int(sys.argv[1]); root=int(sys.argv[2]);
    bound=None if len(sys.argv)<4 else float(sys.argv[3])
    test(n,root,bound)
