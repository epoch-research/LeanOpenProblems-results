"""Finite partition moment experiment; no assertion about actual primes.
Find numerically, reconstruct over rationals, check every constraint exactly.
Usage under Sage Python: N R root cap
"""
from sage.all import ZZ, QQ, GF, matrix, vector
from scipy.optimize import linprog
from scipy.sparse import csc_matrix
from collections import Counter
from functools import lru_cache
from math import comb, factorial, prod
import sys, json, time
@lru_cache(None)
def partitions(n,cap):
    if n==0:return ((),)
    return tuple((j,)+p for j in range(min(n,cap),0,-1) for p in partitions(n-j,j))
def z(p):return prod(j**k*factorial(k) for j,k in Counter(p).items())
def main(N,R,root,cap):
    parts=[p for p in partitions(N,N) if root*max(p)>N]
    pats=[p for n in range(R+1) for p in partitions(n,n)] + [(j,) for j in range(R+1,N+1)]
    cts=[Counter(p) for p in pats]; zs=[z(p) for p in pats]
    scales=[z(p) for p in parts]; cols=[]; rr=[];cc=[];vv=[]
    for i,p in enumerate(parts):
        c=Counter(p)
        col={r:prod(comb(c[j],a) for j,a in pat.items()) for r,pat in enumerate(cts)
             if all(c[j]>=a for j,a in pat.items())}
        cols.append(col)
        for r,v in col.items():rr.append(r);cc.append(i);vv.append(v*zs[r]/scales[i])
    A=csc_matrix((vv,(rr,cc)),shape=(len(pats),len(parts)))
    print('parameters',N,R,root,cap,'shape',A.shape,'nnz',A.nnz,flush=True)
    if 2*R<=N:keep=list(range(1,len(pats)))
    else:
        Mmod=matrix(GF(1000003),len(parts),len(pats),lambda i,r:cols[i].get(r,0)*zs[r])
        keep=list(Mmod.pivots()); del Mmod
        print('modular row selection:',len(keep),'rows',flush=True)
    res=linprog([0.]*len(parts),A_eq=A[keep,:],b_eq=[1.]*len(keep),bounds=(0,cap),
       method='highs-ipm',options={'small_matrix_value':1e-12,'dual_feasibility_tolerance':1e-9,
                                 'primal_feasibility_tolerance':1e-9})
    print(res.message,flush=True)
    if not res.success:return
    support=[i for i,v in enumerate(res.x) if v>1e-10]
    fixed={i for i in support if res.x[i]>cap-1e-8}
    free=[i for i in support if i not in fixed]
    print('support',len(support),'free',len(free),'max full residual',max(abs(A@res.x-1)),flush=True)
    candidate={'N':N,'R':R,'root':root,'cap':cap,'parts':parts,'support':support,
               'fixed':list(fixed),'keep':keep}
    json.dump(candidate,open('/tmp/partition_level_candidate_%d_%d_%d.json'%(N,R,root),'w'))
    D=factorial(N)
    rhs=vector(ZZ,[D//zs[r]-sum(cap*(D//scales[i])*cols[i].get(r,0) for i in fixed) for r in keep])
    M=matrix(ZZ,len(keep),len(free),lambda r,j:cols[free[j]].get(keep[r],0))
    sol=M.solve_right(rhs)
    W={i:QQ(cap*(D//scales[i])) for i in fixed}
    W.update(zip(free,sol))
    assert all(v>=0 and v*scales[i]<=cap*D for i,v in W.items())
    assert sum(W.values())==D
    for r in range(len(pats)):
        assert sum(v*cols[i].get(r,0) for i,v in W.items())*zs[r]==D, r
    data={'N':N,'root':root,'halfLevel':R,'densityCap':cap,
          'data':[[list(parts[i]),str(v/D)] for i,v in sorted(W.items()) if v>0]}
    path='/tmp/partition_level_certificate_%d_%d_%d_cap%d.json'%(N,R,root,cap)
    json.dump(data,open(path,'w'))
    print('EXACT ALL CONSTRAINTS VERIFIED',path,flush=True)
if __name__=='__main__':main(*map(int,sys.argv[1:]))
