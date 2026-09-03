"""Experimental finite moment LP, with exact rational certificate checking.
Run under Sage's Python. This is NOT a model or disproof about actual primes.
"""
from sage.all import QQ, matrix, vector
from scipy.optimize import linprog
from scipy.sparse import csc_matrix
from collections import Counter
from functools import lru_cache
from math import comb, factorial, prod
import sys, json

@lru_cache(None)
def partitions(n, cap):
    if n == 0: return ((),)
    return tuple((j,) + p for j in range(min(n,cap),0,-1)
                 for p in partitions(n-j,j))

def z(p):
    return prod(j**k*factorial(k) for j,k in Counter(p).items())

def main(N, root):
    R=N//2
    parts=[p for p in partitions(N,N) if root*max(p)>N]
    pats=[p for n in range(R+1) for p in partitions(n,n)]
    pats += [(j,) for j in range(R+1,N+1)]
    counters=[Counter(p) for p in pats]
    zs=[z(p) for p in pats]
    rows=[]; cols=[]; vals=[]; exactcols=[]; scales=[]
    for i,p in enumerate(parts):
        c=Counter(p)
        col={r:zs[r]*prod(comb(c[j],a) for j,a in pat.items())
             for r,pat in enumerate(counters) if all(c[j]>=a for j,a in pat.items())}
        scale=z(p); scales.append(scale); exactcols.append(col)
        for r,k in col.items():
            rows.append(r); cols.append(i); vals.append(k/scale)
    A=csc_matrix((vals,(rows,cols)),shape=(len(pats),len(parts)))
    print('N',N,'root',root,'shape',A.shape,'nnz',A.nnz,flush=True)
    result=linprog([0.]*len(parts),A_eq=A[1:,:],b_eq=[1.]*(len(pats)-1),bounds=(0,2),method='highs-ipm',
       options={'small_matrix_value':1e-12,'dual_feasibility_tolerance':1e-9,'primal_feasibility_tolerance':1e-9})
    print(result.message,flush=True)
    if not result.success: return
    support=[i for i,v in enumerate(result.x) if v>1e-12]
    print('support',len(support),'scaled residual',max(abs(A@result.x-1)),flush=True)
    M=matrix(QQ,len(pats),len(support),lambda r,j:exactcols[support[j]].get(r,0))
    fixed={j:QQ(2)/scales[i] for j,i in enumerate(support) if result.x[i]>1.99999999}
    free=[j for j in range(len(support)) if j not in fixed]
    rhs=vector(QQ,[1]*len(pats))-sum((M.column(j)*v for j,v in fixed.items()),vector(QQ,len(pats)))
    wf=M.matrix_from_columns(free).solve_right(rhs)
    w=vector(QQ,len(support))
    for j,v in fixed.items(): w[j]=v
    for j,v in zip(free,wf): w[j]=v
    assert M*w==vector(QQ,[1]*len(pats))
    assert all(v>=0 for v in w)
    assert sum(w)==1
    print('EXACT certificate checked; support',sum(v>0 for v in w),flush=True)
    data={'N':N,'root':root,'halfLevel':R,
          'data':[[list(parts[i]),str(w[j])] for j,i in enumerate(support) if w[j]>0]}
    path='/tmp/finer_partition_cap2_certificate_%d_%d.json'%(N,root)
    json.dump(data,open(path,'w'))
    print(path,flush=True)

if __name__=='__main__': main(int(sys.argv[1]),int(sys.argv[2]))
