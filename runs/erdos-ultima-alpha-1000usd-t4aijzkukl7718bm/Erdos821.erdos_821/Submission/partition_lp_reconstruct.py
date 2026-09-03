"""Finite abstract moment-model search followed by exact rational checking.
Run with sage -python. This does not prove anything about actual primes.
"""
from sage.all import matrix, vector, QQ
from partition_lp_probe import parts,z
from scipy.sparse import coo_matrix
from scipy.optimize import linprog
import numpy as np, json, sys, time

n=int(sys.argv[1]); root=int(sys.argv[2])
ps=[p for p in parts(n) if p[0]>n//root]; pos={p:i for i,p in enumerate(ps)}
mus=[p for t in range(n//2+1) for p in parts(t)]+[(j,) for j in range(n//2+1,n+1)]
rr=[];cc=[];vv=[]
for row,mu in enumerate(mus):
    for nu in parts(n-sum(mu)):
        col=pos.get(tuple(sorted(mu+nu,reverse=True)))
        if col is not None:
            den=z(mu)*z(nu)
            assert z(ps[col])%den==0
            rr.append(row);cc.append(col);vv.append(z(ps[col])//den)
a=coo_matrix((vv,(rr,cc)),shape=(len(mus),len(ps))).tocsr()
b=np.array([1/z(mu) for mu in mus])
print('Numerical search',n,root,a.shape,'nnz',len(vv),flush=True)
t=time.time()
sol=linprog(np.zeros(len(ps)),A_eq=a,b_eq=b,method='highs',
            options={'primal_feasibility_tolerance':1e-10,
                     'dual_feasibility_tolerance':1e-10})
print(sol.message,'seconds',time.time()-t,flush=True)
if not sol.success: raise SystemExit(1)
keep=[i for i in range(len(ps)) if sol.x[i]>0]
print('Exact reconstruction on support',len(keep),flush=True)
A=matrix(QQ,a[:,keep].toarray().tolist())
B=vector(QQ,[QQ(1)/z(mu) for mu in mus])
t=time.time()
try: W=A.solve_right(B)
except ValueError as e:
    print('EXACT RECONSTRUCTION FAILED',e,flush=True)
    raise SystemExit(2)
assert A*W==B
if not all(w>=0 for w in W):
    print('EXACT POSITIVITY FAILED; min weight',min(W),flush=True)
    raise SystemExit(3)
assert sum(W)==1
print('EXACT CHECK PASSED',n,root,'support',sum(w>0 for w in W),
      'maximum density ratio',max(w*z(ps[i]) for w,i in zip(W,keep)),
      'seconds',time.time()-t,flush=True)
with open(f'/tmp/partition_exact_reconstruction_{n}_{root}.json','w') as f:
    json.dump([{'partition':ps[i],'weight':str(w)} for w,i in zip(W,keep) if w],f)
