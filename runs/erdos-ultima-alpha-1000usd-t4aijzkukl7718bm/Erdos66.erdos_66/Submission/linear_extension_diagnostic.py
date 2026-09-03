"""Finite optimization diagnostic; numerical solver output is not a Lean proof.
First-window new/new terms vanish, so this is a genuine linear model.
"""
import numpy as np
from scipy import sparse
from scipy.optimize import milp, Bounds, LinearConstraint
import sys,json,time
from rank_extension_diagnostic import profile,reps

N=int(sys.argv[1]) if len(sys.argv)>1 else 256
prefix=np.load(f'/tmp/rank_extension_seed1_N{N}.npz')
A=prefix['A'];p=profile(2*N);P=np.r_[0,np.cumsum(p)]
old=np.zeros(N);old[A]=1
row=[];col=[]
for a in A:
    row.extend(range(a,N));col.extend(range(N-a))
T=sparse.coo_matrix((np.full(len(row),2.),(row,col)),shape=(N,N)).tocsc()
R=reps(A,N)
H=np.cumsum(1./np.arange(1,2*N+1))
b=H[N:2*N]-R[N:2*N]
s=np.sqrt(np.log(np.arange(N,2*N)+2))
W=sparse.csc_matrix(-s[:,None])
C=sparse.vstack([sparse.hstack([T,W]),sparse.hstack([-T,W])],format='csc')
low=np.full(2*N,-np.inf);upp=np.r_[b,-b]
cells=np.floor(P[N:2*N]+1e-9).astype(int)
first=int(P[N]+1e-9);last=int(P[2*N]+1e-9)
rows=[];cols=[]
for j in range(first,last):
    ind=np.flatnonzero(cells==j);rows.extend([j-first]*len(ind));cols.extend(ind)
B=sparse.coo_matrix((np.ones(len(rows)),(rows,cols)),shape=(last-first,N+1)).tocsc()
C=sparse.vstack([C,B],format='csc');low=np.r_[low,np.ones(last-first)];upp=np.r_[upp,np.ones(last-first)]
upper=np.r_[np.where(cells<last,1.,0.),np.inf]
c=np.r_[np.zeros(N),1.]
for integer in [False,True]:
    t=time.time()
    r=milp(c,integrality=np.r_[np.ones(N) if integer else np.zeros(N),0.],
        bounds=Bounds(np.zeros(N+1),upper),constraints=LinearConstraint(C,low,upp),
        options=dict(time_limit=90.,mip_rel_gap=0.001))
    out=dict(N=N,integer=integer,status=r.status,message=r.message,seconds=time.time()-t,
        objective=float(r.fun) if r.fun is not None else None)
    if r.x is not None:
        x=r.x[:N]
        out['max_constraint_violation']=float(np.maximum(C@r.x-upp,low-C@r.x).max())
        out['fractional_variables']=int(np.sum((x>1e-6)&(x<1-1e-6)))
        if integer:
            new=np.flatnonzero(x>0.5)+N
            full=np.r_[A,new];rr=reps(full,2*N)
            out['independent_max_scaled_error']=float(np.max(abs(rr[N:2*N]-H[N:2*N])/s))
            out['lookahead_max_scaled_error']=float(np.max(abs(rr[2*N:4*N]-np.fft.irfft(np.fft.rfft(p,4*N)**2,4*N)[2*N:4*N])/np.sqrt(np.log(np.arange(2*N,4*N)+2))))
            np.savez(f'/tmp/linear_extension_N{N}.npz',A=full,p=p,R=rr)
    print(json.dumps(out),flush=True)
