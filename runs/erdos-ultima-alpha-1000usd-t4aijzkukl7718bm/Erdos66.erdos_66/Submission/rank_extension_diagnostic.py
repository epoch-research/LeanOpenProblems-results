"""Finite constructive diagnostic, NOT a proof or counterexample.
One point per harmonic rank cell, with a frozen prefix at each doubling.
Includes the finite-prefix convolution as a lookahead target.
"""
import numpy as np, json, sys, time

def profile(N):
    M=8*N; radius=np.exp(-32.0/M)
    z=radius*np.exp(2j*np.pi*np.arange(M)/M)
    vals=np.sqrt(-np.log(1-z)/(z*(1-z)))
    p=np.fft.fft(vals).real[:N]/M/np.power(radius,np.arange(N))
    return p

def reps(A,N):
    a=np.zeros(N);a[A]=1
    return np.rint(np.fft.irfft(np.fft.rfft(a,2*N)**2,2*N)).astype(int)

def build(seed=1,Nmax=4096,steps=60000):
    rng=np.random.default_rng(seed); p=profile(Nmax)
    P=np.r_[0,np.cumsum(p)]
    starts=np.searchsorted(P,np.arange(int(P[-1])+2),side='left')
    # cell(i)=floor(P(i)); account for exact P(0)=0 and P(1)=1.
    starts[0]=0; starts[1]=1
    A=[]; results=[]; freeze=0
    for k in range(7,int(np.log2(Nmax))+1):
        N=2**k; ncells=int(P[N]+1e-10)
        prev=len(A)
        A.extend(int(rng.integers(starts[j],min(starts[j+1],N))) for j in range(prev,ncells))
        A=np.array(A,dtype=int)
        movable=np.flatnonzero(starts[:ncells]>=freeze)
        R=reps(A,N)
        mu=np.fft.irfft(np.fft.rfft(p[:N],2*N)**2,2*N)
        scale=np.sqrt(np.log(np.arange(2*N)+2))
        valid=np.arange(2*N)>=max(32,freeze)
        # Lookahead compares to the actual finite fractional convolution.
        # It prevents an unconstrained self-count peak immediately after N.
        def loss(vals,idx,t):
            e=(vals-mu[idx])/scale[idx]
            return np.where(valid[idx],np.cosh(np.clip(t*e,-50,50)),0.)
        best=1e99; accepted=0;t0=time.time()
        # Heating is brief; subsequent batches increase focus on worst errors.
        for it in range(steps):
            j=int(rng.choice(movable)); a=A[j]
            b=int(rng.integers(starts[j],min(starts[j+1],N)))
            if a==b:continue
            other=np.r_[A[:j],A[j+1:]]
            idx=np.r_[a+other,b+other,2*a,2*b]
            delta=np.r_[np.full(len(other),-2),np.full(len(other),2),-1,1]
            idx,inv=np.unique(idx,return_inverse=True)
            delta=np.bincount(inv,weights=delta).astype(int)
            t=1+2*it/steps
            change=np.sum(loss(R[idx]+delta,idx,t)-loss(R[idx],idx,t))
            temp=0.6*(1-it/steps)**3
            if change<0 or (temp>0 and rng.random()<np.exp(-min(change/temp,700))):
                A[j]=b;R[idx]+=delta;accepted+=1
        # Independent recomputation certifies this finite diagnostic's counts.
        assert np.array_equal(R,reps(A,N))
        lo=max(32,freeze)
        e=R-mu
        rr=R[lo:N]/np.log(np.arange(lo,N))
        result=dict(seed=seed,N=N,freeze=freeze,card=len(A),accepted=accepted,
            max_abs_error=float(np.max(np.abs(e[lo:N]))),
            max_scaled_error=float(np.max(np.abs(e[lo:N])/scale[lo:N])),
            min_ratio=float(rr.min()),max_ratio=float(rr.max()),
            lookahead_max_scaled=float(np.max(np.abs(e[N:2*N])/scale[N:2*N])),
            seconds=time.time()-t0)
        print(json.dumps(result),flush=True);results.append(result)
        np.savez(f'/tmp/rank_extension_seed{seed}_N{N}.npz',A=A,p=p[:N],R=R,mu=mu)
        freeze=N;A=list(A)
    return results

if __name__=='__main__':
    build(int(sys.argv[1]) if len(sys.argv)>1 else 1,
          int(sys.argv[2]) if len(sys.argv)>2 else 4096,
          int(sys.argv[3]) if len(sys.argv)>3 else 60000)
