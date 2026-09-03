"""Finite diagnostic of a monotone feedback rule; not a proof or disproof.
Insert n if the already formed ordered count is below c*log(n+2).
All recorded counts are ordinary integer sums, with both ordered pairs.
"""
import sys, time, json
import numpy as np
N = int(sys.argv[1]) if len(sys.argv)>1 else 1_048_576
c = float(sys.argv[2]) if len(sys.argv)>2 else 1.0
r = np.zeros(2*N+1, dtype=np.int64)
a = np.empty(N+1, dtype=np.int64)
a[0]=0; size=1; r[0]=1
threshold=c*np.log(np.arange(N+1)+2)
start=time.time()
for n in range(1,N+1):
    if r[n] < threshold[n]:
        r[a[:size]+n]+=2
        r[2*n]+=1
        a[size]=n; size+=1
print(json.dumps(dict(N=N,c=c,card=size,seconds=time.time()-start)), flush=True)
for k in range(8, N.bit_length()):
    lo=2**(k-1); hi=min(2**k,N+1)
    if lo>=hi: continue
    x=np.arange(lo,hi)
    err=r[lo:hi]-c*np.log(x)
    print(json.dumps(dict(lo=lo,hi=hi,min_ratio=float(np.min(r[lo:hi]/np.log(x))),
      max_ratio=float(np.max(r[lo:hi]/np.log(x))),mean_ratio=float(np.mean(r[lo:hi]/np.log(x))),
      max_abs_error=float(np.max(abs(err))), rms_error=float(np.sqrt(np.mean(err*err))),
      card=int(np.searchsorted(a[:size],hi)),
      expected_card=float(2*np.sqrt(c/np.pi)*np.sqrt(hi*np.log(hi))))),flush=True)
np.savez(f'/tmp/greedy_log_feedback_{N}_{c}.npz',A=a[:size],R=r[:N+1])
