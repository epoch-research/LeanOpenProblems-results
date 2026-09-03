import numpy as np,sys,time,json
from scipy.optimize import milp, LinearConstraint, Bounds
from scipy.sparse import lil_matrix, vstack
N=int(sys.argv[1]); E=float(sys.argv[2]); path=sys.argv[3]
A=np.loadtxt(path,dtype=int,ndmin=1); A=A[A<N]
p=np.minimum(1,np.sqrt(4*np.log(np.arange(2*N)+np.e)/(np.pi*(np.arange(2*N)+1))))
q=np.fft.irfft(np.fft.rfft(p,4*N)**2,4*N)[:2*N]
a=np.zeros(2*N);a[A]=1
r=np.rint(np.fft.irfft(np.fft.rfft(a,4*N)**2,4*N)[:2*N])
M=lil_matrix((N+1,N));
for n in range(N,2*N):
 for t in A:
  b=n-t
  if N<=b<2*N:M[n-N,b-N]=1
need=round(sum(p))-len(A); M[N,:]=1
lo=np.r_[np.ceil((q[N:]-E-r[N:])/2),need]; hi=np.r_[np.floor((q[N:]+E-r[N:])/2),need]
print('N',N,'E',E,'need',need,'oldPeak',max(r[N:]-q[N:]),flush=True)
t=time.time()
res=milp(np.zeros(N),integrality=np.ones(N),bounds=Bounds(np.zeros(N),np.ones(N)),constraints=LinearConstraint(M.tocsc(),lo,hi),options={'time_limit':90})
print('time',time.time()-t,'status',res.status,res.message,flush=True)
if res.x is not None:
 B=np.r_[A,N+np.where(res.x>.5)[0]]; np.savetxt(path+'.ext'+str(E),B,fmt='%d')
 rr=np.array([sum((n-x in set(B)) for x in B if x<=n)for n in range(N,2*N)])
 print('actual max',max(abs(rr-q[N:])))
