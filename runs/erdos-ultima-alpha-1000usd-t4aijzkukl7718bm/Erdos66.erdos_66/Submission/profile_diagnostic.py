import numpy as np
from fractions import Fraction
N=2**20
M=4*N
radius=np.exp(-32.0/M)
theta=2*np.pi*np.arange(M)/M
z=radius*np.exp(1j*theta)
values=np.sqrt(-np.log(1-z)/(z*(1-z)))
p=np.fft.fft(values).real[:N]/M/np.power(radius,np.arange(N))
del z,theta,values
# Compare a small exact rational prefix, using P^2 = H shifted.
exact=[Fraction(1)]
H=Fraction(1)
for n in range(1,80):
    H+=Fraction(1,n+1)
    exact.append((H-sum((exact[i]*exact[n-i] for i in range(1,n)),Fraction(0)))/2)
print('Coefficient max error against 80 exact rational values:',max(abs(p[i]-float(v)) for i,v in enumerate(exact)))
S=np.r_[0.0,np.cumsum(p)]
a=np.diff(np.floor(S)).astype(np.int64)
print('Indicator range:',a.min(),a.max(),'cardinality:',a.sum())
frac=S[2:]-np.floor(S[2:])
print('Closest interior cumulative sum to an integer:',np.min(np.minimum(frac,1-frac)))
R=np.rint(np.fft.irfft(np.fft.rfft(a,2*N)**2,2*N)[:N]).astype(np.int64)
pp=np.fft.irfft(np.fft.rfft(p,2*N)**2,2*N)[:N]
h=np.cumsum(1.0/np.arange(1,N+1))
print('Largest tested fractional convolution residual:',np.max(abs(pp-h)))
for j in range(12,21):
    lo=2**(j-1); hi=2**j
    rr=R[lo:hi]
    ratios=rr/np.log(np.arange(lo,hi))
    print('block',lo,hi,'min/max r',int(rr.min()),int(rr.max()),'holes',int(np.sum(rr==0)),
          'ratio min/mean/max',float(ratios.min()),float(ratios.mean()),float(ratios.max()))
