# Independent audit of periodic_norm_two_scale.md

A fresh research agent independently read Sections 2--5 and the scalar
Frobenian reference /corpus/src/1904.12845/1904.12845.tex, lines 532--604.
Its verdict was sound for each fixed modulus, with two minor precisions.
The parent independently checked the Euler-state multiplication, stochastic
spectral bound, local Hankel error, and conversion to actual potentials.

1. The exact state algebra correctly retains nonunit and zero residues.
   Coprime multiplicativity follows from Gaussian unique factorization. The
   factor 1/2 in the prime-ideal expansion is correct. Acceptance is only
   linear, not multiplicative; the proof does not assume otherwise.
2. 2V is column-stochastic and power-bounded. Thus eigenvalues of V have
   modulus <=1/2, the leading eigenvalue 1/2 is semisimple, and all other
   eigenvalues have strictly smaller real part. Lower Jordan blocks are
   allowed and their logarithmic factors are retained.
3. The analytic growth statements must be restricted to a fixed vertical
   strip, for example Re(s)<=2, inside a slightly smaller zero-free region.
   A bound on log((s-1)L(s,1)) solely in Im(s) cannot hold as Re(s)->infinity.
   The corrected strip suffices for every contour used in the proof. For
   fixed conductor the needed Hecke zero-free and logarithm bounds are
   unconditional; this supplies no conductor-uniform information.
4. Choose the smoothing cutoff by rescaling one fixed smooth transition.
   This gives the required derivative bounds O_r(epsilon^(-r)); an arbitrary
   unspecified family of smooth cutoffs would not automatically do so.
5. Bounded coefficients allow sharp/smooth error O(x epsilon+1). The Mellin
   contour with epsilon=log(x)^(-B), T=exp(sqrt(log x)), and decay order above
   the growth exponent gives negligible nonlocal errors. The local Taylor
   error is O(x log(x)^(Re(beta)-J-1) (loglog x)^k). Reciprocal-Gamma
   derivatives handle nonpositive integer exponents correctly.
6. With J=2 the resulting actual norm population is
     F_B(X)=X h(log X)+O_M(X log(X)^(-5/2)(loglog X)^d).
   The independently established first-order theorem identifies the leading
   coefficient kappa*lambda_B; stochasticity alone would not identify it.
   Both h and its derivative have lower-order corrections controlled by a
   fixed spectral gap. Consequently the squared potential is
     K(P_R)^2=c^2/h(log(4R^2))^2+o(1), c=pi*delta/4,
   and the derivative of its smooth main term tends to
   (pi*delta/(4*kappa*lambda_B))^2. Actual endpoint errors O_M(R) are small
   enough on this additive potential scale.

Thus the actual two-scale limit is valid for fixed M, mask A, and 0<t<1:

 K(P_R)^2-K(P_(tR))^2 ->
   (pi*delta/(4*kappa*lambda_B))^2*log(t^(-2)).

The claimed near-half-cardinality actual child eventually has potential
loss <=1, but its threshold depends on M. The mod-13 missing-norm term of
order X/log(X)^(5/6) is consistent with this limit and cannot be discarded
from the potential itself. There is no unrestricted finite-height or
modulus-uniform contraction. No statement of Spec.lean is settled.
