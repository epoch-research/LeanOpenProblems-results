# Continuous fixed-marginal moment obstruction (auxiliary research)

This note concerns reconstruction from low-mass factorial moments. It does
**not** disprove the density conjecture about consecutive integers.
The kernel identities are Lean-checked in `ContinuousKernelObstruction.lean`.
The probability-space/Poisson–Dirichlet argument below is a mathematical proof
using the standard PD(1) factorial-moment and residual-partition formulas;
those formulas and their application here have NOT been formalized in Lean.

## 1. Polynomial identities

Write h(t)=t^3(1-t)^3, g(x,y)=h(x)h(y), and D=(partial_x-partial_y)^2.
Set F=Dg, F2=(x+y)F/2, k1=partial_x partial_y F,
k2=partial_x partial_y F2. Explicitly,

  F = h''(x)h(y)-2h'(x)h'(y)+h(x)h''(y),
  k1 = h'''(x)h'(y)-2h''(x)h''(y)+h'(x)h'''(y),
  k2 = (x+y)k1/2+(partial_x F+partial_y F)/2.

Both kernels are symmetric. On the unit square their row integrals vanish.
Every sum-line integral vanishes: integrate x from 0 to s when 0<=s<=1,
and from s-1 to 1 when 1<=s<=2, with y=s-x. This follows from the line
primitive h''(x)h'(y)-h'(x)h''(y) for k1, and the corresponding primitive
s/2 times this expression plus (h''(x)h(y)-h(x)h''(y))/2 for k2.
All primitive boundary values vanish since h,h',h'' vanish at 0 and 1.

The square integrals are

  H1(t)=F(t,t)=-6t^4(t-1)^4(2t^2-2t+1),
  H2(t)=F2(t,t)=t H1(t).

Consequently H1 H2'-H2 H1'=H1^2, with strictly positive integral over (0,1).
All these identities and strict positivity are Lean theorems in the module.
SymPy independently gives the exact value 74/1616615; that exact rational
value is not used by, or asserted as a theorem in, the Lean module.

Extend k1,k2 by zero outside [0,1]^2. The extended kernels are bounded
piecewise polynomial; they are NOT claimed to be globally smooth.
Boundary values do not affect any integral below.

## 2. Rescaling

Take a=7/20, b=3/8, delta=b-a=1/40, and c=3/5. In particular,

  a>1/3, b<1-c, 2a>c, 2b<1, and 1-2a<a.

For u=(x-a)/delta and v=(y-a)/delta, define the bounded supported kernels

  K1(x,y)=k1(u,v),
  K2(x,y)=a k1(u,v)+delta k2(u,v)

on (a,b)^2, zero elsewhere. Their row integrals and their integrals on every
sum line vanish by an affine change of variables. Hence the integral of Ki
over x+y<r vanishes for every r (integrate the zero sum-line integrals).

Let A_i(t)=integral_{x<=t,y<=t} Ki(x,y) dx dy. For t in (a,b),

  A1(t)=delta^2 H1((t-a)/delta),
  A2(t)=t A1(t).

For t outside (a,b), both are zero. Thus the extended CDFs are absolutely
continuous and integral(A1 A2'-A2 A1')=integral A1^2>0.

## 3. A PD(1) weighted factorial density

Let P be a PD(1) mass partition, interpreted as its point measure of atoms.
Its ordered k-th factorial-moment density is

  rho_k(z_1,...,z_k)=1/(z_1 ... z_k) for z_j>0, sum_j z_j<1.

The corresponding factorial Palm distribution has a residual PD(1)
partition scaled by 1-sum_j z_j. Equivalently, the higher factorial densities
can be used directly in the following overlap expansion.

Define the bounded partition functions

  f_i(P)=sum_{ordered distinct atoms x,y of P} x y Ki(x,y).

There are at most two atoms in (a,b), because 3a>1, so these functions are
bounded. The factorial formula gives E f_i=integral Ki=0. The ordered pair
convention exactly matches rho_2; NO factor of 1/2 is present.

For fixed inserted ordered atoms z_1,...,z_k of total mass s<1, multiply
their factorial density by the conditional expectation of f_i and expand
according to its overlap with the inserted atoms. Dividing by rho_k gives
exactly:

  (I) integral_{x+y<1-s} Ki(x,y) dx dy;
  (II) 2 sum_j z_j integral_{0<y<1-s} Ki(z_j,y) dy;
  (III) sum_{j!=l} z_j z_l Ki(z_j,z_l).

The factor 2 in (II) accounts for the two orders of the pair. Term (I)
uses rho_{k+2}/rho_k=1/(xy), cancelling its xy weight. Term (II) uses
rho_{k+1}/rho_k=1/y, cancelling y but leaving z_j. Term (III) has no
additional residual integration. These observations also derive the formula
without invoking a separate Palm theorem.

If s<c, every term vanishes:
- (I) by sum-line cancellation;
- (II) because 1-s>1-c>b, so the whole row support is integrated;
- (III) because two support atoms have sum >2a>c>s.

Thus EVERY f_i-weighted factorial density of mass <c is zero, not merely
some finite list of moments. k=0 is included via (I).

## 4. Fixed-PD-marginal asymmetric coupling

Start with independent PD(1) partitions P,Q. For sufficiently small positive
epsilon, perturb their product-law density by

  1+epsilon*(f_1(P)f_2(Q)-f_2(P)f_1(Q)).

Boundedness makes this density strictly positive for an appropriate epsilon.
Its integral is 1, and both marginals remain EXACTLY PD(1), since E f_i=0.

The perturbation to any mixed factorial density is the antisymmetric product
of the two weighted factorial densities in Section 3. If the combined inserted
mass on P and Q is <=1, one side has mass <=1/2<c, so both of that side's
weighted densities vanish. Hence all mixed factorial densities on the full
low-mass simplex are unchanged from independence. By integration, the same
holds for every integrable factorial test supported in that simplex.

## 5. Largest-atom order bias

When Ki(x,y) is nonzero, x,y in (a,b), and all other atoms have total mass
1-x-y<1-2a<a. Thus x and y are the two largest atoms. By rho_2,

  E[f_i(P) * 1_{largest(P)<=t}] = A_i(t).

Indeed for t<a both sides are zero; for t>=a the residual largest-atom
constraint is automatic, while x,y must lie below t. The support also gives
x+y<1 automatically (2b<1).

Under the perturbed coupling, the change in the rising comparison probability
Pr(largest(P)<largest(Q)) is

  epsilon * integral [A1(t) A2'(t)-A2(t) A1'(t)] dt
  = epsilon * integral A1(t)^2 dt > 0.

The largest PD(1) atom has a continuous distribution. Its independent copies
therefore have equality probability zero, as does any absolutely continuous
perturbation of their product law. The original rising probability is 1/2,
and the perturbed one is strictly larger than 1/2.

## Scope

This supplies, at the mathematical level using the stated standard PD(1)
factorial law, a fixed-PD-marginal obstruction to deriving order symmetry
solely from the low-total-mass mixed factorial data. It does NOT construct
a sequence of integers with that joint limit, nor claim compatibility with
all arithmetic constraints, dilation identities, or high-mass observations.
Only the explicit unit-square kernel calculus is currently Lean-checked.
The original conjecture in Spec.lean still has no completed proof/disproof.
