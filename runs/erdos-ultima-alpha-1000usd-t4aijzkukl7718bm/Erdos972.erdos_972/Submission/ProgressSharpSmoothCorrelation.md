# Sharper smoothing comparison — original conjecture still unresolved

Spec.lean is unchanged with its original sorry. No lower bound for the
smoothed correlation in the comparison regime, no sufficient signed
four-factor gap, and no irrational counterexample have been proved.
No proof submission was made.

## SharpSmoothMangoldt.lean

Namespace Erdos972SharpSmoothMangoldt.

The Euler product provides an improvement over the earlier divisor-cardinality
Taylor bound:

    |S(t,n)-Lambda(n)| <= t (log n)^2, for EVERY t>0 and n>=0.

There is no tau(n) factor and no hypothesis t log n<=1.

Proof:
- If n is a prime power p^k, the full smooth weight is
  (1-exp(-t log p))/t. For t log p<=1 use the exponential remainder bound;
  for t log p>=1 use 0<=S<=log p. Both give t (log p)^2.
- If n>1 is not a prime power, there are distinct prime factors p,q.
  Each Euler factor lies in [0,1], so the full product is at most the
  product of the p and q factors, at most t^2 log p log q.
- The n=0 and n=1 conventions are handled explicitly.

## SharpSmoothCorrelation.lean

Namespace Erdos972SharpSmoothCorrelation. Defines

    E(alpha,t,N)=t [1+log(floor(alpha*N))]^2.

A pointwise expansion around the actual Mangoldt factors gives

    |S(t,m)S(t,n)-Lambda(m)Lambda(n)|
      <= E [Lambda(m)+Lambda(n)] + E^2

whenever both pointwise errors are at most E.

Instead of replacing both Mangoldt factors by their logarithmic maxima,
the proof sums them using Chebyshev's linear bound. Injectivity of
floor(alpha*n), alpha>=1, gives the corresponding output first moment.
Thus for all N and all t>0,

    |smoothCorrelation(t,alpha,N)-mangoldtCorrelation(alpha,N)|
      <= [(log 4+4)(1+alpha) E(alpha,t,N)+E(alpha,t,N)^2] N.

Consequently, for any eventually positive t_N,

    t_N [1+log(floor(alpha*N))]^2 -> 0

implies normalized signed correlation error ->0. This is stronger than
the preceding comparison theorem. A concrete choice is now

    cubeParameter(alpha,N)=1/[1+log(floor(alpha*N))]^3,

rather than the earlier inverse fifth power.

## The remaining incompatibility is retained explicitly

sharp_regime_damping_tendsto_one verifies that throughout this improved
comparison regime, for ANY D_N<=N eventually,

    exp(-t_N log D_N) -> 1.

Thus the improved comparison still cannot simply be combined with the
proved divisor-tail estimates that need this damping factor to vanish.
This assertion concerns the damping factor, NOT a lower bound on the
actual signed tail. A stronger signed-tail/cross-correlation estimate may
still be possible; none is supplied here.

AuditSharpSmoothCorrelation.lean compiles and audits eight principal
results with only propext, Classical.choice, and Quot.sound.
