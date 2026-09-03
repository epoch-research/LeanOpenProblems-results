# Actual Gaussian-ideal collisions: exact finite support bounds

These statements concern actual finite sets in a bounded integer square. They
neither prove nor disprove the unrestricted planar conjecture in Spec.lean.

Let P be a subset of {1,...,L}^2, n=|P|>=2. Let D(P) count positive squared
distances. Let S(x) count positive integers <=x that are sums of two integer
squares, for a real argument x. Put Q=floor(4L^2/n), so Q>=4, and

  C(n) = S(n-1)-S(ceil(n/2)-1).

## 1. Pigeonholing actual endpoints

For every norm integer m with n/2<=m<n, fix beta in Z[i] with N(beta)=m.
Multiplication by beta has integer determinant m, hence the additive quotient
Z[i]/(beta) has exactly m elements. Two of the n actual points collide in
this quotient. Their nonzero difference is beta*gamma for some Gaussian
integer gamma. Thus the actual squared distance d satisfies

  d=m*q,  q=N(gamma)>=1,
  q <= 2(L-1)^2/m <= 4L^2/n.

Choose one such d for each m. At a fixed d, the different possible m produce
different q=d/m, each of which is counted by S(Q). Therefore the exact bound

  D(P) * S(Q) >= C(n)

holds. No passage from an ambient upper capacity to a lower bound is used.

The classical two-sided Landau estimates give, with an absolute positive c,

  D(P) >= c * (n^2/L^2)
               * sqrt(log(2+L^2/n)/log(2+n)).

The finite initial range can be absorbed in c. This bound retains a density
and height loss and is not a solution for arbitrary integer sets.

## 2. Injecting rough norms into actual distance labels

Let B_Q(x) count those positive norm integers <=x having no prime factor
<=Q. Restrict m above to such integers. In d=m*q every prime factor of q is
<=Q, whereas every prime factor of m is >Q. Hence m is exactly the part of
d supported on primes >Q. In particular the choice m -> d is injective.
This proves the stronger exact bound

  D(P) >= B_Q(n-1)-B_Q(ceil(n/2)-1).

For a squarefree integer d supported on primes <=Q define nu multiplicatively
by nu(2)=2, nu(p)=p for p=1 mod 4, and nu(p)=p^2 for p=3 mod 4. Unique
factorization, or the norm criterion, gives the exact inclusion-exclusion

  B_Q(x) = sum_(d | product_(p<=Q) p) mu(d)*S(x/nu(d)).

For each fixed Q the Landau asymptotic gives

  B_Q(x) ~ kappa*eta(Q)*x/sqrt(log x),
  eta(Q) = product_(p<=Q) (1-1/nu(p))
          asymp 1/sqrt(log(2Q)).

A quantitative uniform version follows from the usual first Landau error
S(y)=kappa*y/sqrt(log y)+O(y/log(y)^(3/2)), Chebyshev's theta bound, and
expanding the square root in this finite inclusion-exclusion. In particular
there is an absolute C such that log n>=C Q ensures

  B_Q(n-1)-B_Q(ceil(n/2)-1)
     >= c*n/(sqrt(log n)*sqrt(log(2Q))).

To check uniformity: log nu(d)<=2 theta(Q)=O(Q), so all arguments are a
fixed positive power of n. The weighted absolute error is controlled by
product(1+1/nu(p))=O(sqrt(log(2Q))) and the logarithmic shift by
sum(log nu(p)/(nu(p)+1))=O(log(2Q)). Their relative contribution is
O(log(2Q)^2/log n), small for the stated sufficiently large C. Interval
endpoints do not affect the leading constant. This is a mathematical argument
using classical analytic number theory, not a verified Lean formalization.

For fixed positive density delta, n>=delta L^2 makes Q<=4/delta. Eventually,

  D(P) >= c * delta/sqrt(log(2/delta)) * L^2/sqrt(log L).

All endpoints here are actual elements of P. The constants and starting
threshold must not be used as though density- or height-free. Nor is there
a justified reduction of arbitrary real planar configurations to dense
integer sets.
