# Harmonic-scale attempt: exact reduction and a scalar obstruction

**Status.** This is a mathematical partial result, not a proof or disproof of
`Spec.lean`. The specification is unchanged. No statement here uses either
sorry-bearing declaration in that file. The new arguments below have not been
formalized in Lean; the safe-gluing and window inequalities they refer to
already have separate Lean proofs in this directory.

## 1. The extremal-density series is an exact criterion

Fix an integer k >= 3. Let r(N) be the largest size of a subset of [0,N)
containing no nonconstant k-term arithmetic progression. Translation gives the
same extremal number for [1,N]. Put

    rho_j = r(3^j)/3^j,
    S = sum_{j>=0} rho_j,
    T = sum_{n>=1} r(n)/(n(n+1)),
    M = sup { sum_{a in F} 1/a : F is finite, positive, and k-AP-free }.

All three quantities may take the value infinity. Then

    S/3 <= M <= (3/2) S,
    (2/3) S <= T <= 2 S,
    M <= T <= 6 M.

In particular, the following are equivalent:

* every k-AP-free set of positive integers has convergent reciprocal sum;
* M is finite;
* S is finite;
* T is finite.

### Proof of the lower bound: globally safe blocks

For every j choose a k-AP-free E_j in [0,3^j) of size r(3^j), and set

    B_j = 2*3^j + E_j,
    B = union_{j>=0} B_j.

The crucial assertion is that **B is globally k-AP-free**, not merely that each
block is free.

Indeed, no nonconstant progression of length at least three can cross between
X contained in [1,L] and Y contained in [2L,3L). A crossing step has size at
least L, whereas a step between two points of either one of these intervals has
size at most L-1. A monotone progression using both intervals, with at least
three terms, has both a crossing step and an adjacent pair in one interval.
These cannot have the same difference. (Reflect a negative difference to make
it positive.)

Before adding B_j, all earlier blocks lie in [1,3^j]. Thus this observation,
inductively with L=3^j, proves that every finite union of the B_j is k-AP-free.
Every finite progression in B would lie in one such finite union, so B itself
is k-AP-free.

Every element of B_j is positive and less than 3^(j+1), so

    sum_{b in B_j} 1/b >= rho_j/3.

The same lower bound holds after summing any finite collection of initial
blocks. Hence S/3 <= M. Moreover, if S diverges, the displayed B is an actual
globally k-AP-free set with divergent reciprocal sum. This last statement is
conditional on divergence of S: no such divergence for actual r_k has been
established here.

### Proof of the upper bound

Partition the positive integers into intervals

    [3^j,2*3^j) and [2*3^j,3^(j+1)),   j >= 0.

Each interval has length 3^j, and the intersection of a k-AP-free F with it has
at most r(3^j) elements. The reciprocal weight of these two intersections is at
most rho_j and rho_j/2 respectively. Therefore M <= (3/2) S. This also directly
bounds the reciprocal sum of every infinite k-AP-free set when S is finite.

### Proof of the comparison with T

The elementary partition inequality is

    r(u+v) <= r(u)+r(v).

For 3^j <= n < 3^(j+1), monotonicity and this inequality give

    r(3^j) <= r(n) <= r(3^(j+1)) <= 3 r(3^j).

Also

    sum_{n=3^j}^{3^(j+1)-1} 1/(n(n+1)) = 2/(3*3^j).

Summing proves (2/3) S <= T <= 2 S. Finally, for finite positive F,

    sum_{a in F} 1/a
      = sum_{n>=1} |F intersect [1,n]|/(n(n+1)) <= T,

by telescoping each 1/a. Thus M <= T, and T <= 2S <= 6M.

### A necessary quantitative consequence

Subadditivity implies rho_(j+1) <= rho_j. If S is finite, monotonicity gives

    j*rho_j <= 2 sum_{i=floor(j/2)}^j rho_i -> 0.

If 3^j <= N < 3^(j+1), then r(N)/N <= 3 rho_j and
log N <= (j+1) log 3. Consequently, for all N, not just powers of three,

    r(N) = o(N/log N).

So proving the conjecture by a qualitative argument would still imply a new
pointwise logarithmic improvement for each k. Conversely, merely proving
r(N)=o(N/log N) would not establish convergence of S: a comparison sequence of
order 1/(j log j) still diverges.

The sufficient estimate requested in the prompt,

    r_k(N) <= C_k N/[log N (log log N)^(1+epsilon_k)],

would give rho_j = O_k(1/[j (log j)^(1+epsilon_k)]) and hence S < infinity.
The exact missing assertion in this route is S < infinity for every fixed
k >= 3; a fixed epsilon_k power saving is sufficient but is not asserted to be
necessary.

## 2. The existing window inequality does not force this convergence

The proved window estimate has the form

    (m+c) r(N) <= N r(m) + sum_{t=1}^m r(t),   c=1/(k-1).

Here is an integer-valued countermodel to extracting summability from this
estimate, subadditivity, monotonicity, and qualitative decay alone. This is a
countermodel to a collection of scalar constraints, **not** an AP-free set or
an assertion about the true extremal numbers.

For x >= 1 and positive integer n, define

    f(x) = x/(1+log x),
    g(n) = ceil(f(n)),
    R_k(n) = min(n, max(k-1, g(n))),
    R_k(0) = 0.

For every fixed k >= 3, R_k has all the following properties:

1. It is integer-valued, nondecreasing, and between 0 and n.
2. Its successive increments are 0 or 1.
3. R_k(u+v) <= R_k(u)+R_k(v).
4. R_k(n)=n for n<k, and R_k(k)=k-1.
5. R_k(n)/n -> 0, but R_k(n) ~ n/log n.
6. For every m>=1 and N>=1,

       (m+1/(k-1)) R_k(N)
         <= N R_k(m) + sum_{t=1}^m R_k(t).

7. sum_{j>=0} R_k(3^j)/3^j diverges.

This shows that the window inequality cannot, even together with these usual
scalar properties, supply the missing harmonic estimate. Additional
combinatorial information is needed.

### Elementary properties

One computes

    f'(x) = log x/(1+log x)^2,
    f''(x) = (1-log x)/(x(1+log x)^3).

Thus f is nondecreasing, its derivative is at most 1/4, and f(x)/x is
nonincreasing. In particular g is nondecreasing, with integer increments at
most one. Taking the maximum with a constant and the minimum with n preserves
these two properties.

For subadditivity define the real-valued function on positive integers

    q_k(n) = min(n, max(k-1,f(n))).

The ratio

    q_k(n)/n = min(1, max((k-1)/n, 1/(1+log n)))

is nonincreasing. Therefore q_k(u+v) <= q_k(u)+q_k(v) for positive u,v.
Since R_k(n)=ceil(q_k(n)), the same inequality holds for R_k, by
ceil(a+b) <= ceil(a)+ceil(b). A zero argument is immediate.

The initial values follow from f(k)<=k-1 for k>=3. The asymptotic formula follows
because f(n) tends to infinity, so eventually R_k(n)=ceil(f(n)). Finally,

    R_k(3^j)/3^j >= f(3^j)/3^j = 1/(1+j log 3),

which proves divergence.

### The window inequality for g

It suffices first to prove the estimate with c=1/2 and r replaced by g.

If N<=m, monotonicity gives

    N g(m)+sum_{t=1}^m g(t)
      >= N g(N)+(m-N+1)g(N) = (m+1)g(N).

Assume N>m>=5. Since f is concave for x>=5,

    D(x) = x f(m) - (m+1/2) f(x)

is increasing for x>=m: indeed

    D'(x) >= f(m)-(m+1/2)f'(m)
           = (m-(log m)/2)/(1+log m)^2 > 0.

Consequently D(N)>=D(m)=-f(m)/2. Using f(n)<=g(n)<=f(n)+1,

    N g(m)+sum_{t=1}^m g(t)-(m+1/2)g(N)
      >= sum_{t=1}^m f(t)-f(m)/2-m-1/2 =: H(m).

The increment of H is

    H(m+1)-H(m) = (f(m+1)+f(m))/2-1 >= 0.

Also H(5)>2/15>0. For a rational verification, use log 4<3/2 and log 5<2:

    f(1)=1, f(2)>=1, f(3)>6/5, f(4)>8/5, f(5)>5/3,

so

    H(5)>1+1+6/5+8/5+5/6-11/2 = 2/15.

(The elementary inequalities e<3, log 4<3/2, and log 5<2 used here can be
obtained from the exponential series and the trapezoidal bound
log 2 < (1+1/2)/2.)

For m=1,2,3,4, the values of g(m) are 1,2,2,2 and their prefix sums are
1,3,5,7. For N>=3, log N>1, so g(N)<=N/2+1. This proves all cases m<=3,
apart from m=1,N=2, where the inequality is equality. For m=4, the same bound
works for 5<=N<=8 (indeed up to 10); for N>=9, log N>2, and the stronger
bound g(N)<=N/3+1 proves the estimate. This completes all cases for g.

### Passing to the actual countermodel R_k

Write K=k-1 and c=1/K<=1/2. Always R_k(n)>=g(n). If R_k(N)=g(N), the proved
inequality for g immediately implies the one for R_k.

In the remaining cases, if N<=m, use the monotonicity argument above. If N>m:

* When N<=K, R_k(N)=N, R_k(m)=m, and the prefix sum is m(m+1)/2. The necessary
  inequality is cN<=m(m+1)/2, which follows from cN<=1.
* When N>=K and R_k(N)=K, if m>=K then R_k(m)>=K and N>=m+1, so the term
  N R_k(m) alone suffices. If m<K, then R_k(m)=m and the prefix sum is at
  least 1=cK; also Nm>=Km. These two facts again give the desired bound.

This proves the window inequality for every m,N, including the rounding and
the initial-value modifications.

## 3. What is actually known or obtained here

* The full specification remains unresolved by this attempt. No genuinely
  k-AP-free divergent set has been constructed.
* Section 1 gives an exact, globally safe gluing criterion. It does not prove
  that the actual extremal-density series converges or diverges.
* Section 2 proves that a bootstrap based only on the existing scalar window
  bound and the listed extremal-number properties cannot prove convergence.
  The model R_k is not realizable evidence for an AP-free construction.
* The supplied corpus does give the actual k=3 case: Bloom--Sisask,
  `2007.03528/Roth.tex`, Theorem 1.1, proves

      r_3(N) << N/(log N)^(1+c), c>0.

  This makes the triadic series convergent and gives reciprocal summability
  for every 3-AP-free set. Removing finitely many points also shows that a set
  of divergent reciprocal sum has infinitely many nontrivial 3-APs.
  This invokes their proved theorem; it is not a new proof of that estimate
  and it has not been imported as an axiom or formalized here.

The precise remaining task for the general theorem is a new bound proving

    for every k>=3,  sum_{j>=0} r_k(3^j)/3^j < infinity,

or, in the opposite direction, an actual k for which this series diverges
(the construction in Section 1 would then give a globally AP-free divergent
set). Neither conclusion follows from the present argument.

## 4. Verification and scope

All logarithms above are natural. The all-index assertions in Section 2 are
justified by the proofs, not by the following supplementary computations:

* Symbolic differentiation confirmed both displayed derivatives and D'(m).
* For k=3,4,5,10,100, an integer-arithmetic check of the cleared-denominator
  window inequality covered all 1<=m,N<=2000: 20,000,000 pairs in total.
  Sage 160-bit real-interval arithmetic separately certified all 2000 ceiling
  values used in these checks. Subadditivity was also checked for all positive
  u,v with u+v<=2000, together with the initial values and unit increments.
* Exhaustive checks for 1<=L<100 found no crossing 3-AP in the full ambient
  set [1,L] union [2L,3L). The proof above establishes the assertion for all L.
* `/tmp/HarmonicScaleAudit.lean` checked the supporting safe-gluing, nested-union,
  window, and conjecture-equivalence lemmas. Their axiom reports contain only
  `propext`, `Classical.choice`, and `Quot.sound`; they do not prove the missing
  estimate. The new series comparison and scalar-countermodel arguments in
  this note are mathematical proofs, not Lean formalizations.
* `Submission/Spec.lean` retained SHA-256
  `a9bf43ac93cdad8588489e5208920139e52899b7c15fdd7270e63caea6c20814`.

