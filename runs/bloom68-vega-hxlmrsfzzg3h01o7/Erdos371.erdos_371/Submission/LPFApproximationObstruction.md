# An actual largest-prime-factor cutoff escapes the periodic–Mellin class

**Status:** analytic partial result, not a Lean proof of either target. This
shows that one cannot finish the present bounded-cut approach by putting all
LPF cutoffs in the small-coefficient approximation class from
`BoundedMultiplierCutResearch.md`. It does not refute the bounded-cut estimate.

Fix `1/2 < alpha < 1` and `0 < delta < alpha`. Let `H=floor(X^delta)`,
`y=X^alpha`, and put, on the full product interval `[1,HX]`,

    F_X(m) = 1_{P(m)>y},       f_X(n)=F_X(n) (n<=X),
    c = -log(alpha),           h_X(n)=f_X(n)-c.

Here all integer variables are positive. In particular `0<c<1` and `|h_X|<=1`.
Let `mu(a)=#{(k,n):k<=H,n<=X,kn=a}/(HX)` be incidence probability measure.

## 1. Exact multiplicative invariance and a uniform counting estimate

Since `H<=y`, `F_X(kn)=f_X(n)` for every relevant `k,n`: multiplication by
`k` cannot introduce a prime above `y`. Likewise `f_X(dr)=f_X(r)` whenever
`d<=q<y` and `dr<=X`.

For `S(v)=sum_{n<=v} f_X(n)`, uniqueness of a prime divisor above `y` when
`n<=X<y^2` gives the exact formula

    S(v) = sum_{y<p<=v} floor(v/p)       (1<=v<=X).

Mertens' reciprocal-prime estimate with error `O(1/log y)`, and Chebyshev's
prime-counting upper bound, imply uniformly for `y<=v<=X`

    S(v) = v log(log(v)/log(y)) + O_alpha(v/log X).

For `v<y`, `S(v)=0`. Combining the two cases, and absorbing the difference
between `v` and `floor(v)`, gives

    |sum_{n<=v}(f_X(n)-c)|
      <= C_alpha v (1+log(X/v))/log X.                  (1)

For the first case use `log(v)/log X >= alpha`; for the second use
`log(X/v)>=(1-alpha)log X`. The floor error is absorbed because
`v(1+log(X/v))/log X >= 1` for `1<=v<=X`, once `X` is large.
In particular `X^{-1}sum f_X = c+O_alpha(1/log X)`.

## 2. Covariance with small-period divisor-class functions

For a `q`-periodic function `p` with `|p|<=1`, define

    g(n) = (1/q) sum_{r=1}^q p(rn).

Multiplication modulo `q` shows that `g(n)` depends only on `gcd(n,q)`.
Consequently, by finite divisor Möbius inversion,

    g(n)=sum_{d|gcd(n,q)} b_d,  b_d=sum_{e|d} mu(d/e)g(e),
    |b_d|<=tau(d),            sum_{d|q}|b_d|/d <= q^2.   (2)

The crude last bound suffices. Assume `q<y`. Applying (1) to the progression
`n=dr` is legitimate because `f_X(dr)=f_X(r)`. Thus

    |sum_{n<=v} h_X(n)g(n)|
      <= C_alpha q^2 v (1+log q+log(X/v))/log X.         (3)

Terms `d>v` are empty. Partial summation of (3), using
`integral_1^X log(X/v) dv <= X`, gives, for every real `t`,

    |X^{-1}sum_{n<=X} h_X(n)g(n)n^(it)|
      <= C_alpha q^2(1+log q)(1+|t|)/log X.             (4)

This argument uses only divisibility classes, NOT equidistribution of primes
or smooth numbers in general arithmetic progressions.

## 3. All the permitted dictionary atoms have negligible covariance

Let `A_H L(n)=H^{-1}sum_{k<=H} L(kn)`. Retain the frequency window `T_H` and
high-frequency bound `E_H` from `BoundedMultiplierCutResearch.md`. For an atom
`L(m)=p(m)m^(it)`, the partial-summation identity there is

    A_H L(n) = M_H(t)n^(it)g(n)
                + O(q(1+|t|log H)/H),  |M_H(t)|<=1.

For `|t|<=U`, (4) controls its covariance with `h_X`. For
`U<|t|<sqrt H`, the pointwise bound is
`||A_H L||_infty << 1/U+q log H/sqrt H`; for
`sqrt H<=|t|<=T_H`, the previously audited derivative estimate is
`||A_H L||_infty << E_H`. Therefore, uniformly for periods `q<=Q` and
frequencies `|t|<=T_H`,

    |X^{-1}sum h_X(n) A_H L(n)| <= C_alpha eta,

where

    eta = Q^2(1+log Q)(1+U)/log X
          + Q(1+U log H)/H + 1/U + Q log H/sqrt H + E_H. (5)

Take `U=(log X)^(1/4)`, `Q=(log H)^beta`, `0<=beta<gamma`, and
`W_0=(log H)^((gamma-beta)/6)`, where
`gamma=1-(1+log(log 2))/log 2` is the positive Ford exponent, less than `1/10`.
At fixed `delta>0`, `W_0 eta -> 0`. Indeed the first logarithmic power is at
most `gamma/6+2gamma+1/4-1<0`; the `1/U` term has exponent at most
`gamma/6-1/4<0`, and the remaining terms decay faster than any fixed negative
power of `log X`.

## 4. A positive incidence-distance lower bound

For any finite model `P=sum_j a_j L_j` with the permitted periods and
frequencies, and `sum_j|a_j|<=W_0`, incidence duality and `|h_X|<=1` imply

    ||F_X-P||_{L1(mu)}
      >= |X^{-1}sum h_X(n)(A_H F_X(n)-A_H P(n))|
      >= (1-c) X^{-1}sum f_X(n) - C_alpha W_0 eta
      = c(1-c)-o(1).                                   (6)

This is uniform over all such models. Since `c(1-c)>0`, the very LPF cutoffs
relevant to ordering already escape the model class. This is stronger than
merely noting that no approximation theorem has been proved.

**Limits of the conclusion:** (6) does not show a nonzero adjacent current,
does not give a counterexample to the residual cut estimate (13a), and does
not settle Erdős 371. It rules out a specific small-budget approximation
shortcut. The proof invokes classical analytic estimates and the prior
high-frequency lemma; it has not been formalized in Lean. `Spec.lean` is
unchanged.

### Audit

The Mertens error used above follows by partial summation from
`sum_{p<=z} (log p)/p = log z + O(1)`: the tail of the integrated error is
`O(1/log z)`. In (3), the discrepancy is against `c floor(v/d)`, not
`c v/d`; the floor correction has already been included in (1). Partial
summation in (4) uses the local `v log(X/v)` bound, so there is no spurious
additional factor of `log X`. The comparison in (6) uses the incidence
measure, not uniform counting measure on `[1,HX]`.

Finite exact-rational checks verified (2) for moduli through 30, and cutoff
invariance and the unique-large-prime count on three small parameter sets.
They are consistency checks only, not substitutes for the arguments above.
The specification was recompiled and still has exactly its two original
`sorry` warnings, with unchanged SHA-256
`d48bb112dcd4fd5c98dae80077b7384df62a14ef9a919fe7d476b9c5ace427bb`.
