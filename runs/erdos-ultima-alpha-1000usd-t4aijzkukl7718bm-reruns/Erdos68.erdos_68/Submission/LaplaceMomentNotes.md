# Laplace and Laguerre moments (not a solution)

This is mathematical analysis, not a Lean-verified proof. No change to
`Submission/Spec.lean` follows from it.

Let

    F(z) = sum_(n>=2) z^n/(n!-1),
    G(z) = F(z) - (exp(z)-1-z)
         = sum_(n>=2) z^n/[n! (n!-1)].

Both functions are entire. Write alpha=F(1).

## Laplace identities

For real 0<x<1, termwise positive integration gives

    integral_0^infinity exp(-t) F(tx) dt - F(x) = x^2/(1-x).

Indeed the integral multiplies the coefficient of x^n by n!, so the
coefficient of the difference is exactly 1 for n>=2. At x=1 this integral
of F diverges; it cannot be substituted into the identity there.

In contrast,

    integral_0^infinity exp(-t) G(t) dt = alpha.

For each polynomial P(t)=sum_(j=0)^m p_j t^j its weighted integral exists
absolutely and equals

    integral_0^infinity exp(-t) P(t) G(t) dt
      = sum_(n>=2) W_P(n)/(n!-1),

where

    W_P(n) = sum_(j=0)^m p_j (n+1)(n+2)...(n+j).

The product for j=0 is 1. Absolute convergence follows because W_P grows
polynomially and the denominators grow factorially. Thus arbitrary polynomial
kernels introduce polynomially weighted versions of the original sum.

The rising-factorial polynomials have distinct degrees and leading
coefficient 1. Consequently W_P can be constant at every sufficiently large
integer only if P is constant. In particular a nonzero polynomial kernel
cannot simultaneously annihilate some initial coefficient contributions and
retain a fixed nonzero constant weight on all later contributions. This is
an obstruction to that specific coefficientwise construction, NOT a theorem
excluding more general relations among weighted sums.

## Laguerre kernels

For the ordinary Laguerre polynomial

    L_m(t) = sum_(j=0)^m (-1)^j binomial(m,j) t^j/j!,

its monomial moment is

    integral_0^infinity exp(-t) t^n L_m(t) dt
      = (-1)^m n! binomial(n,m).

Hence

    integral_0^infinity exp(-t) L_m(t) G(t) dt
      = (-1)^m sum_(n>=2) binomial(n,m)/(n!-1).

For m>=2, multiplying the unsigned right side by m! gives exactly

    sum_(k>=0) (m+k)!/[k! ((m+k)!-1)]
      = exp(1) + sum_(k>=0) 1/[k! ((m+k)!-1)]
      = exp(1) + G^(m)(1).

The final positive correction tends to zero: it is at most
exp(1)/(m!-1). Thus these unscaled integrals tend to zero, but their scaled
limits involve exp(1) and derivatives of G, not just alpha. Rationality of
alpha does not make these forms integers.

## Constant-kernel derivatives

For N>=2, differentiation and positive termwise integration give

    integral_0^infinity exp(-t) G^(N)(t) dt
      = sum_(n>=N) 1/(n!-1).

Equivalently, integration by parts subtracts the rational boundary values
G^(j)(0)=1/(j!-1) for j>=2 (the first two boundary values are zero).
This produces precisely the ordinary partial-sum errors. It supplies no
new small-denominator approximants by itself.

## Status

No integer-valued nonzero forms tending to zero under a rationality
assumption have been constructed. The exact factorial denominator recurrence
also still lacks a rational numerator-descent or multiplier-growth argument.
The original conjecture remains unproved and undisproved in this work.
