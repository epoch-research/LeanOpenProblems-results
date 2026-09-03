# Higher-degree auxiliary polynomials: unresolved nonvanishing

This is exploratory mathematical analysis, not a Lean-verified result and
not a solution of Erdős 68. `Submission/Spec.lean` remains unchanged.

The previously verified Lambert regrouping gives

    f(z) = sum_(d>=2) z^d/(d!-z^d)
         = sum_(m>=0) A_m z^m/m!,
    A_m in Z,   f(1)=alpha.

It is analytic on |z|<sqrt(2). Integer factorial-scaled coefficients are
preserved by products and by multiplication by integer polynomials.
Consequently equations requiring a polynomial P(z,f(z)) to vanish to high
order at zero become integer linear equations after multiplying the equation
at degree m by m!.

## A direction beyond fixed-degree Padé tests

Allow both degrees of P(z,X) to vary, with many more coefficients than
vanishing conditions. In a prospective Siegel-lemma construction, increasing
the degree in X could reduce the coefficient-height cost per unknown.
Analytic estimates on a fixed circle 1<R<sqrt(2) could then control the
remainder at z=1.

No fully quantified construction or Lean theorem asserting these bounds has
been obtained here. In particular, the earlier failed fixed-degree Padé
experiments do not establish impossibility for this different regime.

## The decisive missing condition

Even a nonzero integer polynomial

    Q(X)=P(1,X)

with very small |Q(alpha)| does not by itself prove irrationality. Under
alpha=p/q, q^(degree Q)*Q(alpha) is an integer, but it could be exactly zero.
A sequence of auxiliary polynomials all having the factor q*X-p would be
fully compatible with rationality.

One would need, for example:

* nonzero values Q(alpha) with quantitative smallness relative to the degrees;
* rational-root-free Q with that smallness; or
* sufficiently controlled independent Q with no common rational root.

A homogeneous kernel-dimension or pigeonhole argument alone does not supply
any of these. A determinant bound for the solution lattice does not by itself
bound the size of a solution in a prescribed affine congruence class, nor the
last successive minimum needed to escape a specified hyperplane.

Transcendence of f as a function would also be insufficient: it excludes
P(z,f(z)) vanishing identically, not vanishing at the single point z=1.
For comparison, the transcendental entire function

    h(z)=1+(z-1)*exp(z)
        =sum_(n>=2) (n-1)*z^n/n!

has nonnegative integer factorial-scaled coefficients and h(1)=1.
It shows why analyticity, factorial-scaled integrality, and functional
transcendence alone cannot close this particular nonvanishing gap.

## Status

No suitable nonvanishing argument for the exact Lambert function has been
found. No proof or disproof of the original conjecture has been submitted.
