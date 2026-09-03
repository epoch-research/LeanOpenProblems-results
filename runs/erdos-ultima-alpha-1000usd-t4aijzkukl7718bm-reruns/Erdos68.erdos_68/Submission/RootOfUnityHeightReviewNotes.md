# Quantitative factorial-root boundary review

Informal mathematical analysis only, NOT a Lean theorem and NOT a proof or
disproof of Erdos 68. `Spec.lean` is unchanged with its original sorry.

Put

    F(z)=sum_(n>=2) z^(n!-1)/(n!-1),  alpha=F(1).

The series converges absolutely on the closed unit disk. For N>=3 and
zeta^(N!)=1, factorial divisibility gives the exact identity

    zeta*F(zeta)
      =alpha+sum_(n=2)^(N-1) (zeta^(n!)-1)/(n!-1).

Thus all N!-th-root boundary values are represented by the same polynomial

    P_N(z)=alpha-S_(N-1)+sum_(n=2)^(N-1) z^(n!)/(n!-1),

whose degree is only (N-1)!. This is a stronger quantitative feature than
merely having algebraic boundary values under rationality of alpha. The
older sparse rational comparison does not retain this same degree bound
relative to the root order.

If alpha=a/q, q>0, the coefficients of P_N have a common denominator
dividing

    q*D_(N-1),  D_(N-1)=product_(n=2)^(N-1)(n!-1).

The logarithm of this upper bound is O(N^2 log N) for fixed q. However,
the constant coefficient is exactly the positive original tail
alpha-S_(N-1), of order 1/N!. Clearing that coefficient with q*D_(N-1)
does NOT give a small positive integer: the product denominator is much
larger than N!. Also, the interpolation points lie on the boundary of the
analytic disk. No interior interpolation estimate or analytic continuation
across the natural boundary has been established or may be inferred from
the displayed finite identities.

A related local observation was reviewed: for n>=p and a prime p,

    1/(n!-1)+1 = n!/(n!-1)

has p-adic valuation v_p(n!). Consequently the direct generating series,
after subtracting its eventual geometric coefficient part, has improved
p-adic coefficient decay. This does not identify its real value at one
with a p-adic value. In particular, no contradiction follows just from
different real and p-adic boundary behavior. No adelic height estimate
sufficient for an irrationality proof was obtained.

The physical positive-kernel and modified Engel approaches were also
reconsidered against their existing notes. No controlled integer matrix
family, integer-height descent, or infinite carry violation resulted.

No new numerical search, Lean declaration, or submission check was made.
There is no complete informal solution awaiting formalization. Nothing is
pending compilation or computation.
