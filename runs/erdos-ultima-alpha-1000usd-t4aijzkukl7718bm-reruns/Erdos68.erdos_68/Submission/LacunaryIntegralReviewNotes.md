# Lacunary monomial integral review

Informal mathematical review, NOT a Lean theorem and NOT a settlement of
Erdős 68. Spec.lean remains unchanged with its original sorry. No proof or
disproof has been submitted.

For x in [0,1), put f(x)=sum_(n>=2) x^(n!-2). Positive termwise integration
represents alpha as integral_0^1 f(x) dx. A polynomial weight
P(x)=sum_(j=0)^m c_j*x^j instead gives

    integral_0^1 P(x)*f(x) dx
      = sum_(j=0)^m c_j * sum_(n>=2) 1/(n!+j-1).

These shifted sums cannot be treated as rational constants under the sole
assumption that alpha is rational.

In particular the beta weight (1-x)^m gives the positive expression

    I_m=sum_(n>=2) m!/[(n!-1)*n!*...*(n!+m-1)]
       =sum_(j=0)^m (-1)^j choose(m,j)
                         *sum_(n>=2) 1/(n!+j-1).

For m=0 the denominator product is the single factor n!-1. Although these
weighted integrals decrease to zero, the displayed expansion supplies no
integer linear form in alpha alone. The j=1 term already introduces e-2;
higher j introduce further shifted-factorial constants. No elimination
with controlled integral coefficients was found.

Root-of-unity filtering of the factorial exponents was also reconsidered
against SparseSeriesNotes.md. It does not by itself remove the extra
boundary constants. Earlier rational comparison series already caution
against inferring irrationality from lacunarity, eventual congruences,
or algebraic boundary values alone.

No new numerical search or formal theorem was produced in this review.
There is no complete informal argument awaiting formalization, and the
original conjecture remains unresolved in this workspace.
