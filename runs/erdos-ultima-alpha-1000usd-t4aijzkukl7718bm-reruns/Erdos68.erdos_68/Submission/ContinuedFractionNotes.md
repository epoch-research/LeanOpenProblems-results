# Continued-fraction investigation (not a proof of Erdős 68)

Let d_n = (n+2)! - 1, S_n = sum_{k=0}^n 1/d_k, and alpha = lim S_n.

Euler's generalized continued fraction for the sum has denominator coefficients

    b_0 = d_0,
    b_n = d_{n-1} + d_n     (n >= 1),

and numerator coefficients

    a_n = -d_{n-1}^2        (n >= 1).

Writing its convergents as P_n/Q_n, its continuant recurrence gives exactly

    Q_n = product_{k=0}^n d_k,
    P_n = Q_n S_n.

These identities follow directly by substituting into

    X_n = (d_{n-1}+d_n) X_{n-1} - d_{n-1}^2 X_{n-2}.

Thus this representation itself gives precisely the original partial sums, not
new rational approximations. Its existence and convergence do not prove
irrationality. In particular, a generalized continued fraction with integral
numerators is not automatically an ordinary simple continued fraction.

## Constant Bauer–Muir modification

For a fixed nonzero rational c, set r_n = -d_n+c. For n >= 1,

    (P_n + r_n P_{n-1}) / (Q_n + r_n Q_{n-1})
      = S_{n-1} + 1/c.

Indeed, the numerator is Q_{n-1}(1+c S_{n-1}) and the denominator
is c Q_{n-1}. Consequently the modified limit is alpha+1/c.

This rational shift DOES preserve irrationality. Merely observing that the
limit changes is not an objection to this transformation. The actual problem
is that the resulting approximants are still just shifted partial sums.
There is no improvement in their approximation errors or denominator growth
apart from the fixed shift and the index change.

The cancellation determinant

    a_n - r_{n-1}(b_n+r_n) = -c^2

can misleadingly look like a route to unit numerators. It does not by itself
make the transformed continued fraction a simple continued fraction: the
remaining coefficient transformation retains the large original factors.
For c=0 the modified denominator vanishes identically, so that case cannot
be used.

For variable nonzero c_n, the same elementary computation gives modified
convergents S_{n-1}+1/c_n. The cancellation determinant instead becomes

    d_{n-1}(c_n-c_{n-1}) - c_n c_{n-1}.

Taking c_n to infinity recovers alpha as the limit but supplies neither
integrality with small denominators nor an irrationality criterion.

## Status

These observations do not prove or disprove the conjecture. No changes to
Submission/Spec.lean have been made as part of this investigation.
