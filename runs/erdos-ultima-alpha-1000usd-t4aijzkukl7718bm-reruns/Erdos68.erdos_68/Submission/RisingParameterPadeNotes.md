# Fixed-parameter rising-factorial expansion (not a settlement)

This is an exact external arithmetic investigation, not a new Lean theorem.
Spec.lean is unchanged and still contains its original sorry. No proof or
disproof has been obtained or submitted.

## Representation distinct from the original coefficient Padé test

For a real parameter n>=2, write

    T(n)=sum_(k>=0) 1/[2*(n+1)(n+2)...(n+k)-1],

with empty product 1. At n=2, the product times 2 is (k+2)!, so T(2)=alpha.
Introducing z=1/(2n) gives the expression

    H(z)=sum_(k>=1) 2^(k-1)*z^k /
         [product_(j=1)^k(1+2*j*z)-2^(k-1)*z^k],
    alpha=1+H(1/4).

The expression for each summand has a formal power-series expansion at zero
with integer coefficients and order k. Thus each formal coefficient of H is
well-defined by finitely many summands. The first coefficients, starting with
constant term, are

    0, 1, 1, -7, 19, -31, 135, -2319, 26511, -212415, ...

No assertion that this formal series converges at 1/4 is made. Nor is a Padé
convergence theorem being asserted. The coefficient arithmetic only defines
rational approximants to be checked separately against an enclosure of alpha.

## Exact finite Padé check

For denominator degree d=1,...,17 and numerator degree m=d-1,d,d+1, solve
exactly for Q(0)=1 and

    [z^k](Q*H)=0,  k=m+1,...,m+d.

Then take P to be the degree-m truncation of Q*H and reduce

    1+P(1/4)/Q(1/4)=a/b.

The (m,d)=(0,1) system is inconsistent with Q(0)=1 (H begins with z).
All other 50 systems were solved. The script verifies their equations with
exact rational arithmetic. No evaluated denominator vanished.

Error certification uses the elementary positive-tail enclosure

    L=sum_(k=2)^100 1/(k!-1),
    L<alpha<U=L+2/(101!-1).

For all completed cases except

    (m,d)=(1,2),(2,3),(1,1),(2,2),(2,1),(3,2),

the exact rational interval [b*L-a,b*U-a] lies entirely outside [-1,1].
The six exceptions have their intervals strictly inside (-1,1).

Some diagnostics, not themselves the certificates:

    m  d  | reduced denominator bits | log10(abs(b*alpha-a))
    10 10 |                      138 | 34.88038
    17 17 |                      495 | 136.11522
    16 17 |                      469 | 129.03539
    18 17 |                      537 | 149.20531

Artifacts:

* /tmp/rising_parameter_pade.py
* /tmp/rising_parameter_pade.log
* /tmp/rising_parameter_pade.json (exact approximants and rational enclosures)

The computation is complete; no process is running. It supplies no family
of nonzero integer linear forms tending to zero, and proves no asymptotic
impossibility theorem. In particular, integrality of the formal expansion's
coefficients does not control the reduced boundary denominator after Padé
approximation and evaluation. The original conjecture remains unsettled.
