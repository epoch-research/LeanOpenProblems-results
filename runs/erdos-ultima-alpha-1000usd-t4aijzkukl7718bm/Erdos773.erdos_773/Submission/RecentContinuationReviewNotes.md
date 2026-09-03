# Recent continuation reviews: no settlement

The original Erdos 773 conjecture remains unresolved. No Lean source was
changed during these reviews, no new bound was proved, and no incomplete
proof was submitted. Spec.lean retains its sole admission for
0 < epsilon < 1/3. Its completed unconditional endpoint is eventual
M(N) >= N^(2/3).

## Sieve correlations

The established upper bound is

    M(N) <= 2 N exp(-log N / (512 log log N)).

Its exponent loss tends to zero. The already proved integer-cardinality
model satisfies all of the existing scalar modular inequalities
simultaneously at near-linear sizes. No stronger argument retaining joint
residue distributions was obtained. This does not rule out every stronger
sieve or correlation argument.

## Rational specialization

The existing rational-specialization obstructions already include positive
small absolute coefficients, small total coefficient sum, injective
individual evaluation, and arbitrarily large inert-prime denominators.
Individual evaluation injectivity is not injectivity of pairwise sums of
squares. Applying the coefficient-bound injectivity lemma directly to the
square-sum discrepancy requires a quadratic coefficient bound and does not
supply the needed near-linear construction. No additional restriction with
a successful cardinality and Sidonness proof was found.

## Joint root and square digit constraints

Constraining digits of both roots and their squares was considered. No
lemma was obtained forcing the carry discrepancy to vanish. In particular,
common low-order statistics do not by themselves justify replacing an
integer collision by a formal polynomial identity. The existing general
finite-color theorem applies to any statistics with sufficiently few
colors, but only guarantees a bad color class; it does not prove all
classes bad or preclude a specially selected large Sidon subclass.

## Partial residue fibers

The exact known compatibility criterion remains: with modular pair
matching, the union is Sidon precisely when each value fiber is Sidon and
the actual positive difference sets of distinct fibers are disjoint.

For aligned roots r+p*x, s+p*y, r+p*x', s+p*y', the collision equation is

    2*r*(x-x') + 2*s*(y-y')
      + p*(x^2+y^2-x'^2-y'^2) = 0.

Reducing modulo p discards the last term. Requiring separation of all
resulting linear congruences is a stronger condition, not a necessary one.
The full-fiber bounds cannot be applied to arbitrary sparse index sets.
No large partial-fiber family with suitably small actual overlap cost was
constructed in this review.

## Other checks

Finite checksum successes were not promoted to uniform constructions.
Bounded-capacity selections and fractional weights were not treated as
integral Sidon sets. No fixed-power upper bound for arbitrary square-Sidon
subsets was derived from full-interval counts.

External reference attempts failed both ordinary DNS access and direct-IP
HTTPS connections to GitHub raw content and a DNS-over-HTTPS endpoint.
No external mathematical result was retrieved.

## Submission state

Spec.lean SHA-256:

    257d2e55d464b8ea5a35ca7f1257dc2f59e682772c2f52fa771ee4bfdf9b8940

Original theorem: line 17276.
Sole admission: line 17287.
Sole import: import FormalConjecturesUtil.

These are records of unsuccessful research checks, not new Lean theorems,
not a disproof, and not a claim that all refinements of these approaches
are impossible.
