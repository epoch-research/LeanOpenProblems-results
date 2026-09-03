# Prefix-balanced rounding with logarithmic representation upper bounds

## Status of the original task

Erdős 66 remains unresolved. `Submission/Spec.lean` is unchanged with its
original statement, import, and sorry. No proof/disproof was submitted.

## New unconditional infinite construction

`Erdos66PrefixBalancedUpperLimit.exists_harmonic_rounding_with_upper_bound`
constructs ONE set A satisfying

    |sum_{i<=n} (1_A(i)-profile(i))| <= 1       for every n,
    r_A(n) <= 6 log(n+2)                      eventually.

Here profile is the exact previously constructed decreasing fractional
profile with profile*profile(n)=H_(n+1). Thus this is an actual bounded-
discrepancy rounding with an O(log) pointwise upper bound, not an arbitrary
signed error sequence and not a conditional assumption on a rounding.

The existing general cumulative rounding theorem also applies to this A:

    |sum_{k<=n} (r_A(k)-H_(k+1))|
      <= 2 sqrt((2n+1) H_(2n+1)) + 1.

The main new theorem does NOT assert the pointwise limit or a pointwise
asymptotic lower bound.

## More general infinite theorem

`exists_balanced_upper` accepts any p:Nat->Real with 0<=p<=1 and
(p*p)(n)/log n -> c, c>=0. It constructs A with discrepancy at most one
from p on EVERY prefix, and eventually

    r_A(n) <= (2c+4) log(n+2).

The cutoff is chosen before the final finite length, so the compactness
step has the required quantifier order.

## Finite dependent rounding

Five new production files compile, with built oleans:

1. OrderedPipageGeometryExplore.lean
2. OrderedPipagePrefixExplore.lean
3. OrderedPositiveRoundingExplore.lean
4. PrefixBalancedUpperSelectionExplore.lean
5. PrefixBalancedUpperLimitExplore.lean

`two_coordinate_rounding` gives two box-constrained endpoints with fixed
coordinate sum, the correct convex-combination means, and nonincreasing
mean coordinate product. At least one of the two coordinates becomes
integral at each endpoint.

`exists_prefix_balanced_rounding` applies this to any multilinear polynomial
with nonnegative coefficients. It finds a Boolean vector whose polynomial
value does not exceed the fractional value and whose EVERY prefix lies
between the original prefix floor and ceiling. It rounds the first two
fractional coordinates. A prefix split by those coordinates contains just
one fractional entry, so its floor/ceiling bracket survives the step.
The number of fractional coordinates strictly decreases. A final lone
fractional coordinate is rounded down, using polynomial monotonicity.

For each fixed sum target, unordered pair-coordinate sets are disjoint.
Therefore its independent-Bernoulli exponential MGF expands into a
multilinear polynomial. For nonnegative tilt all expansion coefficients
are nonnegative. A finite nonnegative combination of upper exponential
potentials is thus covered by the rounding theorem.

`exists_prefix_balanced_upper_selection` returns a Boolean vector with all
prefix brackets and total upper-potential cost no greater than its original
independent-Bernoulli expectation. This does not claim that the resulting
Boolean coordinates are independent.

## Infinite upper envelope

At tilt 1/2, the existing Bernoulli MGF implies

    E exp(r(n)/2) <= exp(mu(n)).

Uniformly in finite cutoff, eventually mu(n)<=(c+1/2)log(n+2). Multiply by
exp(-(c+2)log(n+2)). The resulting expected cost is bounded by
(n+2)^(-3/2), whose tail is summable. Choose one tail with total cost <1.
Prefix-balanced finite selection makes each individual potential <1,
yielding r(n)<(2c+4)log(n+2). Compactness simultaneously preserves the
upper inequalities and every prefix discrepancy bound.

## Verification and exact remaining limitation

`PrefixBalancedUpperAxiomCheck.lean` audits the principal declarations.
They depend only on propext, Classical.choice, Quot.sound. None of the five
production files contains sorry or a new axiom.

The positive-coefficient argument does not apply to lower-tail exponentials:
negative tilts introduce negative polynomial coefficients. Nor does bounded
prefix discrepancy plus the O(log) envelope imply vanishing quadratic error.
The existing equivalence still leaves

    ((1_A-profile)*(1_A-profile))(n)/log n -> 0

unproved for the selected A. The upper coefficient 6 is not the desired 1.
No original-conjecture conclusion has been claimed.

## Possible next step, NOT proved here

For a fixed target n, a sum-preserving rounding of coordinates i,j with
i+j != n affects distinct pair factors. Their two linear coefficients have
the same sign even for negative tilt, giving concavity along the rounding
line. The exceptional case is i+j=n. Along ordered first-two-fractional
rounding, the pair sums strictly increase, suggesting that each target can
incur a bounded penalty only once. A compensated lower-tail potential
argument could potentially recover two-sided concentration while retaining
prefix balance. That compensated selection theorem and any resulting
infinite two-sided construction have NOT been formalized or used here.
Even standard two-sided logarithmic concentration would still not supply
the shrinking all-target error required by Erdős 66.
