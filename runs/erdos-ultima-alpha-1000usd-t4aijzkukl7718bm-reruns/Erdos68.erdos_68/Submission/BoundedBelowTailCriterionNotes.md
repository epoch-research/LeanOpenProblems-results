# Fixed lower bounds suffice in the prime-unit tail criterion

`BoundedBelowTailCriterion.lean` is verified and has a built olean. Its
three principal axiom audits contain only propext, Classical.choice,
and Quot.sound. This is not a settlement of the conjecture.

## New verified criterion

For integer coefficients c(n), write

    T(n) = n! * (sum c(k)/k! - sum_{k<=n} c(k)/k!).

Suppose eventually

* (n-1) divides c(n)-1;
* c(p)=1 at primes;
* -B <= T(n) <= C*n*(floor(sqrt(n))+1),

where B and C are fixed natural constants. Then the sum is irrational.

Thus the earlier lower bound 0 can be replaced by any fixed negative
constant. Under rationality T(n) is eventually an integer. At a unit
coefficient index, T(n+1)=(n+1)T(n)-1; if n>B this and T(n+1)>=-B
force T(n)>=0. Also

    increment(n) = 1/n + T(n+1)/(n(n+1)) >= 0

for n>B. These are the sign facts needed for the integer increment-sum
contradiction. The close-prime-pair argument is reused from the earlier
verified criterion.

The file also proves the local version, with variable interval height H
and size condition a*L+(L+1)*H+1<a^2.

## Remaining application gap

No representation of the target is known here to satisfy all the
hypotheses. The Lambert coefficients retain the arithmetic properties
but have huge positive tails. Rowwise floors produce small positive
tails but lose the required congruences and prime coefficients.

This result does not conflict with SignedLinearTailComparison: that
rational comparison has tails unbounded below, not a fixed lower bound.

Spec.lean is unchanged and still contains its original sorry.
