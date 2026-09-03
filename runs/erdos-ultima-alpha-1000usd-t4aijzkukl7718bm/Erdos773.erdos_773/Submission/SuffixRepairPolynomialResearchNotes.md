# Suffix-repair counting polynomial: a verified numerical cost

The original Erdos 773 conjecture remains UNSETTLED. Spec.lean is unchanged,
with its sole admission at line 17287 for 0 < epsilon < 1/3. The proved
actual lower endpoint remains eventually M(N) >= N^(2/3).

## Motivation and limits of the review

Revisited an insertion process with ordered root slots. Erasing a suffix can
make deleted positions recoverable from the recovered root values, avoiding
one position-recording issue of arbitrary ordered deletions. Given two roots
of a square-sum relation, a divisor bound controls the remaining pair.

However, the suffix may have any length d through the current state size.
Recording its unaffected entries produces a length-dependent cost. The
following theorem checks one proposed UNIFORM numerical cost polynomial.
It does NOT formalize an entire insertion/decoding algorithm, prove that
these coefficients are exact or necessary record counts, or rule out more
selective records, nonuniform bounds, or other repair strategies.

## New clean module

Submission/SuffixRepairPolynomial.lean imports only FormalConjecturesUtil.
It builds without warnings or admissions and has an olean. Its four printed
main audits use only propext, Classical.choice, Quot.sound.
Log: /tmp/suffix-repair-polynomial.log.

For a finite set S of erasure lengths, define

    cost(S,K,D,z) = 1 + D * sum_{d in S} K^(d-2) z^d.

Here K>0, D>=0, z>=0, and every d in S is at least two.

length_cost proves

    cost(S,K,D,z) < K*z  ==>  D * sum_{d in S} d < K^2.

Put t=Kz. The strict hypothesis implies t>1. Multiplying by K^2 rewrites
the failure term as D*sum t^d. Bernoulli's inequality gives
sum t^d >= (t-1)*sum d. Cancellation of positive t-1 proves the result.

interval_length_sum proves, for m>=3,

    m^2 <= sum_{d=4}^{2m} d.

Thus choices_exceed_half_slots proves that, with D>=1, the displayed strict
criterion for all lengths 4,...,2m requires m<K.

slot_height_bound writes the resulting limitation at the declared height
N=(2m)K:

    (2m)^4 < 4*((2m)K)^2.

This only constrains the parameter range of THIS POLYNOMIAL CRITERION. It is
not an upper bound on actual Sidon sets or on every suffix-repair algorithm.
In particular, a better bound on actual records is not excluded.

## Other checks

The generic bounded-capacity counterexamples remain relevant: merely using
a small pair-recovery bound cannot silently yield near-linear extraction
for arbitrary carriers. They are not counterexamples among all squares.
Reviews of non-contiguous deletion, occupancy reconstruction, and polynomial-
height graph specialization did not provide a new square-specific exponent
or a valid near-linear construction.

No original-conjecture proof or disproof was obtained or submitted. The
main statement and import were not changed.
